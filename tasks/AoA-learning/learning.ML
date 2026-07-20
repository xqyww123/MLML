(* AoA-learning App.

   Replays a theory from source and, at each goal command, runs the AoA agent with
   a LearningTask: the agent is handed the goal together with its ORIGINAL Isar
   proof (as reference), reconstructs the proof with its own proof operations, and
   distils reusable experience into the shared experience-memory DB. After the AoA
   run (a pure side effect — its result is discarded) the REPL continues the
   theory's own original proof so the replay advances to the next goal.

   The replay-and-hook idea is borrowed from
   tasks/extraction/theorem-relevance/extraction.ML (NOT copied): a REPL.collector
   plugin fires after each command with the resulting state; at a goal command it
   invokes AoA, then returns (NONE, NONE) so the original proof runs unchanged.

   Client protocol (msgpack, this App is "Minilang.AoA_Learning"):
     header  (client -> ML):  (driver:string, log_dir:string, path:string)
     ML -> client per goal:   (0, pos)            goal opened at `pos` ("file:line")
                              client replies bool  (run AoA on this goal? — skip for
                                                    resume via control.db)
                              (1, pos, outcome, iid)
                                                  the AoA run concluded; `outcome` is:
                                                    "finished"  agent ran to completion
                                                    "timeout"   hard backstop fired (the
                                                                agent was wedged)
                                                    "infra"     RPC host unreachable — the
                                                                agent never ran, so this is
                                                                NOT evidence the goal is
                                                                unlearnable; the client
                                                                retries it rather than
                                                                counting it toward give-up
                                                    "error"     other exception
                                                    "extraction_skipped"
                                                                the original proof has no
                                                                recognised terminal
                                                                (sorry/oops); nothing to
                                                                learn, no agent runs, iid=""
                                                  `iid` = the goal's AoA log directory
                                                  <log_dir>/<iid>/ (empty when no run)
                              (2, errs)           error detail(s) (list of strings), sent
                                                  alongside every non-"finished" outcome
     ML -> client at end:     5                    theory replay done
*)

structure AoA_Learning = struct

open MessagePackBinIO.Pack MessagePackBinIO.Unpack MiniLang_Agent_AoA

fun is_goal_command (Command_Span.Command_Span (name, _)) =
      member (op =) ["lemma", "theorem", "schematic_goal", "proposition", "corollary"] name
  | is_goal_command _ = false
fun is_goal_command' (Command_Span.Span (k, _)) = is_goal_command k

(* Reconstruct the source text of command spans (the "original Isar proof" the
   LearningTask shows the agent for reference). Markup-free token unparse. *)
fun span_src sp =
  Command_Span.content sp
  |> filter Token.is_proper
  |> map Token.unparse
  |> space_implode " "
fun isar_of_spans spans = spans |> map (span_src o snd) |> cat_lines

(* Extract exactly the proof of the goal just opened: the prefix of the remaining
   commands up to (and including) the command that closes it. Bracket-matching over
   the Isar proof structure (idea borrowed from extraction.ML): a BWD frame is a
   goal awaiting a terminal (`by`/`done`/`.`/`..`); a FWD frame is a `proof` block
   awaiting `qed`; `have`/`show`/... open a nested BWD goal. Start with one BWD
   frame (the current goal) and stop when the stack empties. *)
fun extract_proof remaining =
  let datatype frame = FWD | BWD
      fun pop _ [] = error "extract_proof: malformed proof"
        | pop k (k' :: rest) = if k = k' then rest else error "extract_proof: malformed proof"
      (* Faithful to extraction.ML's `extract_proof` (theorem-relevance, which has
         run over the whole AFP): the final `| go _ _ = error ...` catch-all is
         ESSENTIAL. When the bracket stack cannot close before `remaining` is
         exhausted — e.g. the original proof is `sorry`/`oops` (not a recognised
         terminal), or any structure outside the recognised command set — it raises
         a *catchable* Isabelle ERROR instead of an SML `Match` that would crash the
         whole replay. The caller wraps the call in `\<^try>` (mirroring
         extraction.ML's call site) so that one goal is skipped and the replay
         continues. Do NOT special-case `sorry`: the catch-all handles it uniformly
         with every other unclosable form. *)
      fun go [] _ = []
        | go stack ((tr, sp as Command_Span.Span (Command_Span.Command_Span (name, _), _)) :: L)
            = (case name
                 of "proof"     => (tr, sp) :: go (FWD :: stack) L
                  | "qed"       => (tr, sp) :: go (stack |> pop FWD |> pop BWD) L
                  | "have"      => (tr, sp) :: go (BWD :: stack) L
                  | "show"      => (tr, sp) :: go (BWD :: stack) L
                  | "hence"     => (tr, sp) :: go (BWD :: stack) L
                  | "thus"      => (tr, sp) :: go (BWD :: stack) L
                  | "consider"  => (tr, sp) :: go (BWD :: stack) L
                  | "obtain"    => (tr, sp) :: go (BWD :: stack) L
                  | "interpret" => (tr, sp) :: go (BWD :: stack) L
                  | "subgoal"   => (tr, sp) :: go (BWD :: stack) L
                  | "by"        => (tr, sp) :: go (pop BWD stack) L
                  | "done"      => (tr, sp) :: go (pop BWD stack) L
                  | "apply_end" => (tr, sp) :: go (pop BWD stack) L
                  | "."         => (tr, sp) :: go (pop BWD stack) L
                  | ".."        => (tr, sp) :: go (pop BWD stack) L
                  | _           => (tr, sp) :: go stack L)
        | go _ _ = error "extract_proof: malformed proof"
   in go [BWD] remaining
  end

fun pos_str pos =
  let val file = the_default "" (Position.file_of pos)
      val line = the_default 0 (Position.line_of pos)
   in file ^ ":" ^ string_of_int line end

(* `send f` writes to the client via `f cout`; `recv u` reads one value. Both close
   over the App's (cin, cout). *)
fun learning_plugin (driver, log_dir, budget : MiniLang_Agent.budget, send, recv) : REPL.collector =
  fn _ => fn {current_command, state, remaining} =>
    let val pos = case current_command
                    of Command_Span.Span (Command_Span.Command_Span (_, p), _) => p
                     | _ => Position.none
     in if is_goal_command' current_command
           andalso Toplevel.is_proof state
           (* Skip goals in an infrastructure session (e.g. HOL-Decision_Procs):
              these are excluded from semantic collection/retrieval by design
              (Infra_Filter), so learning from them yields no useful, retrievable
              experience — keep them out of the learning scope. *)
           andalso not (Infra_Filter.is_infra_theory
                          (Proof_Context.theory_of (Toplevel.context_of state)))
           andalso (let val st = #goal (Proof.raw_goal (Toplevel.proof_of state))
                     in not (Thm.is_dummy st) andalso not (Thm.no_prems st) end)
        then let
            val _ = send (fn cout => doPack (packPair (packInt, packString)) (0, pos_str pos) cout)
            val run = recv unpackBool
          in if not run then (NONE, NONE)
             (* extract_proof raises a catchable ERROR when the original proof has no
                recognised terminal (e.g. `sorry`/`oops`). Mirror extraction.ML's call
                site: run it under `\<^try>`, and on failure report the goal and skip it
                so the replay continues — never let it escape as an uncaught exception. *)
             else (case Exn.capture (fn () => isar_of_spans (extract_proof remaining)) ()
                     of Exn.Exn e =>
                          (send (fn cout => doPack (packPair (packInt, packList packString))
                                   (2, [pos_str pos ^ " : proof extraction skipped: "
                                        ^ (Runtime.exn_message e |> REPL.trim_makrup)]) cout);
                           (* Terminal, like a finished goal: the original proof has no
                              recognised terminal (sorry/oops), so there is nothing to
                              learn and re-running cannot change that. Emit a completion
                              so the client marks the goal resolved instead of retrying
                              it forever. No agent ran, so there is no log dir (iid=""). *)
                           send (fn cout => doPack (packTuple4 (packInt, packString, packString, packString))
                                   (1, pos_str pos, "extraction_skipped", "") cout);
                           (NONE, NONE))
                      | Exn.Res isar => let
               (* Cache is bypassed for BOTH read and write on the learning path
                  (C8): a cache hit would replace the proof before the agent ever
                  runs (zero learning), and a store would pollute the shared
                  production cache. *)
               val ctxt = Toplevel.context_of state
                     |> Config.put AoA_use_proof_cache false
                     |> Config.put AoA_store_proof_cache false
                     |> Config.put AoA_log_dir log_dir
               val sequent = #goal (Proof.raw_goal (Toplevel.proof_of state))
               val iid = "learn_" ^ string_of_int (serial ())
               (* Disable on-demand deformalization during retrieval/embedding
                  (auto_interpret_for_embedding = SOME false) — same as the agent
                  evaluators (evaluator.py MinilangAgent_Base default False).
                  Otherwise a single `query` can spawn a Claude interpretation storm
                  over hundreds of auto-generated junk lemmas (e.g. floatarith
                  constructor distinct/case facts) and burn the whole per-goal
                  budget. Budget comes from the client. *)
               val cfg = { auto_interpret_for_embedding = SOME false } : MiniLang_Agent.cfg
               (* Hard backstop over AoA's own cooperative budget: kill a wedged
                  goal 300s past its budget so it cannot wedge the whole replay. *)
               val hard = Time.fromSeconds (#timeout_seconds budget + 300)
               val task = ("learning", packString isar)
               (* `outcome` classifies why the AoA run ended so the client can decide
                  resume policy per goal (see the protocol doc at the top). A plain
                  return means the agent ran to completion ("finished"); the two catch
                  clauses split the failures the client treats differently — a timeout
                  (agent wedged; counts toward give-up) vs. an RPC-host outage ("infra";
                  the agent never ran, so retry rather than give up). The RPC layer
                  raises a plain ERROR (no dedicated exception), so infra is matched on
                  its message text. *)
               val outcome = \<^try>\<open>
                     Timeout.apply hard (fn () =>
                        (AoA_RPC (driver, (cfg, budget), iid) task (ctxt, sequent); "finished")) ()
                   catch Timeout.TIMEOUT _ =>
                           (send (fn cout => doPack (packPair (packInt, packList packString))
                                    (2, [pos_str pos ^ " : AoA timed out (hard backstop)"]) cout);
                            "timeout")
                       | e =>
                           let val msg = Runtime.exn_message e |> REPL.trim_makrup
                            in send (fn cout => doPack (packPair (packInt, packList packString))
                                       (2, [pos_str pos ^ " : " ^ msg]) cout);
                               if String.isSubstring "RPC host" msg
                                  orelse String.isSubstring "RPC Host" msg
                                  orelse String.isSubstring "Cannot connect" msg
                               then "infra" else "error"
                           end\<close>
               (* `iid` names the AoA log directory <log_dir>/<iid>/ for THIS goal.
                  The client needs it to attribute experience-memory writes and
                  token cost to the goal: with a fleet of workers writing into one
                  shared log_dir concurrently, timestamps cannot identify which
                  directory belongs to which goal. *)
               val _ = send (fn cout => doPack (packTuple4 (packInt, packString, packString, packString))
                                (1, pos_str pos, outcome, iid) cout)
             in (NONE, NONE)   (* let the theory's original proof run *)
             end)
          end
        else (NONE, NONE)
    end

fun REPL_App (cin, cout, toplevel) =
  let fun read packer = let val (r, cin') = doUnpack packer (!cin) in cin := cin'; r end
      fun send f = (f cout; BinIO.StreamIO.flushOut cout)
      val (driver, log_dir, path, (ts, mtc, mr)) =
            read (unpackTuple4 (unpackString, unpackString, unpackString,
                                unpackTuple3 (unpackInt, unpackInt, unpackInt)))
      val budget = { timeout_seconds = ts, max_tool_calls = mtc, max_retries = mr }
                 : MiniLang_Agent.budget
      val path' = Path.explode path
      val src = File.read path'
      val thy_qualifier = the_default "HOL" (REPL_Aux.parse_session_name path')
      val _ = REPL.init_repler NONE
      val _ = REPL.set_register_thy false
      val _ = REPL.register_plugin ("AoA_Learning", learning_plugin (driver, log_dir, budget, send, read))
      (* Q3: cap a single ORIGINAL Isar command (elaboration / `by` step) at 600s so
         a wedged single command cannot stall the replay before AoA is even reached;
         does NOT bound total replay time (thousands of slow proofs are fine). *)
      val cfg = { thy_qualifier = thy_qualifier,
                  file = SOME path,
                  position_label = NONE,
                  (* Inject Minilang_AoA as a base ancestor of every replayed
                     target theory (PREPENDed — see REPL.ML init_thy): the AoA agent
                     lives in theory Minilang, so a target that does NOT import it
                     (e.g. any AFP theory) would otherwise fail every goal with
                     "Cannot join unrelated theory certificates Minilang:_ and
                     <target>:_" when the agent applies a Minilang-certified tactic.
                     Making Minilang_AoA an ancestor gives the goal's theory a
                     common lineage with Minilang so the certificate join succeeds. *)
                  additional_libs = ["Minilang_Agent_Injector.Minilang_Agent_Injector"],
                  configs = [],
                  import_dir = NONE,
                  single_cmd_timeout = SOME (Time.fromSeconds 600),
                  attributes = [],
                  base_dir = Path.dir path',
                  write_thy = false }
      val errs = REPL.collect_erros (REPL.RE cfg src)
      val _ = if null errs then ()
              else send (fn cout => doPack (packPair (packInt, packList packString)) (2, errs) cout)
   in send (fn cout => doPack packInt 5 cout)
    ; toplevel
  end

val _ = REPL_Server.register_app "Minilang.AoA_Learning" REPL_App

end
