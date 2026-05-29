local open MessagePackBinIO.Pack MessagePackBinIO.Unpack in

val smt_solvers = ["z3", "cvc4", "cvc5", "cvc5_proof", "verit",
                   "vampire_smt_dt", "vampire_smt_nodt"]

fun is_smt_oracle ((name, _), _ : term option) =
    member (op =) smt_solvers (Long_Name.base_name name)

fun get_oracles thy thms = Thm_Deps.all_oracles (map (Thm.transfer thy) thms)

fun get_local_facts thy =
  let
    val parent_facts = map Global_Theory.facts_of (Theory.parents_of thy)
    val thy_facts = Global_Theory.facts_of thy
  in Facts.dest_static false parent_facts thy_facts end

val pack_thm_entry =
  packPair (packString, packList RPC_Pretty.pack_raw_term)

val unpack_thm_entry =
  unpackPair (unpackString, unpackList RPC_Pretty.unpack_raw_term)

val pack_axiom_name = packString

val unpack_axiom_name = unpackString

fun snapshot thy =
  let
    val facts = get_local_facts thy
    val sorry_facts =
      facts |> map_filter (fn (name, thms) =>
        if Thm_Deps.has_skip_proof (map (Thm.transfer thy) thms)
        then SOME (name, map Thm.prop_of thms)
        else NONE)
    val axiom_names = map fst (Theory.all_axioms_of thy)
  in (sorry_facts, axiom_names) end

fun verify thy (baseline_props, baseline_axioms, extra_whitelist) =
  let
    val goal_results = baseline_props |> map (fn (name, expected_props) =>
      let val actual_thms =
            try (fn () => Global_Theory.get_thms thy name) ()
      in case actual_thms of
           NONE => (name, false)
         | SOME thms =>
             let val actual_props = map Thm.prop_of thms
             in if length actual_props = length expected_props
                   andalso ListPair.all Term.aconv (actual_props, expected_props)
                then (name, true)
                else (name, false)
             end
      end)
    val goal_preserved = forall snd goal_results

    val all_thms = baseline_props |> maps (fn (name, _) =>
      the_default [] (try (fn () => Global_Theory.get_thms thy name) ()))
    val bad_oracles = get_oracles thy all_thms |> map_filter (fn oracle =>
      if is_smt_oracle oracle then NONE
      else if member (op =) extra_whitelist (fst (fst oracle)) then NONE
      else SOME (fst (fst oracle)))
    val oracles_ok = null bad_oracles

    val current_axiom_names = map fst (Theory.all_axioms_of thy)
    val new_axioms = subtract (op =) baseline_axioms current_axiom_names
    val axioms_ok = null new_axioms
  in
    (goal_preserved, goal_results, bad_oracles, oracles_ok, new_axioms, axioms_ok)
  end

val _ = REPL_Server.register_app "verify_proof" (fn (cin, cout, state) =>
  let
    fun read unpacker =
      let val (ret, cin') = doUnpack unpacker (!cin)
      in cin := cin'; ret end

    fun run () =
      let
        val thy = Toplevel.end_theory Position.none state
        val mode = read unpackString
      in
        if mode = "snapshot" then
          let val (sorry_facts, axiom_names) = snapshot thy
          in REPL_Server.output cout
               (packPair (packList pack_thm_entry, packList pack_axiom_name))
               (sorry_facts, axiom_names);
             BinIO.StreamIO.flushOut cout
          end
        else if mode = "verify" then
          let
            val (baseline_props, baseline_axioms, extra_whitelist) =
              read (unpackTuple3 (unpackList unpack_thm_entry,
                                  unpackList unpack_axiom_name,
                                  unpackList unpackString))
            val result = verify thy (baseline_props, baseline_axioms, extra_whitelist)
          in REPL_Server.output cout
               (packTuple6 (packBool,
                            packList (packPair (packString, packBool)),
                            packList packString,
                            packBool,
                            packList packString,
                            packBool))
               result;
             BinIO.StreamIO.flushOut cout
          end
        else
          (REPL_Server.output_err cout ("Unknown mode: " ^ mode);
           BinIO.StreamIO.flushOut cout)
      end
  in
    \<^try>\<open>run ()
      catch exn => (REPL_Server.output_err cout (Runtime.exn_message exn);
                    BinIO.StreamIO.flushOut cout)\<close>;
    state
  end)

end
