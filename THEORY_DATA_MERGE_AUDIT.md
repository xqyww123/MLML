# Audit: does our code assume `Theory_Data` merge always runs?

Read-only audit, 2026-08-13. Nothing was changed in response to it.

## Why

Isabelle's `Theory_Data` merge function is **not** always called.
`Context.merge_data` (`contrib/Isabelle2025-2/src/Pure/context.ML:447-456`):

```sml
fun merge_data [] = Datatab.empty
  | merge_data [thy] = data_of thy                    (* ONE parent: the whole Datatab is taken
                                                         verbatim; NO kind's merge runs *)
  | merge_data thys =
      let fun merge (k, kind) data =
        (case map_filter (fn thy => lookup_data k thy |> Option.map (pair thy)) thys of
          [] => data
        | [(_, x)] => Datatab.default (k, x) data      (* >=2 parents but only ONE carries this
                                                          kind: inherited, merge NOT run *)
        | args => Datatab.update (k, invoke_merge kind args) data);
      in Datatab.fold merge (Synchronized.value kinds) (data_of (hd thys)) end;
```

There is no flag on `declare_data` to force invocation, and for a single-parent theory the
kind table is never even consulted. This is a **sound optimisation** for the intended use — a
value describing the theory's own accumulated content, where `merge [x] = x`. It is wrong only
for a value that describes something else: a set of theories, an identity, or a mutable cell.

The audit was prompted by `Universal_Key.Cache_Scope`
(`contrib/Isabelle_RPC/Tools/Universal_Key.ML`), which made exactly that mistake — its data
named a *population* of theories, so inheriting one parent's value silently enlarged the
population. Diagnosed and fixed by moving the reconciliation into `Theory.at_begin`, the only
place with both the beginning theory and all its parents in hand
(`BUG_UNIVERSAL_KEY_SHORT_NAME_FIX_PLAN.md` §A.6). The question here is whether the same
mistake is anywhere else.

## What was looked for

Six symptoms, not "looks risky":

- **S1** a mutable cell inside `T` (`Unsynchronized.ref`, `Synchronized.var`, an array, a
  mutable hash table) — verbatim inheritance shares it **by reference** with every descendant,
  and through a common ancestor with siblings in unrelated cones;
- **S2** `merge` with an observable side effect (`serial ()`, allocation, writing a global
  table, logging) — silently skipped on the single-parent path;
- **S3** `merge` that resets, filters, deduplicates or re-validates, where correctness depends
  on that happening;
- **S4** `merge` that raises on conflict as a soundness check — dead whenever merge is bypassed;
- **S5** a comment or surrounding logic asserting that merge runs at every theory begin;
- **S6** a value describing a set of theories, an identity or a population.

Plus the mirror-image error in `Theory.at_begin` / `at_end` wrappers: assuming the wrapper runs
for every theory in a cone (it only runs for descendants of the theory that registered it), or
returning `SOME` unconditionally (which makes `Theory.apply_wrappers`' fixpoint loop diverge).

The intended monotone-accumulator use — `Symtab.merge`, `union`, `@`, `Library.merge`, no side
effects, no mutable cells — was **not** reported. Inheriting one parent's value is correct there.

## Verdict

**122 live functor applications** across the two parts: 91 in `phi-system`, 31 elsewhere.
**Sixteen are suspect. Exactly one is a live defect, and it is not a merge error:**

- `phi-system/Phi_Logic_Programming_Reasoner/library/tools/statistics.ML:335` writes
  `val _ = Theory.at_begin (…)`, discarding the `theory -> theory` that `Theory.at_begin`
  returns. **The wrapper is never installed**, so the per-theory reset of the rule-utilization
  counter never happens and `utilization` reports stale data. The correct idiom is two files
  away (`thy_hacks.ML:22`). See Part I, F1.

The one genuine instance of the hunted misconception is **latent**, in a dormant file:

- `Semantic_Embedding/Tools/Sledgehammer/sledgehammer_embedding.ML:209` — `Thm_Vector`'s `T` is
  a `Synchronized.var option` and its `merge` **allocates** cells (S1+S2+S3+S5). A theory
  importing two theories that both import `Sledgehammer_Embedding` gets a *fresh* cell holding
  a snapshot, so its cone forks the embedding cache and re-pays for RPC embeddings already
  computed. Cost, not correctness. Nothing imports that theory today and the ROOT does not
  build it. See Part II, F1.

The next thing to break, if its writer ever gets a second call site:

- `phi-system/…/opr_stack.ML:339` — `Meta_Opr.merge = Symtab.merge (K false)` raises
  `Symtab.DUP` for **any** key two parents share, including one both inherited unchanged from a
  common ancestor. Unreachable only because `set_meta_opr` has zero call sites. See Part I, F2.

Everything else is latent or cosmetic, and is listed in full below with the reason.

Two findings worth keeping even though they are not defects, because they are easy to
reintroduce: `Table.join` short-circuits on `pointer_eq` and on an empty first table
(`table.ML:539-548`), so a strict merge equality only bites when two parents hold *distinct*
tables sharing a key; and `Net.merge` / `iNet.merge` use `insert_safe`, so **no net-based merge
in this codebase can raise** — all twenty-odd are the intended monotone use.

`contrib/AutoCorrode/` is **third-party** (`origin https://github.com/awslabs/AutoCorrode`; all
13 hits attributed to upstream AWS authors). Its instances were checked and none is a finding.

The two parts below keep their own `F`-numbering; cite them as "Part I F2", "Part II F1".

---

# Part I — `contrib/phi-system/`

Scope: `contrib/phi-system/` only. All paths below are relative to
`/home/qiyuan/Current/MLML/contrib/phi-system/` unless they start with `contrib/`.

## 1. Verdict

I enumerated every functor application in scope by grepping for `structure|functor … = Theory_Data'? |
Generic_Data | Proof_Data` over `*.ML` and `*.thy` (105 matching source lines). Of those, **91 are live
functor applications** — 13 `Theory_Data`, 48 `Generic_Data`, 30 `Proof_Data` — plus 7 that sit inside
`(* … *)` comments and 2 in `Phi_Semantics_Framework/Statespace/state_space.bak.ML`, a file no `.thy`
ever loads (only `state_space.ML` is loaded, from
`Phi_Semantics_Framework/Statespace/StateSpaceLocale.thy:11`). There is **no** use of the primed
`Theory_Data'` anywhere in scope, so no instance inspects its parent list.

**Ten instances are suspect.** Exactly **one is a real, present-tense defect**, and it is the
mirror-image `Theory.at_begin` error rather than a merge error:
`Phi_Logic_Programming_Reasoner/library/tools/statistics.ML:335` writes
`val _ = Theory.at_begin (…)`, discarding the `theory -> theory` that `Theory.at_begin` returns, so
the wrapper is **never installed** and per-theory reset of the rule-utilization statistics never
happens. Everything else is a latent hazard: one merge (`Meta_Opr`) will abort a theory with an
uncaught `Symtab.DUP` the day its currently-unused writer gets a second call site; two mutable-cell
`Proof_Data` wrappers share an `Unsynchronized.ref` across context branches by design but with no
guard; and several merges are non-identity-on-one-argument in ways that are today masked by the data
being written from a single place.

I found **no** `Theory_Data` or `Generic_Data` in scope whose `empty` value contains a mutable cell.
Every `Unsynchronized.ref` / `Synchronized.var` that lives inside a data value lives inside a
`Proof_Data`, where `init : theory -> T` is re-run per `Proof_Context.init_global`
(`contrib/Isabelle2025-2/src/Pure/context.ML:585-586, 612-614`), so the "one shared `empty` for the
whole process" failure mode does not arise here. I also verified that the discrimination net used
pervasively by phi-system, `iNet`, is a purely functional datatype
(`contrib/Performant_Isabelle_ML/library/improved_net.ML:203-205`), so the many `iNet.net`-typed data
values carry no hidden mutable state.

Two background facts I re-derived because several judgements below turn on them:

- `Table.join` (and hence `Symtab.merge`, `Symreltab.merge`, `PriorityTab.merge`) short-circuits on
  `pointer_eq (tab1, tab2)` and on `is_empty tab1`
  (`contrib/Isabelle2025-2/src/Pure/General/table.ML:539-548`). So a strict merge equality only bites
  when the two parents' tables are *distinct values that share a key*.
- `Net.merge` and `iNet.merge` are `fold (insert_safe eq) (dest net2) net1`
  (`contrib/Isabelle2025-2/src/Pure/net.ML:252-253`,
  `contrib/Performant_Isabelle_ML/library/improved_net.ML:466-467`). `insert_safe` swallows `INSERT`,
  so **no net-based merge in this codebase can ever raise**. All 20-odd `Net.merge` / `iNet.merge`
  instances are monotone union-with-dedup and are the intended use.

---

## 2. Findings, most severe first

### F1 — `Theory.at_begin` registration is discarded; the wrapper never runs

`Phi_Logic_Programming_Reasoner/library/tools/statistics.ML:335`

```sml
val _ = Theory.at_begin (fn thy => (reset_utilization_statistics thy; NONE))
```

Symptoms: the `at_begin` mirror-image check.

`Theory.at_begin f = map_wrappers (apfst (cons (f, stamp ())))`
(`contrib/Isabelle2025-2/src/Pure/theory.ML:186`), i.e. its type is
`(theory -> theory option) -> theory -> theory`. The line above therefore builds a
`theory -> theory` function and binds it to `_`. It is never applied to a theory, so the wrapper is
never stored in any theory's `wrappers` field and `Theory.begin_theory`'s
`apply_wrappers (begin_wrappers thy)` (`theory.ML:196-205`) never sees it. Contrast the *correct*
idiom two files away: `Phi_BI/library/tools/thy_hacks.ML:22` writes
`val _ = Theory.setup (Theory.at_begin (…))`.

Concrete consequence. `reset_utilization_statistics thy`
(`statistics.ML:74-75`) is what installs a fresh, empty per-theory bucket in the process-global
counter `rule_usage` (`statistics.ML:71-72`), a
`… Synchronized.var Symtab.table Synchronized.var` keyed by `Context.theory_long_name thy`. Because
the wrapper never fires, no bucket is ever created at theory-begin. `utilization thy group`
(`statistics.ML:80-83`) then returns `Net.empty` for any theory whose bucket has not been created by
the lazy path at `statistics.ML:135`, and `utilization_of_group`
(`statistics2.ML:43-46`) reports zero utilization for every collected rule. Observably: turn on
`collect_reasoner_statistics` for a group, build, and ask for the utilization — the counts are those
accumulated since whenever the lazy path last created the bucket, never reset at theory boundaries,
which is precisely what this line was written to prevent.

Severity: **real** (dead code with a silently wrong observable result). It is not a soundness bug —
it only corrupts a profiling report.

Smallest fix: wrap it, `val _ = Theory.setup (Theory.at_begin (fn thy => (reset_utilization_statistics thy; NONE)))`.

Two caveats the author should know before doing that, because they are the same class of mistake:
(a) an `at_begin` wrapper registered by `Theory.setup` in theory *T* applies only to *descendants* of
*T*, never to *T* itself and never to any theory that came out of a pre-built heap image, so the
reset will silently not happen for the heap-resident part of the session; (b) the wrapper has a real
side effect on a process-global `Synchronized.var` and `Theory.apply_wrappers` re-runs the whole
wrapper list until every wrapper returns `NONE` (`theory.ML:83`) — this one returns `NONE`
unconditionally, so it terminates, but it will be re-executed once per outer loop iteration if any
*other* wrapper in the list returns `SOME`. With `Phi_Hacks`' wrapper (F3) in the same list, that is
exactly what happens: `Thy_At_Begin_Version` returns `SOME` on the first pass, so the loop runs a
second pass and the reset would fire twice. Harmless for a reset, but it is a side effect in a
function the framework assumes is re-runnable.

---

### F2 — `Meta_Opr.merge = Symtab.merge (K false)`: any key shared by two parents aborts the theory

`Phi_System/library/system/opr_stack.ML:339-343`

```sml
structure Meta_Opr = Theory_Data (
  type T = meta_opr Symtab.table
  val empty = Symtab.empty
  val merge = Symtab.merge (K false)
)
```

Symptoms: **S4** (merge raises on conflict), and the conflict it "guards" is not a real conflict.

`Symtab.merge eq = join (fn key => fn xy => if eq xy then raise SAME else raise DUP key)`
(`table.ML:548`). With `eq = K false`, *every* key that exists in both argument tables raises
`Symtab.DUP key` — even when the two entries are literally the same ML value inherited unchanged from
a common ancestor. The `pointer_eq` short-circuit in `join` (`table.ML:539-547`) only rescues the
case where neither parent modified the table at all.

Concrete scenario I can construct from the source (it is not currently reachable — see severity):
theory `A` calls `set_meta_opr ("foo", op_foo)` (`opr_stack.ML:346`, which is
`Meta_Opr.map o Symtab.update`). Theory `B imports A` calls `set_meta_opr ("bar", …)`; theory
`C imports A` calls `set_meta_opr ("baz", …)`. Now `theory D imports B C`. `Context.begin_thy` calls
`merge_data [B, C]` (`context.ML:548`); both carry the kind, so `invoke_merge` runs
(`context.ML:452-455`); `Symtab.merge (K false)` folds `C`'s entries into `B`'s table, reaches key
`"foo"` — present in both, inherited identically from `A` — and raises `Symtab.DUP "foo"`. `D` fails
to begin with an uncaught exception, not an `error` with a legible message.

Note the bypass direction here is the *opposite* of the usual worry: the check is *too* eager, and
the single-parent shortcut is the only reason it has never fired.

Severity: **latent**. I grepped the whole repository (excluding the Isabelle distribution and AFP):
`set_meta_opr` has **zero call sites** — only its signature declaration at `opr_stack.ML:80` and its
definition at `opr_stack.ML:346`. So `Meta_Opr` is always `Symtab.empty`, both parents hold the same
`empty` value, `pointer_eq` fires, and merge never raises. The first user to call `set_meta_opr` in
two theories that meet at a diamond will hit it.

Smallest fix: `val merge = Symtab.merge (K true)` if last-writer-wins is acceptable, or
`Symtab.join (fn k => fn _ => error ("Duplicate meta operator " ^ quote k))` if a genuine clash
really must be rejected — but note even that still cannot distinguish "both inherited from a common
ancestor" from "genuinely declared twice", because merge does not see the ancestor.

---

### F3 — `Thy_At_Begin_Version`: `merge = K ""`, and the value is a theory identity

`Phi_BI/library/tools/thy_hacks.ML:16-27`

```sml
structure Thy_At_Begin_Version = Theory_Data (
  type T = string
  val empty = ""
  val merge = K ""
)

val _ = Theory.setup (Theory.at_begin (fn thy =>
  if Thy_At_Begin_Version.get thy = Context.theory_long_name thy
     orelse Thy_At_Begin.is_empty (Context.Theory thy)
  then NONE
  else SOME (thy |> Thy_At_Begin_Version.put (Context.theory_long_name thy)
                 |> Thy_At_Begin.invoke (Context.Theory thy) () )))
```

Symptoms: **S3** (merge resets rather than being identity on one argument) and **S6** (the value is a
theory identity, not the theory's own accumulated content).

The design is a once-per-theory latch: the datum records the long name of the theory in which the
`Thy_At_Begin` hooks last ran, so that when `apply_wrappers` re-runs the wrapper list
(`theory.ML:83`) the second pass sees `get thy = theory_long_name thy` and returns `NONE`,
terminating the loop.

`merge = K ""` is written on the assumption that merge runs at every begin and clears the latch. It
does not run for a single parent. **In this particular case the code survives anyway**, and I want to
be explicit that I could *not* construct a failure:

- one parent → the latch is inherited verbatim as the *parent's* long name, which differs from the
  child's long name, so the guard is false and the hooks fire;
- ≥2 parents, only one carrying the kind → `Datatab.default` installs that parent's long name
  (`context.ML:452`, `table.ML:419`), again ≠ the child's long name, hooks fire;
- ≥2 parents both carrying the kind → `merge = K ""` yields `""` ≠ the child's long name, hooks fire.

So all three paths reach the intended behaviour, because no *inherited* value can ever equal the
child's own long name (long names are unique per theory in a process). `merge = K ""` is therefore
redundant rather than wrong.

Severity: **cosmetic**, but it is a genuine misconception written into the source and it is one
refactor away from mattering — e.g. if the latch were ever changed to a boolean or to a session-local
short name, the single-parent path would stop clearing it and the hooks would silently never run in
any child theory.

Smallest fix: delete the custom merge and use the identity that the shortcut already implements,
`val merge = fst` (or `K ""` documented as "the value is meaningless after merge; only equality with
the current theory's own long name matters"). A comment stating why single-parent inheritance is
already correct is worth more than the code change.

Also worth recording against this instance: the `Theory.at_begin` wrapper registered here applies
only to descendants of the theory that loads `thy_hacks.ML` (Phi_BI's preliminary theory), and never
re-runs for theories already baked into a heap image. Any code that assumes `Thy_At_Begin` hooks have
fired for *every* theory in the session — including Pure, HOL, AFP imports, and phi-system's own
ancestors — is wrong. I did not find such an assumption in the sources I read, but `Thy_At_Begin` is
a public hook (`Phi_Hacks.Thy_At_Begin`) so callers outside this scope may hold it.

---

### F4 — `Single_Thread_Proof_Data` / `Single_Thread_Proof_Data_Opt`: `Unsynchronized.ref` inside `Proof_Data`

`Phi_BI/library/tools/Phi_Help.ML:206-219` and `:235-258`

```sml
functor Single_Thread_Proof_Data(Arg: PROOF_DATA_ARGS): PROOF_DATA = struct
structure Data = Proof_Data (
  type T = Arg.T Unsynchronized.ref
  val init = Unsynchronized.ref o Arg.init
)
val get = Unsynchronized.! o Data.get
fun put x ctxt = (Data.get ctxt := x; ctxt)
fun map f ctxt = let val r = Data.get ctxt in r := f (!r); ctxt end
```

and the `_Opt` variant with `type T = Arg.T Unsynchronized.ref option`, `val init = K NONE`,
allocating the ref lazily on first write (`Phi_Help.ML:239-256`).

Symptoms: **S1** (mutable cell inside `T`).

What the cell holds: whatever the client wants to thread through a proof context without the
functional-update discipline. The one instantiation in scope is
`Phi_System/library/system/generic_element_access.ML:56`,
`structure Unprc_EleIdx = Single_Thread_Proof_Data_Opt (type T = prohibit_remainig_eleidx * (cterm * cterm) option)`,
which records the not-yet-consumed element index of a generic element access, mutated at
`generic_element_access.ML:64` (`Unprc_EleIdx.put (false, SOME (ctm,hook)) ctxt`) and read at `:33-36`.

Who shares the cell. `Proof_Data`'s `init` is run per `Proof_Context.init_global`
(`context.ML:585-586, 612-614`), so a *fresh* context gets a fresh ref — this is not the
"one `empty` for the whole process" hazard. The sharing is along a different axis: `Proof_Data.put`
builds a new `Prf` record that reuses every unchanged `Datatab` entry (`context.ML:632-637`), so the
ref is shared by the original context and *every* context functionally derived from it, and
`raw_transfer`'s `init_new_data` preserves existing entries across theory transfer
(`context.ML:600-607`). Writing through `put` is therefore visible to the ancestor context and to
sibling contexts on other backtracking branches. Since `Unsynchronized.ref` is used (not
`Synchronized.var`), concurrent writes from two Isabelle proof futures are also unsynchronised.

Concrete scenario: `Phi_Reasoner` explores alternatives via `Seq`; branch 1 derives `ctxt1` from
`ctxt0` and calls `Unprc_EleIdx.put`, then fails and is discarded; branch 2 derives `ctxt2` from the
same `ctxt0` and calls `Unprc_EleIdx.get` — it sees branch 1's write, because both `ctxt1` and
`ctxt2` hold the same ref that `ctxt0` created. The functional-context abstraction that makes
backtracking sound does not protect this value.

Severity: **latent, and evidently deliberate** — the functor is named `Single_Thread_…`, so the
author knows the cell escapes the functional discipline. I am flagging it because the name documents
the thread-safety caveat but not the *branch*-safety caveat, and the branch one is the one that bites
inside a backtracking reasoner.

Smallest fix: none, if the escape is intended. If it is not, drop the ref and use plain `Proof_Data`
with `put`/`map` returning the new context (the call sites at `generic_element_access.ML:58-64`
already thread a context through, so they would need no restructuring). At minimum, extend the
comment at `Phi_Help.ML:206` to say that writes are visible to sibling `Seq` branches.

---

### F5 — `Phi_Error.D`: merge composes handlers, and the source says so

`Phi_BI/library/tools/error.ML:22-29`

```sml
(*THIS MERGE IS WRONG! ! ! !*)
fun merge (f,g) = (fn c => fn e => f (g c) e)

structure D = Theory_Data(struct
  type T = (exn -> unit) -> exn -> unit
  val empty = I
  val merge = merge
end)
```

Symptoms: **S3** (merge is not identity on one argument: `merge (f,f) = fn c => fn e => f (f c) e`,
not `f`) and **S5** (a comment explicitly asserts the merge is wrong).

Concrete scenario: theory `A` calls `register_handler h` (`error.ML:35`, which is
`D.map (fn g => merge (f,g))`) — this happens once already, in `A = Phi_BI`'s
`Theory.setup` at `error.ML:37-42`. Descendants `B` and `C` each register their own handler, giving
`h_B ∘ h_A` and `h_C ∘ h_A`. `theory D imports B C` merges them into
`h_B ∘ h_A ∘ h_C ∘ h_A` — `A`'s handler is wired into the chain twice. Since the handlers are
continuation-style `(exn -> unit) -> exn -> unit` and `h_A` (`error.ML:38-41`) re-raises a `THM`
exception for `CastFail` and otherwise delegates, duplication would show up as a doubled
transformation of any exception `h_C` passes through.

Severity: **latent** and currently unreachable. `handle_errors_toplevel` (`error.ML:31-33`) is the
only consumer of `D.get`, and I found **zero** call sites for it anywhere in the repository; the file
header calls the mechanism "unfinished". The only two producers of `Phi_Error.CastFail`
(`Phi_System/library/system/Phi_Working_Mode.ML:130, 136`) raise it into ordinary Isabelle exception
handling, never through `D`.

Smallest fix: if the mechanism is revived, store `((exn -> unit) -> exn -> unit) list` with
`val merge = Library.merge (op =)` or a serial-keyed table, so that merge is idempotent on a shared
ancestor's contribution. Leaving it as is, with the shouting comment, is defensible for dead code.

---

### F6 — `Sort_Expection_Red`: merge weakens where the in-theory update strengthens

`Phi_BI/library/tools/lift_type_sort.ML:38-42`

```sml
structure Sort_Expection_Red = Theory_Data (
  type T = sort Symreltab.table   (*key: A and B*)
  val empty = Symreltab.empty
  val merge = Symreltab.join (K (uncurry (inter (op =))))
)
```

Symptoms: **S3** (merge performs a different, and opposite, operation from the accumulation the
module uses everywhere else).

`add_expected_sort_red` (`lift_type_sort.ML:44-53`) combines a new refinement into an existing key
with `curry (Sign.inter_sort thy) C`, i.e. the *sort intersection*, which in Isabelle is the greatest
lower bound — the **stronger** sort, computed by unioning and then normalising the class lists.
`merge` instead uses `inter (op =)`, the plain list intersection of the two class lists, which keeps
only the classes present in *both* and is therefore the **weaker** sort. Two parents that registered
different refinements for the same class pair `(A,B)` yield a child whose refinement is weaker than
either parent's, whereas within a single theory the same situation yields something stronger than
either.

Concrete consequence: `refined_sort_of` / `get_refined_sort_of_lifting_S`
(`lift_type_sort.ML:55-64, 131-140`) would hand back a less-refined sort, so
`Phi_Help.lift_type_sort` would pick a "good" instantiation that is not as good — a worse automation
result or a `LIFT_FAIL`, not unsoundness.

Severity: **latent**. Today the table is written from exactly one place — the seven-entry
`Theory.setup (add_expected_sort_red […])` at `lift_type_sort.ML:184-194` in Phi_BI. Every descendant
inherits the identical table, so `Symreltab.join`'s `pointer_eq` short-circuit (`table.ML:539-547`)
usually fires, and where it does not, `inter (op =) (S,S) = S`. It becomes observable only when two
sibling cones each call `add_expected_sort_red` for the same class pair with different results.

Smallest fix: `val merge = Symreltab.join (K (uncurry (Sign.inter_sort thy)))` is not directly
available (merge has no `thy`), so either use `Theory_Data'` — whose merge receives
`(theory * T) list` and can take the theory from the first parent — or store the raw class lists and
normalise on read. The cheap, correct-direction stopgap is `Symreltab.join (K (uncurry (union (op =))))`,
which at least errs toward the stronger sort like the in-theory update does.

---

### F7 — HOL-Statespace-derived data: `silent1 andalso silent2`, and an `error` inside merge

`Phi_Semantics_Framework/resource_space.ML:209-218` (`EntryData`),
`Phi_Semantics_Framework/Virt_Datatype/Virtual_Datatype.ML:204-214` (`ConstructorData`),
`Phi_Semantics_Framework/Statespace/state_space.ML:195-205` (`NameSpaceData`).
(The fourth copy, `state_space.bak.ML:203`, is in a file no theory loads.)

All three have the shape

```sml
  fun merge ({declinfo=…, distinctthm=…, silent=silent1}, {…, silent=silent2}) : T =
    {declinfo = join_declinfo (declinfo1, declinfo2),
     distinctthm = join_distinctthm_tab (distinctthm1, distinctthm2),
     silent = silent1 andalso silent2 (* FIXME odd merge *)}
```

Symptoms: **S3** (the `silent` component is recomputed by conjunction rather than inherited),
**S4** (`join_declinfo` calls `error` on conflict), **S5** (the `FIXME odd merge` comment).

On `silent`: it is a display flag, set by `set_silent` (`resource_space.ML:226-229`,
`Virtual_Datatype.ML:232`, `state_space.ML:223-227`) and read by `get_silent`. With one parent it is
inherited; with two it is `and`-ed, so a branch that set `silent = true` is silently overridden by a
sibling that did not. Cosmetic: the only effect is whether a warning is printed.

On `join_declinfo`: it is `Termtab.join (fn trm => uncurry (join_declinfo_entry (guess_name trm)))`
(`state_space.ML:173`), and `join_declinfo_entry` (`state_space.ML:159-169`) calls `error` when the
same component name carries two different types or two different statespace kinds. That is a genuine
consistency check living inside merge, and it is dead for single-parent theories. However the module's
own comment at `state_space.ML:176-187` states that *"on the theory level the info stays empty"* —
`declinfo` is only populated where the components are proof-context `fixes` — so at theory-begin the
tables being merged are empty and the check has nothing to check. I could not construct a failure.

Severity: **cosmetic**. All three are near-verbatim copies of Isabelle's own
`HOL/Statespace/state_space.ML`, `FIXME` and all; the divergence from upstream is not in the merge.

Smallest fix: none worth making in phi-system. If it is ever cleaned up, `silent = silent1 orelse silent2`
would at least make "someone asked for quiet" monotone, matching how the flag is used.

---

### F8 — `Symtab.merge pointer_eq`: closure identity as the conflict test

`Phi_System/library/system/generic_element_access2.ML:22-26` (`Hooks`, `final_hook Symtab.table`)
and `Phi_System/library/typeclass.ML:65-69` (`Data`, `typeclass Symtab.table`).

Symptoms: **S4**.

`Symtab.merge pointer_eq` raises `Symtab.DUP key` whenever both parents hold the key with values that
are not the *same ML pointer*. For entries inherited unchanged from a common ancestor the pointers do
coincide, so the common diamond is safe. The failure case is two sibling theories that each register
a hook (or typeclass) under the same name: even if the two registrations are textually identical, two
evaluations of the same `fn …` produce different closures, so merge raises `DUP` rather than
reporting a legible clash. The intra-theory guard is already `Symtab.update_new`
(`generic_element_access2.ML:39`), which raises `DUP` too — so the failure mode is at least
consistent, just unreadable.

Severity: **latent**, and mild — an unreadable exception instead of an error message, in a situation
(same hook name declared in two sibling theories) that is a genuine user mistake.

Smallest fix: `Symtab.join (fn k => fn _ => error ("Duplicate " ^ quote k ^ " …"))`, which produces a
legible message and is exactly as strict.

---

### F9 — `Alg_Decls` is keyed by the theory *short* name

`Phi_System/library/system/phi_type_definition.ML:56-60, 71-72`

```sml
structure Alg_Decls = Theory_Data (
  type T = declaration PriorityTab.table
  val empty = PriorityTab.empty
  val merge = PriorityTab.merge (K true)
)
fun add_algebraic_declaration (priority, decl) thy =
      Alg_Decls.map (PriorityTab.update_new ((priority, Context.theory_name thy), decl)) thy
```

Symptoms: **S6** (the key is a theory identity — and the wrong one).

The merge itself is the intended monotone accumulator and is correctly bypassed for a single parent.
The problem is next door: the key uses `Context.theory_name` (the **short** name) where the
comparable `Hooks` functor at `Phi_Logic_Programming_Reasoner/library/tools/Hook.ML:83` and
`Phi_System/library/system/procedure.ML:22, 26` both use `Context.theory_long_name`. Two theories
that share a short name (different sessions, or a session-qualified vs. unqualified load) and
register at the same priority collide; `update_new` would catch it within one cone, but across two
cones `PriorityTab.merge (K true)` keeps the first and **silently drops the second declaration**.
The dropped `declaration` is a `phi_type * algebra_hints -> local_theory -> phi_type * local_theory`
run by `invoke_algebraic_declarations` (`phi_type_definition.ML:74-78`) at every `\<phi>type` definition,
so losing one silently changes what gets derived.

Severity: **latent**. This is the same short-name-identity failure mode already recorded in the
repository's own bug report (`git log`: *"BUG report: a theorem's universal key depends on
theory-resolution order"*), so it is a known theme rather than a new discovery.

Smallest fix: `Context.theory_long_name thy`, matching `Hook.ML:83`.

---

### F10 — `premise_attribute`: a comment asserts an ordering that the data structure does not provide

`Phi_BI/library/system/premise_attribute.ML:21-38`

```sml
val data_eq = (op = o apply2 #1)
structure Data = Generic_Data (
  (*It relies on that the serial is incremental with time*)
  type T = (serial * bool * Reasoner_Group.group * bool * term * attribute list * Position.T) Net.net
  val empty = Net.empty
  val merge = Net.merge data_eq
)
fun register_attribute (…) = Data.map (Net.insert_term data_eq (pat, (serial(),…)))
```

Symptoms: **S5** (surrounding comment asserts a property merge does not preserve). Not S2 — `serial ()`
is called in `register_attribute`, *not* inside `merge`, so no side effect is skipped.

The merge is a monotone union deduplicated on the serial, which is fine. What is not fine is the
comment. Selection among matching attributes is `Phi_Help.max_of (int_ord o apply2 (#1 o #1))`
(`premise_attribute.ML:65`), and `max_of` (`Phi_Logic_Programming_Reasoner/library/helpers0.ML:135-136`)
is `foldl1 (fn (a,b) => if ord (a,b) = LESS then b else a)` — ties keep the **earlier** element in the
list. The list comes from `Net.match_term`, whose order is the net's insertion order, which after a
merge is `fold (insert_safe eq) (dest net2) net1` (`net.ML:252`) — i.e. determined by which parent
happened to be `hd thys`, and *not* determined at all when merge is skipped for a single parent.
So when two `\<phi>premise_attribute` declarations have equal `Reasoner_Group` priority and both match a
premise, which one wins depends on merge order and not on the serial, contradicting the comment.

Severity: **latent**, and I want to be plain: **I cannot construct an observable failure from the
source alone.** It requires two equal-priority matching attributes to actually exist, and I did not
enumerate the declarations. The measurement that would settle it: instrument
`apply_attribute` to log the full `Net.match_term` result whenever two entries tie on
`#1 o #1`, then run a phi-system build and see whether any tie occurs. If none does, the comment is
merely misleading; if one does, the chosen attribute is build-order-dependent.

Smallest fix: make the tie-break explicit — sort by `(prio, serial)` before `max_of`, or delete the
comment if the ordering was never actually relied on.

---

## 3. Cleared

Every remaining live instance, checked and found sound. "Monotone" below means: no side effects, no
mutable cells, and `merge [x] = x` in spirit, so the single-parent shortcut is a correct optimisation.

#### Theory_Data

- `Debt_Axiom/kernel.ML:5` — `term Symtab.table`; `Symtab.merge (op aconv)` is monotone union; the `DUP` it can raise is a genuine same-name/different-proposition clash, and `discharge`'s deletions can only be *lost* by merge (debt over-reported), never silently satisfied.
- `Phi_BI/library/tools/syntax_group.ML:21` — `Name_Space.merge_tables` on a `Name_Space.table`; the standard monotone name-space merge.
- `Phi_Logic_Programming_Reasoner/library/properties.ML:95` — `term Net.net`, `Net.merge (op aconv)`; nets never raise.
- `Phi_Semantics_Framework/resource_space_more.ML:42` — `(term*term) Symtab.table`, `Symtab.merge (op =)`; structural equality, `DUP` only on a real clash.
- `Phi_System/library/system/generic_variable_access2.ML:82` — pair of `Symtab`s, `(K true)` / `(op =)`; monotone.
- `Phi_System/library/system/opr_stack.ML:223` — `operator_info Symtab.table`, `Symtab.merge (op =)`; `operator_info` is a tuple of ints so equality is exact; identical inherited entries compare equal and are kept.
- `Phi_System/library/system/procedure.ML:43` — `interface Symtab.table Symtab.table`, `Symtab.merge (K true)`; the outer key is `Context.theory_long_name` and only ever written by the theory it names (`procedure.ML:24-27`), so no key is ever written by two theories.
- `Phi_System/library/system/processor.ML:98` — `Symtab.join (K (Ord_List.merge proc_ord))`; total combiner, monotone.

#### Generic_Data

- `Phi_BI/library/tools/adhoc_overloading.ML:65` — `Symtab.merge_list` + `Termtab.join` with an equality check that calls `err_duplicate_variant`; a legible error on a genuine clash, and the clash is impossible with one parent.
- `Phi_BI/library/tools/CoP_simp.ML:61` — `Net.merge pointer_eq`; nets never raise.
- `Phi_Logic_Programming_Reasoner/library/envir_var.ML:30` — `Symtab.join` with a total combiner.
- `Phi_Logic_Programming_Reasoner/library/priority_group.ML:48` — `Name_Space.merge_tables`.
- `Phi_Logic_Programming_Reasoner/library/properties.ML:157` — `Net.merge property_eq`.
- `Phi_Logic_Programming_Reasoner/library/properties.ML:165` — `Net.merge template_eq` (dedups on serial; union).
- `Phi_Logic_Programming_Reasoner/library/reasoner.ML:383` — `Symtab.merge (K true)` on a set.
- `Phi_Logic_Programming_Reasoner/library/reasoner.ML:435` — `iNet.merge registry_eq`; `iNet` is purely functional (`improved_net.ML:203`) and `merge` uses `insert_safe`.
- `Phi_Logic_Programming_Reasoner/library/reasoner.ML:1092` — `iNet.merge DRG_eq`.
- `Phi_Logic_Programming_Reasoner/library/reasoner.ML:1159` — `iNet.merge rule_pass_eq`.
- `Phi_Logic_Programming_Reasoner/library/reasoners.ML:565` — `iNet.merge filtered_out_eq`; the clash `error` lives in `add_…` (`reasoners.ML:589-591`), not in merge.
- `Phi_Logic_Programming_Reasoner/library/tools/Hook.ML:74` and `:121` — `PriorityTab.merge (K true)`, keyed by `(priority, Context.theory_long_name)`; monotone, correct identity.
- `Phi_Logic_Programming_Reasoner/library/tools/simpset.ML:69` — `Raw_Simplifier.merge_ss`, the standard simpset merge. `empty` is a snapshot taken at functor-application time via `Context.the_local_context ()` (`simpset.ML:40-58`), which is intended and documented at `simpset.ML:5-7`.
- `Phi_Logic_Programming_Reasoner/library/tools/statistics.ML:65` — `Symtab.merge (op =)` on a set.
- `Phi_Logic_Programming_Reasoner/library/tools/statistics2.ML:18` — `Symtab.join (K (Net.merge (op aconv)))`.
- `Phi_Logic_Programming_Reasoner/library/tools/term_pattern_store.ML:46` and `type_pattern_store.ML:38` — `Net.merge data_eq`; the `INSERT`-to-`error` conversion is in `add`, not merge.
- `Phi_Logic_Programming_Reasoner/library/type_info_DB.ML:38` — `Symtab.join (K (Symtab.merge entry_eq))`.
- `Phi_Semantics_Framework/resource_space.ML:244`, `Virt_Datatype/Virtual_Datatype.ML:251`, `Statespace/state_space.ML:264` — `Symtab.merge (K true)`.
- `Phi_Semantics_Framework/Statespace/state_fun.ML:102` — `(merge_ss, merge_ss, b1 orelse b2)`; monotone in all three components.
- `Phi_System/library/instructions.ML:19` — `Symtab.join (fn _ => fn _ => raise Symtab.SAME)`; keeps the first, never raises `DUP`.
- `Phi_System/library/phi_type_algebra/commutativity.ML:72`, `:87`, `:268`, `:357` — `iNet.merge` / `Net.merge`.
- `Phi_System/library/phi_type_algebra/tools/BNF_fp_sugar_more.ML:47` — `Symtab.merge fp_more_eq`; structural equality on the stored terms, `DUP` only on a real clash.
- `Phi_System/library/phi_type_algebra/tools/extended_BNF_info.ML:146` — `Symtab.merge (K true)`.
- `Phi_System/library/phi_type_algebra/tools/extended_BNF_info.ML:319` — `Symreltab.merge (K true)`; a lazily filled cache, first-writer-wins is correct.
- `Phi_System/library/phi_type_algebra/typ_def.ML:339`, `:522`, `:672` — `Net.merge`.
- `Phi_System/library/phi_type_algebra/typ_def.ML:512` — `Name_Space.merge_tables`.
- `Phi_System/library/phi_type_algebra/weight.ML:72` — `Net.merge record_eq`.
- `Phi_System/library/syntax/procedure2.ML:26` — `Symtab.merge (K true)`.
- `Phi_System/library/system/app_rules.ML:72` — `Name_Space.join_tables (K (iNet.merge …))`; total combiner.
- `Phi_System/library/system/generic_variable_access.ML:523` — `merge_options` on an `option`; first-writer-wins, monotone.
- `Phi_System/library/system/opr_stack.ML:319` — `Symtab.merge (op =)` on a set.
- `Phi_System/library/system/phi_type_definition.ML:62` — `Symtab.merge (def_eq o apply2 #def)`; the key *is* the constant name that `def_eq` compares, so entries sharing a key always compare equal and merge never raises.
- `Phi_System/library/system/Phi_Working_Mode.ML:74` — `Symtab.merge (K true)`.
- `Phi_System/library/typeclass.ML:65` — see F8 (`Symtab.merge pointer_eq`); listed there, not here.

#### Proof_Data

`Proof_Data` has no merge function at all, so the merge misconception cannot apply; each of these was
checked only for a mutable cell in `T` and for an `init` that captures shared state. All of the
mutable cells below are `Synchronized.var`s or `ref`s **allocated per use at the call site** and
stored in a list/option whose `init` is `K []` / `K NONE`, i.e. the cell is created fresh each time
the feature is entered, not shared through `init`.

- `Phi_BI/library/system/Phi_ID.ML:39` — `init = K ("",[0])`, immutable.
- `Phi_Logic_Programming_Reasoner/library/exhaustive.ML:12` — `thm list Synchronized.var list`, `init = K []`; the var is allocated at `exhaustive.ML:60` per exhaustive-reasoning entry.
- `Phi_Logic_Programming_Reasoner/library/exhaustive_divergen.ML:11` — same shape, var allocated at `:20`.
- `Phi_Logic_Programming_Reasoner/library/handlers.ML:27` — `init = K (0,[])`, immutable; the serial counter is per-context, not global.
- `Phi_Logic_Programming_Reasoner/library/nested.ML:13` — `int`, `init = K 0`.
- `Phi_Logic_Programming_Reasoner/library/optimum_solution.ML:28` — `cost`, `init = K (0,0)`.
- `Phi_Logic_Programming_Reasoner/library/optimum_solution.ML:33` — `… Synchronized.var list`, `init = K []`; var allocated at `:90`.
- `Phi_Logic_Programming_Reasoner/library/pattern_translation.ML:54` — a function value, `init = K (K (K NONE))`.
- `Phi_Logic_Programming_Reasoner/library/rule_generation.ML:243` — three function values, immutable.
- `Phi_Logic_Programming_Reasoner/library/Subgoal_Env.ML:29` — the `subgoal` datatype carries a `bool Synchronized.var` (`:17`), but each is allocated per subgoal at `:71`; `init` itself is a constant.
- `Phi_Logic_Programming_Reasoner/library/tools/failure_reason.ML:26` — `… Synchronized.var option`, `init = K NONE`, allocate-on-write at `:37`; the var is deliberately shared downstream to collect reasons, and `Synchronized` makes that thread-safe.
- `Phi_Logic_Programming_Reasoner/library/tools/ml_thms.ML:20` — `init _ = (Inttab.empty, [])`.
- `Phi_Logic_Programming_Reasoner/library/tools/statistics.ML:207` — nested `Unsynchronized.ref`s, `init = K NONE`, allocated at `:220`/`:227`; the value records a CPU timer plus the owning `Thread.Thread.self ()`, so it is per-thread by construction.
- `Phi_Semantics/library/basic_recursion.ML:40`, `cf_routine.ML:16` — `bool`, `init = K false`.
- `Phi_Semantics/library/variable_pre.ML:10` — `string Symtab.table`, `init = K Symtab.empty`.
- `Phi_System/library/additions/local_value.ML:26` — `init = K Symtab.empty`.
- `Phi_System/library/system/generic_variable_access.ML:84` — `value_context option`, `init = K NONE`.
- `Phi_System/library/system/opr_stack.ML:209` — `opr_stack`, `init = K init_opr_stack`.
- `Phi_System/library/system/Phi_Envir.ML:58` — list of `(thm, thm, thm list lazy, int)`, `init = K []`.
- `Phi_System/library/system/Phi_Envir.ML:275` — `cterm list`, `init = K []`.
- `Phi_System/library/system/Phi_Working_Mode.ML:99` — `working_mode option`, `init = K NONE`.
- `Phi_System/library/system/Phi_Working_Mode.ML:226` — `int`, `init = K 0`.
- `Phi_System/library/system/post-app-handlers.ML:48` — `Proof.state option`, `init = K NONE`.
- `Phi_System/library/system/sys.ML:76` — `int`, `init = K 0`.
- `Phi_System/library/system/toplevel.ML:167` — a record option, `init = K NONE`.
- `Phi_System/library/tools/guess_literal_number_type.ML:29` — `init = K Typtab.empty`; the module's `Synchronized.var synthesisable_literals` (`:57`) is module-level global state, not part of the data.
- `Phi_System/library/tools/named_premises.ML:25` — `init = K (Symtab.empty, "prem_a")`.
- `Phi_BI/library/tools/Phi_Help.ML:210` and `:239` — see F4.

#### Not live

- Inside comments: `Phi_Logic_Programming_Reasoner/library/reasoner.ML:376`,
  `Phi_Logic_Programming_Reasoner/library/tools/extracting_pure_facts.ML:25`,
  `Phi_System/library/additions/overloaded_synthesis.ML:95`,
  `Phi_System/library/phi_type_algebra/deriver_framework.ML:403`,
  `Phi_System/library/system/app_rules.ML:44`,
  `Phi_System/library/system/generic_variable_access.ML:138`,
  `Phi_System/library/system/procedure.ML:63`.
- In `Phi_Semantics_Framework/Statespace/state_space.bak.ML:203, :272` — the file is never loaded;
  only `state_space.ML` is, from `Phi_Semantics_Framework/Statespace/StateSpaceLocale.thy:11`.

---

# Part II — the rest of `contrib/`

Scope: `contrib/Isa-Mini`, `contrib/AutoCorrode`, `contrib/Semantic_Embedding`,
`contrib/Performant_Isabelle_ML`, `contrib/auto_sledgehammer`, `contrib/Isabelle_RPC`,
`contrib/Automation_Base`. Distributions (`Isabelle2024*`, `Isabelle2025-2`, `afp-*`) and
`build/` subtrees excluded. All paths below are relative to `/home/qiyuan/Current/MLML/contrib/`.

The enumeration was produced by grepping every `*.ML`/`*.thy`/`*.sml` in the repository for a
functor application of the three functors and subtracting the excluded trees; the result
matched the file list I was given exactly, with two additions the hit-count summary missed
because they go through a wrapper functor: `Isa-Mini/library/my_object_logic.ML:140,145`
instantiate `iNet_Thm_Collection`, which internally applies `Generic_Data`
(`Performant_Isabelle_ML/library/inet_collection.ML:61`).

## 1. Verdict

**31 functor applications** exist in scope (6 `Theory_Data`, 1 `Theory_Data'`, 10
`Generic_Data`, 14 `Proof_Data`), plus 3 more `iNet_Collection` instantiations inside
`Performant_Isabelle_ML/Test/Test_iNet_Collection.thy` that are test code reusing an
already-cleared functor. **One** instance is a genuine, multi-symptom instance of the hunted
misconception: `Thm_Vector` in
`Semantic_Embedding/Tools/Sledgehammer/sledgehammer_embedding.ML:209`, whose `merge`
allocates `Synchronized.var`s (a side effect that silently never happens on the single-parent
path) around a mutable cache cell that is shared by reference through the rest of the cone.
It is a **latent** defect rather than a live one only because the theory that loads that file
is dormant — nothing in the repository imports `Sledgehammer_Embedding.thy` except its own
test theory, and the session ROOT does not build it. **Three** further instances are
S1-shaped (a mutable cell inside a `Proof_Data` value): `Term_Serial_Index.Local_Registry`
(dead code today), `Isa-Mini`'s `IPS_Data` `Unique_Counter` (deliberate and documented), and
AutoCorrode's `TimingData` (third-party). **Two** are cosmetic S3s where `merge` deduplicates
by name but the same deduplication never runs on the linear-import path that actually
matters. Everything else is the intended monotone-accumulator use and is listed in §3.

`Semantic_Embedding`'s `Thm_Cache` (`Tools/semantic_store.ML:896`) deserves an explicit
"checked and sound": it is the one place in scope where a bypassed merge could plausibly lose
data, and it does not, because its `Theory.at_begin` hook recomputes the delta against the
stored `Facts.T` snapshot at every begin and therefore repairs any parent whose contribution
the bypass dropped. Details in §3.

`AutoCorrode` is **third-party code**: `git remote -v` inside `contrib/AutoCorrode` gives
`origin https://github.com/awslabs/AutoCorrode` with a personal fork (`xqyww123/AutoCorrode`)
as a second remote, and `git log -S` attributes every one of its 13 hits to upstream AWS
authors (Hanno Becker, Ike Mulder) — e.g. the six `Theory_Data` structures in
`Crush/seplog.ML` come from "Crush: move picker/rotation infrastructure into
Crush/seplog.ML", Hanno Becker, 2026-05-11. None of them is a finding anyway.

Already known, no analysis performed: `Universal_Key.Cache_Scope`,
`Isabelle_RPC/Tools/Universal_Key.ML:619` — diagnosed and fixed by moving reconciliation into
`Theory.at_begin claim_cache_scope` (`Universal_Key.ML:701`).

## 2. Findings

### F1 — `Thm_Vector`: merge allocates mutable cells, so the cache silently forks (and never initialises on the path the author expected)

`Semantic_Embedding/Tools/Sledgehammer/sledgehammer_embedding.ML:209-217`

```sml
structure Thm_Vector = Theory_Data (
  type T = vector Termtab.table Symtab.table Synchronized.var option
  val empty = NONE
  fun merge (NONE, NONE) = SOME (Synchronized.var "Thm_Vector" Symtab.empty)
    | merge (NONE, some) = some
    | merge (some, NONE) = some
    | merge (SOME va, SOME vb) = SOME (Synchronized.var "Thm_Vector" (
        Symtab.join (K (Termtab.merge (K true))) (Synchronized.value va, Synchronized.value vb)))
)
```

Symptoms: **S1, S2, S3, S5**.

*What the cell holds.* A `Synchronized.var` whose content maps an embedding-model id
(`string`) to a `Termtab` from a theorem's proposition to its embedding vector — a pure cache
of "what does the embedding service say about this proposition". It is mutated long after the
theory that created it: `cached_embed_premises` writes through it at
`sledgehammer_embedding.ML:285-296` (`Synchronized.change vecs_var ...` and
`Synchronized.change gvar ...`), reached from `relevant_facts` (`:309-312`) and from
`update_premises` (`:379-391`).

*S2 — the side effect in `merge`.* Both the `(NONE, NONE)` and the `(SOME, SOME)` branches
call `Synchronized.var`, which allocates a fresh mutex-guarded cell. Neither allocation
happens for a theory with one parent, nor for a theory with several parents of which only one
carries the kind (`Isabelle2025-2/src/Pure/context.ML:447-456`).

*S5 — what the code assumes.* The `(NONE, NONE)` branch only makes sense as "when a theory
begins with no cache anywhere above it, mint one", i.e. as an initialiser that the author
expected `merge` to run at every begin. It cannot serve that purpose: with `empty = NONE` and
no entry in either parent, `map_filter` at `context.ML:450` yields `[]` and `merge` is not
called at all, so the branch is unreachable except for two parents that both explicitly
`put NONE`. The two "not initialized" `error`s at `:311` and `:388` are the fallback for
exactly the state that branch was meant to prevent. In practice initialisation is rescued by
`Theory.setup (Thm_Vector.put (SOME (Synchronized.var ...)))` at `:393-394`, which plants one
cell in the theory that loads the file — so the dead branch is harmless, but the code reads as
if `merge` were an initialisation hook.

*S1 + S3 — the concrete failure I can construct.* Because `:394` puts the cell in
`Sledgehammer_Embedding` itself, every descendant inherits *that same cell object* by
reference (single-parent verbatim inheritance, `context.ML:448`). Now let `A` and `B` both
import `Sledgehammer_Embedding` and let `C` import both `A` and `B`. `C` has two parents that
both carry the kind, so `merge` runs — and hands `C` a **brand-new** `Synchronized.var`
holding a snapshot join of two values that are, in the common case, the *same* value read
twice. From that point on:

- every `Synchronized.change` performed while working inside `C`'s cone writes to `C`'s
  private cell and is invisible to `A`, `B`, and any other cone;
- every embedding computed after the fork anywhere else is invisible to `C`.

Observably: sledgehammer's `embd` fact filter in `C` re-issues embedding RPCs
(`Remote_Procedure_Calling.call_command embed_premises_cmd`, `:250-263`) for propositions
whose vectors were already paid for in `A` — repeated wall-clock cost and repeated calls to
the embedding service, with no error and no warning. The result stays *correct* (an embedding
is a function of the proposition, not of the theory), so this is a cost defect, not a
soundness defect. The mirror hazard is the same cell being shared across sibling cones that
never merge — also benign for the same reason, but it means the data is not theory-scoped at
all despite living in `Theory_Data`.

*Severity: latent.* Nothing in the repository imports `Sledgehammer_Embedding.thy` except
`Semantic_Embedding/Sledgehammer_Embedding_Tetst.thy:2`, and `Semantic_Embedding/ROOT` lists
only `Semantic_Embedding` under `theories`, so the file is not in the built session. (A stale
copy also sits at `Isabelle2024_removed_backup/src/HOL/Tools/Sledgehammer/sledgehammer_embedding.ML`,
from when it was patched into HOL; out of scope.) I cannot tell from the source whether any
external driver loads the theory dynamically — grepping `*.py`, `*.json`, `*.sh`, `*.scala`
for `Sledgehammer_Embedding` found nothing, so as far as the repository goes it is dormant.
The measurement that would settle it: start the REPL, load `Sledgehammer_Embedding`, and print
`Sledgehammer_Embedding.cache_scope`-style identity — concretely, compare
`Thm_Vector.get thy` pointer identity between a diamond child and its parents.

*Smallest fix.* Make `merge` total and non-allocating by keeping the first available cell,
exactly as `Universal_Key.Cache_Scope` now does (`Universal_Key.ML:628-636`):

```sml
  fun merge (NONE, some) = some
    | merge (some, _) = some
```

That removes S2 and S3 and makes the diamond child keep sharing its parents' cell. If a
genuinely fresh cache per cone is ever wanted, it has to be minted in `Theory.at_begin`, not
in `merge`.

### F2 — the same file's `at_begin` hook does unbounded network work at every descendant theory begin

`Semantic_Embedding/Tools/Sledgehammer/sledgehammer_embedding.ML:393-399`

```sml
val _ = Theory.setup (
            Thm_Vector.put (SOME (Synchronized.var "Thm_Vector" Symtab.empty))
         #> Theory.at_begin (fn thy =>
              let val target_ids = ["test"] (*space_explode "," (getenv "ISABELLE_PREBUILD_PREMISE_EMBEDDING")*)
               in List.app (fn model_id => update_premises model_id thy) target_ids
                ; NONE
              end))
```

This is the wrapper-side counterpart of F1, so I report it here rather than in §3. It does
**not** have the non-termination bug — it returns `NONE` unconditionally, so
`Theory.apply_wrappers` (`Pure/theory.ML:186-205`) runs it once per begin and stops. The
problem is what it does in that one run: `update_premises` (`:379-391`) calls
`Sledgehammer_Fact.all_facts` over the whole theory and then `cached_embed_premises`, which
opens an RPC connection (`Remote_Procedure_Calling.load ["Isabelle_Semantic_Embedding"]`,
`:232`) and embeds every not-yet-cached fact. The model-id list is hard-wired to `["test"]`
because the environment-variable gate that was meant to control it is commented out on the
same line. So *every* theory beginning below `Sledgehammer_Embedding` performs a full fact
sweep plus embedding RPCs, and a begin will fail outright if no Python RPC host is running.
Same dormancy caveat as F1.

*Severity: latent (blocker the moment the theory is imported for real).*
*Smallest fix:* restore the `getenv` gate so `target_ids` is empty unless
`ISABELLE_PREBUILD_PREMISE_EMBEDDING` is set, and return `NONE` early when it is.

### F3 — `Term_Serial_Index.Local_Registry`: a mutable ref holding mutable hash tables inside `Proof_Data`

`Semantic_Embedding/Tools/term_serial_index.ML:44-47`

```sml
structure Local_Registry = Proof_Data (
  type T = local_state option Unsynchronized.ref
  val init = fn _ => Unsynchronized.ref NONE
)
```

where `local_state` (`:37-41`) is `{net_ref: serial iNet.net Unsynchronized.ref, term_tab:
term Inthashtab.table, thm_tab: thm Inthashtab.table}` — one ref plus two `Inthashtab`s, which
are mutable hash tables from `Performant_Isabelle_ML`.

Symptom: **S1**. `Proof_Data` has no `merge`, so the merge-bypass misconception does not apply;
what does apply is the sharing-by-reference half of S1. `Proof_Context.init_global` runs every
registered `init` eagerly (`Isabelle2025-2/src/Pure/context.ML:585-586, 612-614`), so each
`init_global` gets its own ref — but every context *derived* from it copies the `Datatab`
entry and therefore shares that ref. A serial minted inside one branch of a proof search is
visible in a sibling branch, and is not rolled back when a branch is discarded, because
context values are persistent while the cell inside them is not.

Thread safety is, somewhat surprisingly, fine: every mutation of the local ref and of the
local `Inthashtab`s happens inside `Synchronized.change_result state` (`:106-116`), where
`state` is the module's single global var (`:34`), so the global var doubles as the lock for
the per-context state. Worth recording, because it is not obvious and a future refactor that
moves a table update outside that critical section would introduce a real race on a mutable
hash table.

Two adjacent observations about the same module, not themselves `Theory_Data` instances but in
the same S6 family: `term_tab`, `deriv_cache` and `thm_tab` (`:24-34`) are **process-global**
`Inthashtab`/`Strhashtab`s, never cleared. `thm_tab` retains a `Thm.trim_context`'d theorem per
serial forever, and `thm_of_serial` (`:141-149`) pushes it through
`Global_Theory.transfer_theories thy` — which will fail or misbehave if the serial was minted
in a theory outside `thy`'s cone. In a long-lived Isa-REPL process serving many unrelated
scratch theories, that is exactly the "identity valid only over a population" hazard.

*Severity: latent, and currently dead.* Grepping the whole repository for
`Term_Serial_Index.`, `serial_of_thm`, `thm_of_serial` finds no caller outside
`term_serial_index.ML` itself; `serial_of_term` and `term_of_serial` are commented out
(`:89-99`, `:130-139`). Nothing runs today.
*Smallest fix if it is ever wired up:* key the global tables by cone (or clear them per
theory) and make `thm_of_serial` return `NONE` instead of transferring when the stored thm's
theory is not an ancestor of `thy`.

### F4 — `IPS_Data`'s `Unique_Counter` is a `Synchronized.var` inside `Proof_Data`

`Isa-Mini/library/proof.ML:865-878`, installed at `:2185-2186`.

```sml
  | Unique_Counter of int Synchronized.var
...
structure IPS_Data = Proof_Data (
  type T = ( counter * counter * string )
  val init = K (Consecutive_Counter 0, Consecutive_Counter 0, "")
)
```

Symptom: **S1**, deliberately. `init_ctxt` (`:2180-2190`) mints the two vars only when
`counter_mode = "unique"`; in that mode `incr_premise_counter`/`incr_fact_counter`
(`:886-888`, `:900-902`) advance the shared cell and return the *unchanged* context, so the
counter is immune to context backtracking on purpose — that is the documented semantics
("Numbers are never reassigned or changed", `:866-868`). The consequence is already written
down at `:891-899`: prerunning an operation that touches these counters "would permanently
skip numbering", and `derived_subgoals_of` lists exactly which callers are verified
counter-clean. `Proof_Data` has no `merge`, and nothing here depends on a merge running.

*Severity: cosmetic (by design, with the hazard documented at the call site).* No fix
proposed; the note is here only so the instance is not mistaken for an oversight on a later
pass.

### F5 — `Pre_Simproc.Data`: the name-deduplication in `merge` never runs on the path that produces duplicates

`auto_sledgehammer/library/pre_simproc.ML:22-28`

```sml
structure Data = Generic_Data(
  type T = entry list
  val empty = []
  fun merge (a, b) =
    let val names = fold (fn {name, ...} => Symset.insert name) b Symset.empty
    in filter (fn {name, ...} => not (Symset.member names name)) a @ b end
)
```

Symptom: **S3**. `merge` implements "an entry from the right-hand parent replaces the
same-named entry from the left". But `register = Data.map o cons` (`:30`) does no such check,
so registering a name twice along a *linear* import chain leaves both entries in the list, and
`merge` — the only place that would collapse them — is skipped for single-parent theories
(`context.ML:448`). The observable difference: with duplicates present, `pre_simproc_conv`
(`:37-47`) tries the newest entry first and, if its `proc` returns `NONE` or leaves premises,
**falls through to the older same-named entry**; had `merge` run, the older one would be gone
and the conversion would move on to a different name. So a re-registration means "shadow with
fallback" on the linear path and "replace" on the diamond path.

*Severity: cosmetic.* `Pre_Simproc.register` has **zero call sites** anywhere in the
repository (including `phi-system`), so the list is empty in practice.
*Smallest fix:* make `register` do what `merge` does — drop any existing entry with the same
name before consing.

### F6 — `RecordLocalityData`: same shape, third-party

`AutoCorrode/Autogen/AutoLocality.thy:73-81`. `merge` is `Symtab.merge_list` with an equality
on `const_name`, i.e. it deduplicates entries per record; but
`add_record_locality_entry_generic` (`:83-95`) appends with `ls @ [entry]` unconditionally, so
registering the same constant twice down a linear chain leaves two entries that no merge ever
collapses, and consumers iterating the list see the footprint twice.

Symptom: **S3**. *Severity: cosmetic*, and it is upstream AWS code (attributed to Hanno
Becker, "Initial commit", 2025-03-31) — I would not patch it in this fork.

## 3. Cleared

Semantic_Embedding:
- `Tools/semantic_store.ML:896` `Thm_Cache` (`{entries, intro, elim, induct, case_ :
  cached_thm_entry list, facts : Facts.T}`) — merge is a per-bucket dedup by universal key plus
  `Facts.merge`, with the `Bytehashtab` allocated *inside* `merge` and never escaping (`:914`),
  so no S1/S2. It is technically S3 (it deduplicates), but a bypassed merge cannot lose
  anything: the `Theory.at_begin update_thm_cache` hook (`:2146-2183`) recomputes
  `Facts.dest_static false [cached_facts] current_facts` at every begin, and since the beginning
  theory's own `Global_Theory.facts_of` is the union of all its parents', any parent's
  contribution that the bypass dropped reappears in that delta and is re-processed. The only
  bypass-visible difference is list *order* (the merge path reverses each bucket via
  `fold add a (fold add b [])`), which no consumer appears to depend on.
- `Tools/semantic_store.ML:2183` `Theory.at_begin update_thm_cache #> Theory.at_end
  update_thm_cache` — terminates correctly: the hook returns `SOME` only when `new_facts` is
  non-empty, and its `put` sets `facts = current_facts`, so the re-run mandated by
  `Theory.apply_wrappers` sees an empty delta and returns `NONE` (`:2149-2152`, `:2174-2181`).
  This is the "at least one extra pass" that `Universal_Key.ML:648-652` documents relying on.
- `Tools/infra_filter.ML:55` `Infra_Decl` (`Symtab.set * thm iNet.net * Symtab.set`) —
  `Symtab.merge (K true)` twice and `iNet.merge Thm.eq_thm_prop`; monotone, no cells.
- `Tools/Sledgehammer/sledgehammer_embedding.ML:219` `Thm_Vector_Local` — `Proof_Data`, no
  merge; `init` allocates one var per `Proof_Context.init_global` and copies only a pointer to
  an immutable `Symtab`, so it is cheap and per-context by construction. Its whole point is
  that local writes are discarded, which is coherent.
- `Tools/term_serial_index.ML:44` — see F3.

Isa-Mini:
- `Agent/agent_hint.ML:48` — pair of `Symtab.merge (K true)`; monotone.
- `library/my_object_logic.ML:140` `Atomize`, `:145` `Rulify` — `iNet_Thm_Collection`, hence
  `iNet.merge Thm.eq_thm_prop`; monotone.
- `library/proof.ML:873` `IPS_Data` — see F4.
- `library/proof.ML:1323` `Calc_Data` (`(thm * int) list`) — `Proof_Data`, immutable, no merge.
- `library/proof.ML:4969` `Locale_Interpretation_Qualifiers` (`Symtab.set`) — `Proof_Data`;
  the comment at `:4966-4968` correctly says it is rebuilt with the context, which is what
  `Proof_Data` gives.
- `translator/library/translator.ML:4747` `Consider_Branch` — `Proof_Data`, immutable tables.
- `translator/library/translator_auxcmds.ML:15` `MProof_Data` (`Proof.state list`) —
  `Proof_Data`, immutable; both write sites are commented out (`:69`, `:79`) and its only
  reader `local_qed` (`:22-30`) is itself dead (`val mqed = local_qed` is commented at `:34`).

Performant_Isabelle_ML:
- `library/inet_collection.ML:61` (inside `functor iNet_Collection`) — `iNet.merge eq`;
  `iNet.net` is a purely functional datatype (`library/improved_net.ML:198-205`), so no S1.
  Covers the three test instantiations in `Test/Test_iNet_Collection.thy:33,52,57`.
- `library/merely_rewrite.ML:158` — a comment about how to write a merge, not an instance.

auto_sledgehammer:
- `library/pre_simproc.ML:22` — see F5.
- `library/Phi_ID.ML:39` `ID` (`string * int list`) — `Proof_Data`, immutable.
- `library/ground_eval.ML:1` `Eval_Thunk_Data` (`unit -> term`) — `Proof_Data`, immutable
  closure; `init` raises on use before set, which is the right default.
- `library/cache_file.ML:691` `Theory.at_end` — returns `NONE` unconditionally, so no
  `apply_wrappers` loop; it does not assume anything about which theories it covers, and its
  global state lives in `Synchronized.var`s (`openning_stores :534`, `hash_cache`,
  `append_locks :392`) keyed by theory long name / cache-file path, not in `Theory_Data`. The
  concurrency reasoning is spelled out at `:362-390` and `:520-543`.

Automation_Base:
- `default_num_typ.ML:11` (`typ option`, `merge = merge_options`) — total, no side effects,
  `merge [x] = x`; picks the left parent on conflict, which is the standard idiom here.

Isabelle_RPC:
- `Tools/Universal_Key.ML:619` `Cache_Scope` — known, already fixed.

AutoCorrode (third-party, upstream `awslabs/AutoCorrode`):
- `Crush/seplog.ML:8,13,160,165` (`int -> int -> thm option` / `int -> thm option`) — merge is
  first-hit-wins composition of two lookup functions; effect-free, `merge [x] = x`.
- `Crush/seplog.ML:20,170` (`int` cache limits) — `Int.max`; monotone.
- `Crush/crush.ML:120` `URustContractSimps` (`simpset`) — `merge_ss`, Isabelle's own simpset
  merge; `empty` is a value built from `@{context}` at load time, which is the usual pattern.
- `Crush/crush.ML:511` `CrushData` — `Proof_Data` of four optional callbacks; immutable.
- `Crush/parsers.ML:76` `MLParser.Data` (`{tmp_data: T option}`, `merge_options`) — a scratch
  slot used to carry a value out of `ML_Context.expression` (`:92-99`); the mutated context is
  discarded after `the_tmp_data` reads it, so nothing persists into the theory.
- `Crush/time.ML:56` `TimingData` — `Proof_Data` containing
  `TimingStatistics Unsynchronized.ref option`, mutated at `:237-258`. S1-shaped (the ref is
  shared by every derived context and survives backtracking), but it is a timing log with no
  effect on proof results, and it is upstream code. Noted, not actioned.
- `Shallow_Micro_Rust/Micro_Rust_Shallow_Embedding.thy:58` `RustPathResolution` (`string
  Symtab.table`, `merge = Symtab.merge (op =)`) — S4 on paper: the strict-equality merge raises
  `Symtab.DUP` on two parents mapping one Rust path to different HOL names, and that check is
  dead when merge is bypassed. It is not a gap, though: the only writer,
  `add_rust_path_resolution` (`:65-67`), uses `Symtab.insert (op =)`, which raises on exactly
  the same conflict along the single-parent path. The conflict cannot slip through.
