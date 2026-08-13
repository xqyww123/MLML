# Can `Theory_Hash.hash_of` return two different values for one long name in one process?

## Verdict

**REACHABLE.**

Measured, in a live process, twice over, by two independent routes:

```
[HASH thy1 real] 2ec6c541898e932a3ad4d0c37773e9f3     (long name HOL.List)
[HASH thy2 fake] 408e07a30bcc5dd387fbc870590b9946     (long name HOL.List)
[VERDICT hash] two hashes for long name HOL.List differ = true
```

```
[1] hash of UK_Probe_C.Aux_Thy (v1) = 3442b5d18c3ca3897a2453a7dab87178
[4] hash of UK_Probe_C.Aux_Thy (v2) = 20e0660f4c885bd2c92e731aa048fbf9
[VERDICT loader] hash moved within one process = true
```

Both hashes in each pair are *persistent* hashes (LSB of byte 0 clear), i.e. content
digests, not the content-independent WIP fallback. Both caches named in the question are
demonstrably poisoned as a consequence — the `Universal_Key.cache` poisoning and the
constituents-cache staleness are each shown below with the actual bytes.

Both of the "apparent blocks" I was asked to verify turn out to be false as stated.

---

## 1. Static enumeration: every route in this repository that begins a theory

Distribution trees (`contrib/Isabelle2024*`, `contrib/Isabelle2025-2`, the two AFP
snapshots) are excluded from "this repository" except where Pure itself is the caller,
which I list separately at the end.

| # | Site | Name it begins under | Can that name be in `loaded_theories`? |
|---|---|---|---|
| 1 | `/home/qiyuan/Current/MLML/contrib/Isa-REPL/library/REPL.ML:442` (`Resources.begin_theory base_dir header parents`) | `Long_Name.qualify thy_qualifier base`, built at `REPL.ML:422` | **YES** — see §1.1 |
| 2 | `/home/qiyuan/Current/MLML/contrib/Isa-REPL/library/REPL.ML:1101` (`parse_thy_header`, same `qualify_name`) | same | **YES**, same reason; this one only builds the header, the `begin_theory` is still #1 |
| 3 | `/home/qiyuan/Current/MLML/contrib/Isa-REPL/library/REPL.ML:367`, `:379`, `:385` (`Thy_Info.use_theories … thy_qualifier`) | qualified by `thy_qualifier` | **YES** — see §1.2 |
| 4 | `/home/qiyuan/Current/MLML/contrib/Semantic_Embedding/Tools/pide_state.ML:647` (`Resources.begin_theory master_dir header parents`) | the name **as written in the edited file's own header**, unqualified | **YES, but narrowly** — see §1.3 |
| 5 | `/home/qiyuan/Current/MLML/contrib/AutoCorrode/ir/ir.ML:400` and `:598` (`Theory.begin_theory (id, Position.none) …`) | `id`, a caller-supplied REPL identifier | Only if a caller picks an id equal to a loaded theory's long name. Not defended against anywhere. |
| 6 | `/home/qiyuan/Current/MLML/contrib/AutoCorrode/ir/ir.ML:753` (`Thy_Info.use_theories opts "" [(name, …)]`) | qualifier `""`, so the name is used literally | **YES** if the caller passes a qualified name that the session provides |
| 7 | `/home/qiyuan/Current/MLML/contrib/Isabelle_RPC/test/Test_Universal_Key.thy:29`, `:65`; `/home/qiyuan/Current/MLML/contrib/Isabelle_RPC/test/Test_Cache_Scope.thy:25`; `/home/qiyuan/Current/MLML/contrib/Performant_Isabelle_ML/Test/Theory_Data_With_Constructor_Test.thy:44` | test-chosen names (`UK_Test_A2.Bar` etc.) | No — deliberately fresh names |

Pure's own callers, for completeness:
`/home/qiyuan/Current/MLML/contrib/Isabelle2025-2/src/Pure/Build/resources.ML:239`
(`Resources.begin_theory`, the shared entry point),
`/home/qiyuan/Current/MLML/contrib/Isabelle2025-2/src/Pure/Thy/thy_info.ML:283`
(`init ()` inside `eval_thy`, the loader's own call), and
`/home/qiyuan/Current/MLML/contrib/Isabelle2025-2/src/Pure/PIDE/document.ML:637` and `:651`
(the PIDE document model).

### 1.1 Why route #1's name can be a loaded theory's long name

`/home/qiyuan/Current/MLML/contrib/Isa-REPL/library/REPL.ML:422`:

```
fun qualify_name {name,imports,keywords} =
      {name=apfst (Long_Name.qualify thy_qualifier) name, imports=imports, keywords=keywords}
```

`thy_qualifier` comes from `/home/qiyuan/Current/MLML/contrib/Isa-REPL/library/Server.ML:360-364`:

```
val thy_qualifier = if thy_qualifier = ""
                    then if default_session = "Main"
                         then "HOL"
                         else default_session
                    else thy_qualifier
```

with `default_session = getenv "REPL_DEFAULT_SESSION"` (`Server.ML:275`). So the default
qualifier is either the literal string `HOL` or the name of the session whose heap the REPL
is running on — in both cases a qualifier under which real theories exist. The client can
also set it outright (`\005qualifier`, `Server.ML:508-511`; `\005path`, `Server.ML:701`;
`Server.ML:635`). A client that submits a theory whose header says `theory List` to a REPL
with qualifier `HOL` therefore begins a theory whose long name is exactly `HOL.List`.

Two further facts make this not merely possible but *anticipated*:

- `Resources.begin_theory` (`resources.ML:239-247`) performs **no** uniqueness check of any
  kind, and neither does `Theory.begin_theory` (`theory.ML:189-205`) nor
  `Context.begin_thy` (`context.ML:535-550`). The only guard in the whole chain is
  `context.ML:536-537`: name must be non-empty, imports must be non-empty.
- The REPL registers the finished theory at
  `/home/qiyuan/Current/MLML/contrib/Isa-REPL/library/REPL.ML:686-690` and **explicitly
  swallows the collision signal**:

  ```
  ; (Thy_Info.register_thy thy
     handle err as Exn.ERROR msg => (
       if String.isPrefix "Cannot update finished theory" msg
       then ()
       else Exn.reraise err ))
  ```

  That error is raised by `Thy_Info.remove` (`thy_info.ML:186`) for precisely the case "a
  theory of this long name already exists and is finished". The REPL continues with the
  shadow theory in hand.

### 1.2 Why route #3 is open too — and this is the bigger hole

I had been told the loader route is closed because `load_thy` calls `remove_thy` first
(`thy_info.ML:372`) and `remove` errors for a base-session theory (`thy_info.ML:183-192`).
Read `remove` again:

```
fun remove name thys =
  (case lookup thys name of
    NONE => thys
  | SOME (NONE, _) => error ("Cannot update finished theory " ^ quote name)
  | SOME _ => … actually delete …);
```

The error fires only for a name **that `Thy_Info`'s graph holds** and holds as finished
(`(NONE, _)`; `Thy_Info.finish ()` at `thy_info.ML:488` is what stamps every entry that way
when a heap is sealed). A name that is in `Resources`' `loaded_theories` set but **absent
from `Thy_Info`'s graph** takes the first branch, `NONE => thys`, and the load proceeds
normally — while `Theory_Hash.hash_of` still takes its persistent branch, because that
branch is chosen by `Resources.loaded_theory` alone.

Those two sets are not the same set, and I measured a case where they differ. Under an
Isabelle2025-2 batch build, the session's own theories are in `loaded_theories` from the
first instant (the session base lists everything the session *provides*), but they are never
put into `Thy_Info` — the 2025-2 batch build runs through the PIDE document model, and
`Thy_Info.register_thy` has exactly one call site in the whole of Pure
(`thy_info.ML:473`), which that path does not use. Measured inside a build:

```
[0] Resources.loaded_theory UK_Probe_C.Aux_Thy = true
[0] Resources.loaded_theory UK_Probe_C.UK_Probe_C = true
[0b] Thy_Info names matching Probe/Aux:            <- empty
[0c] lookup_theory MISS
```

So during a build, every theory of the session being built is freely (re)loadable by
`Thy_Info.use_theories`, from whatever the file on disk says at that moment, and each load
produces a *persistent* hash. That is route #3, and §2.2 shows it moving a hash for real.

For a long-lived REPL sitting on an already-built heap the picture is different: every
theory of that heap **is** in `Thy_Info` and **is** finished, so route #3 is closed there and
route #1 is the live one.

### 1.3 Why route #4 is narrow but not empty

`build_reeval_cache` (`pide_state.ML:647`) takes the name from `Thy_Header.read text_pos
text`, i.e. the name written in the file being edited, with no qualification. For
`HOL/List.thy` that is `List`, and `Resources.loaded_theory "List"` is false, so this route
normally produces a WIP theory and is harmless. It stops being harmless for **global**
theories, whose long name has no qualifier. Measured:

```
[G] loaded_theory Main = true
[G] loaded_theory HOL.Main = false
[G] loaded_theory Pure = true
[G] loaded_theory Complex_Main = true
[G] loaded_theory List = false
[G] global_theory "Main" = HOL
```

So a file whose header reads `theory Main` (or `Pure`, `Complex_Main`, or any AFP global
theory) re-begun by `build_reeval_cache` lands on the persistent branch under a name the
session already provides.

### 1.4 A third block that also turns out not to be one

I was told `Resources.loaded_theory` reads a set fixed at session start, so a theory's
persistent/WIP classification never changes mid-process. It is not fixed.
`Resources.init_session` is exported (`resources.ML:10`, and `init_session_yxml` at `:18`),
and its body is a `Synchronized.change` that **replaces** the whole record
(`resources.ML:115-128`). Pure itself re-enters it from the protocol command
`Prover.init_session` (`Pure/PIDE/protocol.ML:27-28`) and from `build.ML:72`. Measured:

```
[F1] loaded_theory "Zzz.Nonexistent" = false
[F1] loaded_theory "HOL.List" = true
[F2] after Resources.init_session: loaded_theory "Zzz.Nonexistent" = true
[F2] after Resources.init_session: loaded_theory "HOL.List" = false
```

`HOL.List` flipped from persistent to WIP mid-process. Nothing in this repository calls
`Resources.init_session`, so this is not a live route today; it is a standing hazard, and it
means "the classification cannot change" must not be used as a load-bearing argument.

---

## 2. Dynamic probe

Everything below ran against already-built heaps. No `isabelle build -c` was used; no file
in the repository was created, edited, or deleted. Scratch sessions live entirely under the
scratchpad directory.

### 2.0 A note on `hash_of` and the Python host

`Theory_Hash.hash_of`'s persistent branch RPCs to Python. Under bare
`isabelle ML_process` it cannot run:

```
[HASH thy2(fake HOL.List)] FAILED: exception Fail raised
  (line 83 of "System/isabelle_system.ML"): Bad bash_process server address
```

The ephemeral attached host needs Isabelle's `bash_process` server, which only exists under
`isabelle build` / PIDE. So the hash-producing probes were run as one-theory scratch
sessions under `isabelle build` instead, where the host launches and the real digest comes
back. (`ML_process` was still used for the parts that need no hash: §1.3, §1.4, and the
`register_thy` / `use_theories` behaviour in §2.1.)

Because messages written by `writeln` during a batch build are not echoed to the console,
each probe appends its own lines to a file under the scratchpad; those files are the
"output" quoted here.

### 2.1 Constructing a second theory value under a loaded long name

Source: `/tmp/claude-1002/-home-qiyuan-Current-MLML/a32a489c-01df-4539-89b3-c3bd40f94354/scratchpad/probe1.ML`
Run: `isabelle ML_process -l Isa_REPL -d contrib -f …/probe1.ML`

Output (elided where uninteresting):

```
[0] Resources.loaded_theory "HOL.List" = true
[thy1] long=HOL.List id=255690 loaded_theory=true
      hashed file = …/contrib/Isabelle2025-2/src/HOL/List.thy exists=true bytes=339172
                    sha1=0d8201759714e93c3f0063f9eb024804d0178d24
      parents = HOL.Sledgehammer, HOL.Lifting_Set
[A] Resources.begin_theory SUCCEEDED under long name HOL.List
[thy2] long=HOL.List id=466970 loaded_theory=true
      hashed file = …/scratchpad/fakedir/List.thy exists=true bytes=100
                    sha1=ffaeb37dd1dfd2b852bebaefb3bf658bd01361aa
      parents = Pure
[B] Theory.begin_theory SUCCEEDED under long name HOL.List
[C] thy1 vs thy2 hashed-file identical? false
[D] register_thy thy2 raised ERROR: Cannot update finished theory "HOL.List"
[D] Thy_Info.get_theory "HOL.List" id is now 255690 (thy1 id = 255690)
[E] use_theories HOL.List SUCCEEDED
```

Reading this:

- Two theory values, distinct identifiers (255690 vs 466970), the **same** long name
  `HOL.List`, and `Resources.loaded_theory` true for both — so both go down `hash_of`'s
  persistent branch.
- The file each one would hash is different: the real 339 KB `HOL/List.thy` versus a 100-byte
  file I put in the scratchpad. `Theory_Hash.get_theory_path` derives it from
  `Resources.master_directory`, which `Resources.begin_theory` sets from its first argument
  (`resources.ML:243`).
- `Thy_Info.register_thy` is the only thing that objects, and the registry keeps pointing at
  the original. The shadow theory simply exists alongside it.
- `[E]` is a no-op, not a reload: `require_thy` computes `current` by comparing the master
  file's SHA1 against the recorded one (`thy_info.ML:404-410`), the file was untouched, so
  the task became `Finished (get_theory …)` with no `remove_thy` at all. This is the
  measurement that could most easily be misread as "the loader lets you reload HOL.List".
  It does not; §2.2 is the case where it genuinely does.

### 2.2 Two persistent hashes for one long name — route #1

Sources:
`/tmp/claude-1002/-home-qiyuan-Current-MLML/a32a489c-01df-4539-89b3-c3bd40f94354/scratchpad/UK_Probe/Probe_Common.ML`
plus the two one-line drivers `…/UK_Probe/A/UK_Probe_A.thy` (`order = "fake_first"`) and
`…/UK_Probe/B/UK_Probe_B.thy` (`order = "real_first"`), session roots in
`…/UK_Probe/ROOT`, both children of the built `Isa_REPL` heap.

Run: `isabelle build -d contrib -d …/UK_Probe -o threads=1 UK_Probe_A UK_Probe_B`

Here the shadow theory is parented on the *real* `HOL.List` so that `List.rev` is in scope,
and the two sessions differ only in which context asks for the key first.

```
########## fake_first
[thy1] long=HOL.List id=255690 loaded_theory=true master_dir=$ISABELLE_HOME/src/HOL
[thy2] long=HOL.List id=467093 loaded_theory=true master_dir=…/scratchpad/fakedir
[HASH thy1 real] 2ec6c541898e932a3ad4d0c37773e9f3
[HASH thy2 fake] 408e07a30bcc5dd387fbc870590b9946
[VERDICT hash] two hashes for long name HOL.List differ = true
[ORDER] fake_first
[UK 1st via FAKE thy2] key=408e07a30bcc5dd387fbc870590b9946014c6973742e726576
        theory-hash part = 408e07a30bcc5dd387fbc870590b9946  matches-real=false  matches-fake=true
[UK 2nd via REAL thy1] key=408e07a30bcc5dd387fbc870590b9946014c6973742e726576
        theory-hash part = 408e07a30bcc5dd387fbc870590b9946  matches-real=false  matches-fake=true
[UK] first = second ? true

########## real_first
… identical setup …
[ORDER] real_first
[UK 1st via REAL thy1] key=2ec6c541898e932a3ad4d0c37773e9f3014c6973742e726576
        theory-hash part = 2ec6c541898e932a3ad4d0c37773e9f3  matches-real=true  matches-fake=false
[UK 2nd via FAKE thy2] key=2ec6c541898e932a3ad4d0c37773e9f3014c6973742e726576
        theory-hash part = 2ec6c541898e932a3ad4d0c37773e9f3  matches-real=true  matches-fake=false
[UK] first = second ? true
```

The key layout is `theory hash (16 bytes) ++ tag byte ++ entity digest`; the tag `01` and the
trailing `4c6973742e726576` = `List.rev` are the same in both runs. Only the leading 16
bytes move, and they move **with the order of the two calls**. That is
`Universal_Key.cache` (`Universal_Key.ML:362`), keyed by
`(entity, theory long name)` = `(Constant "List.rev", "HOL.List")` in both runs, memoising
whichever theory value happened to be resolved first. `key_of_ns_entity`
(`Universal_Key.ML:767`) is its only caller, so this is the answer every name-addressed key
gets for the remaining life of the process.

Note where the resolution goes wrong: `key_of_ns_entity` calls
`resolve_theory context thy_long_name`, and `Theory_Hash.resolve_theory` short-circuits when
the requested name equals the context theory's own name — so from the shadow theory's
context it hands back the shadow theory, never consulting `Thy_Info`.

### 2.3 The loader moving a hash, and the constituents cache going stale — route #3

Source: `/tmp/claude-1002/-home-qiyuan-Current-MLML/a32a489c-01df-4539-89b3-c3bd40f94354/scratchpad/UK_Probe/C/UK_Probe_C.thy`
with `…/UK_Probe/C/Aux_Thy.thy`; session `UK_Probe_C` declares both theories, so both names
are in `loaded_theories`.

Run: `isabelle build -d contrib -d …/UK_Probe -o threads=1 UK_Probe_C`

The probe: hash `UK_Probe_C.Aux_Thy`; compute and cache the constituents of `aux_c_def` (a
theorem about a constant that `Aux_Thy` defines); **append one comment line to
`Aux_Thy.thy` on disk**; ask `Thy_Info.use_theories` to load it again; re-hash; re-ask for
the constituents both through the cache and with the cache bypassed.

```
[0] Resources.loaded_theory UK_Probe_C.Aux_Thy = true
[0] Resources.loaded_theory UK_Probe_C.UK_Probe_C = true
[0b] Thy_Info names matching Probe/Aux:
[0c] lookup_theory MISS; using ^theory ancestor
[1] hash of UK_Probe_C.Aux_Thy (v1) = 3442b5d18c3ca3897a2453a7dab87178
[1] theory id v1 = 467010
[2] cached constituents XOR = e0926c3007058948659018b41e8be911
    constituents = HOL.HOL, HOL.Nat, Pure, UK_Probe_C.Aux_Thy
[3] Aux_Thy.thy edited on disk
[3] use_theories returned = OK
[4] theory id v2 = 467251
[4] hash of UK_Probe_C.Aux_Thy (v2) = 20e0660f4c885bd2c92e731aa048fbf9
[VERDICT loader] hash moved within one process = true
[5] constituents XOR via cache after reload = e0926c3007058948659018b41e8be911
[5] constituents XOR recomputed (cache bypassed) = f430bfeec7b17113d69a3809647b6390
[VERDICT constituents] cached entry is now stale = true
```

No bypass anywhere in this one. `Thy_Info.use_theories` — the ordinary loader — accepted the
reload, because `remove` found no entry to refuse (`[0b]`/`[0c]`). Both hashes are
persistent. And the constituents cache, whose entry is keyed by
`Term_Digest.thm128 thm` and whose value carries the XOR of the constituent theories'
hashes (`Universal_Key.ML:605`, populated at `:706-728`), keeps answering with the XOR that
embeds `Aux_Thy`'s **pre-edit** hash `3442…`, while a fresh `compute_constituents` on the
identical proposition now yields `f430…`.

This is exactly the failure the question describes: the proposition's own text did not
change, so its cache key did not change, so its universal key does not move — even though a
constituent theory's content did change and the XOR scheme is supposed to make it move.

---

## 3. Reproducible recipes, and what each one damages

### Recipe A — shadow theory under a loaded long name (works on any process, including a REPL on a sealed heap)

1. Have a directory `D` containing a file `X.thy` whose content is *not* the distribution's
   `X.thy`.
2. `Resources.begin_theory D {name = ("Q.X", pos), imports = …, keywords = …} parents`
   where `Q.X` is a long name in `loaded_theories` (e.g. `HOL.List`). No error.
   Via the real caller: submit a theory whose header says `theory X` to an Isa-REPL whose
   `thy_qualifier` is `Q` — `REPL.ML:422` qualifies it and `REPL.ML:442` begins it. The
   `Thy_Info.register_thy` complaint that follows is swallowed at `REPL.ML:686-690`.
3. Ask for the universal key of any namespace entity whose defining theory's long name is
   `Q.X` while that shadow theory is the context theory.

**Poisons `Universal_Key.cache` (`Universal_Key.ML:362`).** The cache key
`(entity, "Q.X")` carries no hash, so the first answer wins forever. Measured in §2.2:
the same `(Constant "List.rev", "HOL.List")` request returns `408e…` or `2ec6…`
depending only on call order.

**How the damage shows.** Every name-addressed key for that theory's entities — the whole
`key_of_ns_entity` family: constants, types, classes, locales, theorem collections, methods
— is silently minted against the wrong theory content for the rest of the process. Records
written under those keys land next to, and are indistinguishable from, records for the real
theory's entities; lookups of the real entities miss, or worse, hit a shadow record. Nothing
raises, nothing warns.

*Unverified corollary, flagged as such.* The cache-scope fork mechanism
(`claim_cache_scope`, `Universal_Key.ML:657-699`) decides whether to fork the constituents
cache by comparing theory **base** name to theory **long** name across the beginning
theory's cone. The shadow theory contributes `("X", "Q.X")`, which matches the claim the
real theory already made, so no collision is detected and **the shadow theory shares the
real theory's constituents cache**. If the shadow theory declares constants whose internal
names collide with the real theory's (which is the normal case — `Sign.init_naming` gives
them the same `X.` prefix), `Term_Digest.thm128` gives colliding digests over a population
the fork mechanism was built to keep separated. I did not measure this; it follows from
reading `claim_cache_scope` against the §2.2 result, and it is the piece I would test next.

### Recipe B — loader reload of a session-provided theory that `Thy_Info` does not hold

1. Be in a process where some long name `Q.X` satisfies `Resources.loaded_theory "Q.X"` and
   `Thy_Info.lookup_theory "Q.X" = NONE`. Under Isabelle2025-2 this is **every theory of the
   session currently being built**, for the whole duration of that build.
2. Load it: `Thy_Info.use_theories opts "Q" [("X", pos)]`. Succeeds.
3. Change `X.thy` on disk. (In the real world: another agent's edit, a generator writing the
   file, a `git` operation — the process need not have caused it.)
4. Load it again. `require_thy` sees the master SHA1 changed, so `current` is false, so
   `load_thy` runs; `remove_thy` finds nothing to refuse; a second theory value appears under
   `Q.X` with a different persistent hash.

**Poisons the constituents cache (`Universal_Key.ML:605`)** — measured in §2.3: an entry
computed in step 2 still reports the pre-edit XOR after step 4.
**And `Universal_Key.cache`**, by the same argument as Recipe A: any
`(entity, "Q.X")` key minted before step 4 keeps the pre-edit hash. (Mechanism identical to
the measured §2.2 case; I measured the constituents half here rather than both.)

**How the damage shows.** A theorem whose statement never changed keeps a universal key that
should have moved when its constituent theory was edited. That is precisely the automatic
invalidation the XOR scheme exists to provide, silently not happening: downstream records
keyed by that theorem look current, and a consumer deciding "has this gone stale?" by
comparing keys gets "no".

### Not a recipe: names Thy_Info holds as finished

For a name that `Thy_Info` holds and has finished — every theory baked into a heap image —
`remove` does refuse, measured:

```
[D] register_thy thy2 raised ERROR: Cannot update finished theory "HOL.List"
[D] Thy_Info.get_theory "HOL.List" id is now 255690 (thy1 id = 255690)
```

So the loader genuinely cannot replace a heap theory, and the registry genuinely keeps
pointing at the original. That closure is real. It is just much narrower than "the loader
route is closed": it covers only the intersection of `loaded_theories` with `Thy_Info`'s
finished entries, and Recipe A steps around it entirely while Recipe B lives in the gap.

---

## 4. Files

Probe sources, all under
`/tmp/claude-1002/-home-qiyuan-Current-MLML/a32a489c-01df-4539-89b3-c3bd40f94354/scratchpad/`:

- `probe1.ML` — §2.1, run under `isabelle ML_process -l Isa_REPL -d contrib`
- `probe2.ML` + `probe2_inner.ML` — the attempt to reach `Theory_Hash` from bare
  `ML_process`; kept because its failure is the evidence for §2.0
- `probe3.ML` — §1.4, `Resources.init_session` mutability
- `probe4.ML` — §1.3, global theory names in `loaded_theories`
- `UK_Probe/Probe_Common.ML`, `UK_Probe/A/UK_Probe_A.thy`, `UK_Probe/B/UK_Probe_B.thy`,
  `UK_Probe/ROOT` — §2.2; outputs in `out_fake_first.txt`, `out_real_first.txt`
- `UK_Probe/C/UK_Probe_C.thy`, `UK_Probe/C/Aux_Thy.thy` — §2.3; output in `out_loader.txt`
- `fakedir/List.thy` — the 100-byte stand-in for `HOL/List.thy`
