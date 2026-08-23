# `query_by_name` must render live, and `??.` entities must not be listed

Handoff for a dedicated session. Written 2026-08-20 from a review session that
found these two defects while investigating something else. Nothing has been
changed yet — this document is reconnaissance only.

## The two requirements (both from the user, 2026-08-20)

1. **The by-name query path prints strings stored in the semantic database
   instead of rendering against the context live at query time.** Both the
   entity **name** and its **statement/type** must be re-rendered.
2. **Any entity whose externed name begins with `??.` must be dropped from
   result listings, not shown.** `??.` is what `Name_Space.extern` returns when
   no access path resolves — i.e. the agent cannot cite the entity by that name
   at all.

## Background: how the *search* path already does it right

`Name_Space.extern` walks an entity's access paths shortest-first and, when the
option `names_unique` is set, accepts a path only if it resolves uniquely;
otherwise it falls through to a longer path, and if none qualifies it returns
`Long_Name.hidden name`, i.e. `"??." ^ name`.

`names_unique` defaults to `true` (`contrib/Isabelle2025-2/etc/options:84`) and
nothing in `Isa-Mini/`, `Semantic_Embedding/` or `Isabelle_RPC/` overrides it
(grepped for `names_unique` / `names_short` / `names_long`: no hits).

So on the search path the three parts of a result line come from three places:

| part | source | |
| --- | --- | --- |
| entity name | `Name_Space.extern` / `Facts.extern` against the **live** proof context | rendered live |
| statement / type | `Syntax.string_of_term` / `string_of_typ` against the **live** context | rendered live |
| English explanation | the string written at interpretation time | from the record |

Renderer: `contrib/Isa-Mini/IsaMini/AoA/retrieval.py:243-266`
(`_format_fetched_entity`). It consumes a `RetrievedEntity` produced by one ML
round-trip.

ML side: `contrib/Isa-Mini/Agent/agent_server.ML:890-1006`, the
`IsaMini.retrieve_entity` callback. It opens with

```sml
val s0   = get_state state_id
val ctxt = Minilang.context_of s0            (* :900-901 — the LIVE proof context *)
val SOT  = MiniLang_Agent.string_of_term ctxt   (* :902 *)
val SOTy = MiniLang_Agent.string_of_type ctxt   (* :903 *)
```

and then per kind: theorems use `Facts.extern ctxt facts full_name` (`:932`) and
`SOT o Thm.prop_of` (`:942`); constants use
`Name_Space.extern ctxt const_space (Consts.intern consts name)` (`:964-966`)
and `SOTy (Consts.the_constraint consts cname)` (`:967, :970`); types, classes
and locales use `Name_Space.extern` on their own spaces (`:980-985`).

Its argument schema is `(state_id, [(kind, name)])` — **it is keyed on a
Minilang state id**, from which it derives the proof context.

Evidence it works: `tools/aoa_putnam_eval/state/logs/ee54724c2_2/interaction.yaml:129`
shows `Rat.Rats_sum` rendered qualified, because `Rats_sum` is declared twice —
`contrib/Isabelle2025-2/src/HOL/Rat.thy:881` and
`contrib/afp-2026-05-13/thys/Bernoulli/Bernoulli.thy:42` — and both were in
scope. `Name_Space.extern` refused the ambiguous bare path.

## Defect 1: the by-name path

`contrib/Isa-Mini/IsaMini/AoA/retrieval.py:913-949`, `_query_entity_core`:

```python
uk, live_name = await universal_key_and_name_of(connection, tag, name, ctxt=ctxt)
...
rec = Semantic_DB[uk]
if rec is not None:
    rec = apply_live_name_if_member(rec, live_name)
_format_record(buf,
               f"{rec.kind.label} {rec.name}" if rec is not None else f"{tag.label} {name}",
               rec)
```

and `_format_record` (`:954-970`):

```python
buf.write(f"{heading}:")
print_paragraph(2, buf, trunc_expr(rec.expr) if rec.expr else "")
if rec.interpretation:
    buf.write(rec.interpretation)
```

So the heading carries `rec.name` (stored) and the body carries `rec.expr`
(stored). No `extern`, no `Syntax.string_of_term`.

`apply_live_name_if_member`
(`contrib/Semantic_Embedding/Isabelle_Semantic_Embedding/semantics.py:1318-1332`)
substitutes the live name **only** when `rec.from_collection is not None` and
the live name carries a `(digits)` index. The comment at `retrieval.py:919-923`
says this is deliberate — it cites `DYNAMIC_MEMBER_NAMING_PLAN.md §2.1`. **Read
that plan before changing this**: the restraint was reasoned, and the reasoning
must be answered rather than ignored.

**Important nuance on how bad each half is.**
`universal_key_and_name_of` (`contrib/Isabelle_RPC/Isabelle_RPC_Host/universal_key.py:182-203`)
returns the **internal** fully-qualified name (it interns; it does not extern).
So:

- The **name** half is not a mis-citation risk — a fully qualified internal name
  does resolve. It is the wrong *form*: not the shortest citable name, and not
  a reflection of what is in scope now.
- The **statement** half is the real staleness. `rec.expr` was pretty-printed at
  interpretation time, in a different theory context, with whatever notation and
  abbreviations were in scope then. It can differ from what the agent would see
  and write today.

### The obstacle, and why the two callers differ

`_query_entity_core` has two callers, and they are not in the same position:

- **`contrib/Isa-Mini/IsaMini/AoA/retrieval.py:1002`** — the `Head <const>` line
  of an `exact_term` query. It passes `ctxt=ml_state.name`, which **is a
  Minilang state id**. This caller can already reach `IsaMini.retrieve_entity`
  with no new mechanism.
- **`contrib/Isa-Mini/IsaMini/AoA/toplevel.py:65-73`** — the RPC
  `IsaMini.query_by_name`. It passes **no** `ctxt`, and the ML command that
  invokes it (`contrib/Isa-Mini/Agent/agent_server.ML:2136-2148`, declared at
  `:131`) installs exactly one callback:

  ```sml
  val su = Context_Callbacks.static_context_unpacker context
  val cmd = { name = "IsaMini.query_by_name",
              arg_schema = packPair (Universal_Key.pack_entity_kind', packString),
              ret_schema = unpackPair (unpackString, unpackBool),
              callback = [Universal_Key.make_universal_key_callback su],
              timeout = NONE }
  ```

  There is **no Minilang state id and no rendering callback** here. There is a
  `Context.generic`, which is what `retrieve_entity` ultimately needs — but
  `retrieve_entity` takes a state id and derives the context itself.

So the fix has a real design step: either give this RPC a rendering callback
keyed on the `Context.generic` it already holds, or render on the ML side before
returning. Whichever is chosen, **`agent_server.ML:890-1006` already contains
the per-kind rendering logic and must be reused, not re-written** — factor out a
context-taking core and let both `retrieve_entity` and this path call it.

### A third by-name path, not yet examined

`contrib/Semantic_Embedding/Isabelle_Semantic_Embedding/semantics.py:1530-1550`,
`query_by_name_raw`, feeding `mk_query_by_name_tool` (`:1620`), used by the
**interpretation agent** (`semantic_interpretation.py:1165`). It calls
`Semantic_DB.query(uk, with_pretty=..., live_name=live_name)`. Whether that
renders or prints stored strings was not determined. Check it; the same
requirement plausibly applies, but the interpretation agent's context is the
theory being interpreted, not a proof state, so the answer may differ.

## Defect 2: `??.` entities are listed

`??.` reaches the agent verbatim today. Evidence:
`tools/aoa_putnam_eval/state/logs/ee54fd60c_3/interaction.yaml:14232`

```
- narrowing_type.exhaust: (∀(x :: ??.Quickcheck_Narrowing.narrowing_type list list). ?y = Narrowing_sum_of_products x ⟶ ?P) ⟶ ?P
```

Note this instance is `??.` **inside a rendered statement**, not the entity's own
name. Those are two different situations and the fix may need to treat them
differently:

- **(a) the entity's own name externs to `??.`** — the agent cannot cite it at
  all. The user's instruction covers this: drop it from the listing.
- **(b) a constant or type mentioned inside the statement externs to `??.`** —
  the entity itself may be perfectly citable while its statement refers to
  something not accessible here. **RULED OUT by the user, 2026-08-20: do not
  implement (b).** Only an entity whose own name is `??.` is dropped; a `??.`
  appearing inside a rendered statement is left alone.

### What already exists, and where the gap is

A `"??."` test is applied at **interpretation** time for some kinds:

- theorems — `contrib/Semantic_Embedding/Tools/infra_filter.ML:440`,
  `orelse String.isPrefix "??." (Facts.extern ctxt facts full_name)`, wired in as
  the theorem callback's `filter_opt` at
  `contrib/Semantic_Embedding/Tools/semantic_store.ML:1386`
- methods — `infra_filter.ML:476`
- dynamic fact collections — `infra_filter.ML:520`, applied live per query via
  `semantic_store.ML:1392-1393`

The gaps:

- **Constants, types, classes and locales have no `"??."` test at all.**
  `ns_filter` (`contrib/Isabelle_RPC/Tools/context.ML:1016-1050`) drops
  `#concealed` entries and `Long_Name.is_hidden (Name_Space.intern space name)`
  (`:1023-1024`) and applies the `is_infra_*` predicates — but never checks the
  externed form.
- **The cached theorem pass does not re-apply `filter_opt`.** In
  `make_thm_like_callback` (`context.ML:1244-1332`) the live-delta fold applies
  it (`:1291-1292`) while the cached fold (`:1303-1327`) applies only
  `scope_ok`, `name_filter`, `prop_matches`, `target_type_filter` and the
  stale-dynamic-member drop. This is deliberate and documented at
  `semantic_store.ML:1290-1298`. The cached entries were filtered when
  `update_thm_cache` (`semantic_store.ML:2316-2353`) ran them, at
  `Theory.at_begin`/`Theory.at_end` in `Context.Theory thy` — **the theory
  context at load time, not the proof context at query time.**
- **Nothing on the display path strips or warns.** The only `.replace("??.", "")`
  in AoA is `model.py:2539`, and it applies to `raw_display` from
  `unfold_syntax`, not to result lines.

So the natural home for requirement 2 is the **query-time** path, which is
exactly where the test is missing.

## Constraints for whoever does this

From `CLAUDE.md`, and they are absolute:

- **Never run `isabelle build`** without the user's explicit command, in any
  session, with any flags. Starting the REPL server (`repl_server.sh`) is the
  exception.
- After editing any `.ML`, **just restart the REPL server** — a fresh REPL loads
  `.ML` from source. Do not rebuild a heap, do not chase heap timestamps.
- **Never** `git stash`, `git checkout`, `git reset --hard`, and **never**
  `git clean` in any form. Shared working tree.
- Commit directly on `main`; never branch.
- **Never probe the Isa-REPL port (6666) with a bare TCP connect** — it kills the
  server. Use `ss` / `fuser` / `lsof`.
- Ask rather than assume, on anything ambiguous.
- Reuse code; do not copy-paste-and-modify. `agent_server.ML:890-1006` is the
  thing to factor, not to duplicate.
- Production code editing is unblocked as of 2026-08-20 (the earlier
  "migration code only" restriction was lifted).

## The decided design (all approved by the user, 2026-08-20)

### Requirement 2 — where the `??.` drop goes, and why not the candidate fold

**Decided: at the display step, not in the candidate fold.** Measured, not argued.

The candidate fold is `contrib/Isabelle_RPC/Tools/context.ML:1303-1327`, the
CACHED pass of `make_thm_like_callback`. It runs once per semantic query and
walks the **entire** cached list with no early exit, because the Python caller
passes no `limit` (`Isabelle_RPC_Host/context.py:396` defaults `-1`), so
`context.ML:1304`'s `remaining = 0` short-circuit never fires. On a query with no
term pattern, name filter or target type, all three of `mk_prop_pattern_matcher`
(`:909`), `mk_target_type_filter` (`:956`) and `mk_name_filter` (`:997`) degrade
to `K true`, so essentially every cached entry becomes a candidate.

Measured in `MathBench_ProverBase` (98,632 static fact names, 111,276 theorems;
Intel Ultra 7 165U, single-threaded):

| | n | per call | total |
| --- | ---: | ---: | ---: |
| `Facts.extern`, cold first sweep | 98,632 | 4.27 us | 0.421 s |
| `Facts.extern`, runs 2-7 (warm) | 98,632 | 3.37-4.06 us (median 3.99) | 0.332-0.401 s |
| same fold with `extern` removed | 98,632 | 0.006 us | 0.0006 s |
| the cached fold's current per-entry work | 98,474 | **0.75 us** | 0.073 s |
| `Name_Space.extern` on constants | 12,519 | 4.26 us | 0.054 s |

**There is no warm-up amortisation** — the cold sweep (4.27 us) sits inside the
warm spread (3.37-4.06), so every query would pay in full, every time. Adding the
check makes the fold **~5.3x more expensive per entry**; the 0.75 us baseline was
measured with Pure's `Symtab` standing in for the real `Bytehashtab`
(`Performant_Isabelle_ML` is absent from that heap), so it is an upper bound and
the true ratio is higher. Extrapolated to 200,000 candidates: **~0.8 s of pure
CPU added to every semantic query.**

What that would buy: **373 of 98,632 fact names (0.378%)** extern to `??.`
(identical count on all seven repeats); constants 125/12,519 (1.00%); types
4/367. Over 99.6% of the work is confirming a name was already fine.

The display step costs **nothing extra**: `IsaMini.retrieve_entity` already calls
`Facts.extern` at `agent_server.ML:932`, on the ranked shortlist only
(`model.py:2354` takes `scored_recs[:k]`, then `:2363` retrieves).

**Withdrawn:** two earlier proposals in this thread — putting the check in the
cached fold, and unifying both passes' accessibility check on the per-query
context — both rested on a wrong cost assumption (that the expensive filters
would have cut the candidate list to a few dozen first). Neither is worth
reviving.

**Also recorded, not needed:** `Name_Space.intern space name = name` is the cheap
equivalent of "does this name extern without `??.`" — one `intern_chunks` table
lookup instead of `extern`'s loop over access paths (`name_space.ML:275-320`).
Useless for this design, since the display step is already free. Kept only in
case some future consumer needs an accessibility test where no `extern` is
already running.

### The implementation, in `contrib/Isa-Mini/IsaMini/AoA/model.py` — DONE

Written 2026-08-23 in `semantic_knn_counted`. Five edits plus one guard:

- `k_fetch = max(k + 1, int(k * 1.15))`, computed once, used at all **three**
  truncation sites — `store.lookup(query, k_fetch, …)` (vector branch),
  `entries[:k_fetch]` (pattern-only branch), `scored_recs[:k_fetch]` (the
  experience merge). The `exact_name` branch has no truncation and gets none.
- `_retrieve_entity` → `_retrieve_entity_with_diagnostics`, so the per-entity
  diagnostic is available; `info_by_idx` is unchanged.
- The drop: `info[0].unicode.startswith("??.")` or `info is None`. **On every
  path, `exact_name` included** (ruled 2026-08-23) — a name the agent cannot
  write is useless however it was asked for.
- `EXPERIENCE` records are untouched: `ent_idx` already excludes them, they never
  reach `retrieve_entity`, and they can never carry `??.`.
- Dropped count and per-entity diagnostics go to `logging.getLogger(__name__)`,
  **not** into the agent's result text.
- **The cap is conditional and the drop is not.**
  `cap = k if exact_name is None else len(scored_recs)`. A first version capped
  unconditionally at `k`, which would have truncated an `exact_name` bundle
  expansion — that path never over-fetched and legitimately returns more than `k`
  members. That was a regression I introduced and removed.

### The original sketch, for reference

```
1. :2354  take  max(k + 1, int(k * 1.15))  instead of k
2. :2363  run _retrieve_entity on that batch, unchanged -- extern happens here
3.        drop:     short_name starting with "??."   AND   info is None
          do NOT touch: EXPERIENCE records -- :2360 already excludes them from
          ent_idx, they never go through retrieve_entity and can never be "??."
4.        trim to k; if short, return fewer -- no refetch loop
5.        log how many were dropped and their diagnostics (NOT into the agent's
          result text)
```

**Why proportional over-fetch, and why the `k + 1` floor.** `k` is agent-chosen
(`retrieval.py:80-84`, `_query_k` reads the query's `number`), default **15**,
capped at **50**; two internal call sites are fixed at **10**
(`model.py:3785`) and **40** (`model.py:3671`, `INITIAL_K = FINAL_K = 40`).
`int(k * 1.15)` gives +1 at k=10, +2 at k=15, +6 at k=40 — headroom that scales.
But it yields **zero** headroom for k <= 6, and k=1 is the case where losing one
entry loses everything, hence the floor. The margin is generous either way: 15%
over-fetch against a 0.378% hidden rate is a factor of forty.

**Why `info is None` is dropped too.** An entity `retrieve_entity` cannot resolve
is as uncitable as one that externs to `??.`. Today `model.py:2451-2456` still
lists it, using the record's stored full name with an empty statement. Dropping
it is the same standard applied consistently. **The cost is a lost signal** —
`None` has more than one cause (a `Facts.lookup` miss, a name absent from the
space, possibly symptoms of other defects), and silently dropping them would hide
that. `_retrieve_entity_with_diagnostics` (`:2406`) already returns a per-entity
diagnostic which `_retrieve_entity` (`:2438`) discards; the count and the
diagnostics go to the log so the symptom stays visible.

### Requirement 1 — live re-rendering on the by-name path

Unchanged from the analysis above: `_query_entity_core` must stop printing
`rec.name` and `rec.expr`. The design question is still the one in "The obstacle,
and why the two callers differ" — the `exact_term` caller already holds a
Minilang state id (`retrieval.py:1002` passes `ctxt=ml_state.name`) and can call
`IsaMini.retrieve_entity` today, while the RPC caller (`toplevel.py:65-73`,
invoked from `agent_server.ML:2136-2148`) holds only a `Context.generic` and has
no rendering callback. `agent_server.ML:890-1006` must be factored into a
context-taking core shared by both, not duplicated.

Note the severity is asymmetric: `universal_key_and_name_of`
(`universal_key.py:182-203`) returns the **internal** fully-qualified name, which
does resolve — so the name half is the wrong *form*, not a mis-citation risk.
`rec.expr` is the real staleness: it was pretty-printed at interpretation time in
a different theory context.

## Requirement 1 — live re-rendering: the design, settled 2026-08-23

### The essence

`IsaMini.retrieve_entity` is the ONE callback of thirteen that hard-codes "my
argument is a Minilang state id". The other twelve all take a **`context_unpacker`**
and let the caller decide where the context comes from. Make this one conform,
and the problem disappears — no shared helper, no duplicated callback record.

### What was discovered, and what it overturns

**`Agent_Server.query_by_name` has ZERO callers in ML.** Declared at
`agent_server.ML:131`, defined at `:2152`, and nothing in any `.thy` or `.ML`
invokes it — so the Python RPC `IsaMini.query_by_name` (`toplevel.py:65-73`)
never fires. That path is dead today. **The user ruled 2026-08-23 that it must
be fixed anyway.**

The live by-name caller is `retrieval.py:1002` — the `Head <const>` line of an
`exact_term` query — and it already passes `ctxt=ml_state.name`, a Minilang state
id. So the earlier diagnosis ("the obstacle is that the RPC caller has only a
`Context.generic`") described a real obstacle on a path nobody walks.

**A refactor was written and then reverted.** It extracted the ~100-line renderer
into a helper `retrieve_entities_in ctxt entities` and planned two callback
records over it. That is a bespoke solution to a problem this codebase already
solves generically, and it was reverted (`git diff` on `agent_server.ML` is
empty; backup at `scratchpad/agent_server.ML.bak`). **Do not re-derive it.**

### The mechanism, verified from source

`contrib/Isabelle_RPC/Tools/context.ML:4-6` states the pattern: every callback
generator takes a `context_unpacker`, a msgpack unpacker yielding a
`Context.generic`. Two implementations:

```sml
(* Tools/Universal_Key.ML:255-257 *)
fun static_context_unpacker (ctx: Context.generic) : context_unpacker =
  fn src => let val (_, src') = MessagePackBinIO.Unpack.unpackUnit src
            in (ctx, src') end

(* agent_server.ML:734-739 *)
val agent_context_unpacker : Context_Callbacks.context_unpacker =
  fn src => case unpackOption unpackString src of
              (NONE, src')     => (Context.Proof ctxt, src')
            | (SOME sid, src') => (Context.Proof (Minilang.context_of (get_state sid)), src')
```

Both consume exactly one msgpack value in the ctxt slot, and `None`/nil is legal
for both.

**The load-bearing fact that makes the search path zero-risk**
(`contrib/Performant_Isabelle_ML/contrib/mlmsgpack/mlmsgpack.sml:902-903`):

```sml
fun unpackOption u ins = (u >> SOME || unpackUnit >> (fn () => NONE)) ins
```

It tries `u` first. So a **plain** msgpack string still decodes to `SOME s`.
`model.py:2418` sends `(self.name, args)` with `self.name` a bare `str`; under
`agent_context_unpacker` that decodes to `SOME sid` → `get_state sid` → exactly
today's context. **The schema changes; the wire bytes and the behaviour of the
search path do not. Python needs no change there.**

### Which arg_schema changes, and which does not

Two different ones, in opposite directions — an earlier note conflated them:

| | changes? | why |
| --- | --- | --- |
| `IsaMini.retrieve_entity`'s arg_schema (**callback**, Python→ML) | **YES** | `unpackPair (unpackString, …)` → `unpackPair (ctxt_unpack, …)`. This *is* the mechanism. |
| its wire format for the existing caller | no | `unpackOption` accepts a bare string; Python keeps sending `self.name` |
| `IsaMini.query_by_name`'s arg_schema (**command**, ML→Python) | **NO** | `static_context_unpacker context` fixes the context at callback-construction time from the `context` that ML's `query_by_name` already receives. Decided 2026-08-23 not to extend it: the only reason would be letting one ML call pick a different context, and nothing needs that. |
| `query_by_name`'s callback list | add one entry | `make_retrieve_entity_callback su` |

### The four steps

**Step 1 — turn `retrieve_entity_callback` into a generator.**
Currently a `val` at `agent_server.ML:890`, whose `function` opens with:

```sml
        function = (fn (state_id, entities) =>
          let val s0 = get_state state_id
              val ctxt = Minilang.context_of s0
              val thy = Proof_Context.theory_of ctxt
```

Becomes `fun make_retrieve_entity_callback ctxt_unpack = { … }` with
`arg_schema = unpackPair (ctxt_unpack, unpackList (unpackPair
(Universal_Key.unpack_entity_kind, unpackString)))`, `ret_schema` unchanged, and

```sml
        function = (fn (gctx, entities) =>
          let val ctxt = Context.cases Proof_Context.init_global I gctx
              val thy = Proof_Context.theory_of ctxt
```

**The remaining ~100 lines of the body change not at all.** Verified by grep over
`:898-1006`: the body captures exactly ONE name from the enclosing scope,
`get_state`, and that is the name being removed. (`check_criterion`,
`simp_rule_net`, `intro_rule_net`, `elim_rule_net`, `budget`, `driver`, `send`,
`recv` — all zero hits.) The body ends at `:1006`:
`in map (fn e => the_default (NONE, NONE) (try retrieve e)) entities end),`.

**Step 2 — the AoA command uses it with the agent unpacker.**
`make_retrieve_entity_callback agent_context_unpacker`, where
`agent_context_unpacker` is at `:734`. Behaviour identical to today.

**Step 3 — `query_by_name` installs it with the static unpacker.**
At `agent_server.ML:2152-2166` the command currently carries one callback:

```sml
    val su = Context_Callbacks.static_context_unpacker context
    ... callback = [Universal_Key.make_universal_key_callback su],
```

becomes

```sml
    callback = [Universal_Key.make_universal_key_callback su,
                make_retrieve_entity_callback su],
```

**Step 4 — Python actually uses it.**
`retrieval.py:913-949` `_query_entity_core` currently does

```python
rec = Semantic_DB[uk]
if rec is not None: rec = apply_live_name_if_member(rec, live_name)
_format_record(buf, f"{rec.kind.label} {rec.name}" if rec is not None else …, rec)
```

and `_format_record` (`:954-970`) prints `trunc_expr(rec.expr)` and
`rec.interpretation`. Change it to call `IsaMini.retrieve_entity` with
`(ctxt, [(kind, name)])` — `ctxt` is the parameter it already receives (a state
id from `retrieval.py:1002`, `None` from `toplevel.py:72`, and the static
unpacker eats nil) — and render the **returned** short name and expression, while
keeping `rec.interpretation` for the English.

**Read `contrib/Semantic_Embedding/DYNAMIC_MEMBER_NAMING_PLAN.md` §2.1 first.**
`retrieval.py:919-923`'s comment says the restraint in `apply_live_name_if_member`
(substituting the live name only for invented collection-member names) is
deliberate and cites that plan. Answer its reasoning rather than ignoring it.

### IMPLEMENTED 2026-08-23 — `Minilang_AoA` builds clean

The placement question resolved itself: a new top-level
`local open MessagePackBinIO.Pack MessagePackBinIO.Unpack in … end (*local*)`
block sits just **before** `fun raw_AoA`, inside `structure MiniLang_Agent_AoA`
(so both use sites see it; the signature does not export it, which is fine —
there are no external callers).

**The "body captures exactly ONE name" verification was wrong twice.** Besides
`get_state` (removed by the redesign), the body also captured:

1. `abbreviations_in_term` — self-contained (parameters only, library calls
   only); moved verbatim into the same top-level block.
2. `thm_roles` — depends on three iNet rule tables built once per AoA run from
   the run's init-time context (`simpset_of ctxt`, `Classical.dest_decls ctxt`)
   as a deliberate cache. Resolved by lifting the whole cluster into a top-level
   `fun make_thm_roles ctxt = … fn thms => …` and giving the generator a second
   parameter: `make_retrieve_entity_callback ctxt_unpack thm_roles`. raw_AoA
   keeps its per-run cache (`val thm_roles = make_thm_roles ctxt`, TODO comment
   kept in place); `query_by_name` builds one per call from its `context` via
   `Context.cases Proof_Context.init_global I`. Semantics unchanged on the AoA
   path: the role tables still reflect the init-time context, not the
   per-invocation one.

The four steps landed as designed. Python side:

- `model.py`: `_retrieve_entity_with_diagnostics` body extracted to module-level
  `retrieve_entities_with_diagnostics(connection, ctxt, entities)`; the method
  delegates with `ctxt=self.name`. Wire format unchanged (bare string decodes
  as SOME under `unpackOption`).
- `retrieval.py` `_query_entity_core`: after the guarded
  `apply_live_name_if_member`, one extra call
  `retrieve_entities_with_diagnostics(connection, ctxt, [(tag, live_name)])`;
  when it returns info, the heading shows the live externed short name and the
  expression shows the live-rendered propositions/type (per-item `trunc_expr`,
  newline-joined); `rec.interpretation` stays the stored English. When it
  returns None (kind without a retrieve branch, entity gone), the old stored
  rendering is the fallback. `live_name` is passed, not the agent's `name`, so
  the direct branch and the short-name retry branch normalize identically.
- `_format_record` gained an optional `expr` override so a live expression can
  show even when there is no semantic record.

**One deliberate small choice, flagged for review**: kinds whose live expression
list is empty — types, classes, locales (`retrieve` returns `[]` for them) —
keep the stored `rec.expr`. The alternative (show nothing) loses information and
the callback simply has no renderer for those kinds.

Verified: `isabelle build -d . -d contrib/Semantic_Embedding Minilang_AoA`
passes (2026-08-23); both Python modules import clean. NOT yet exercised at
runtime — no live AoA query or `query_by_name` RPC has been run against the new
code; a running REPL server must be restarted to pick up the `.ML` change.

## Requirement 2 — DONE, and what is left of it

Implemented in `model.py` (see the section above for the exact edits).
`exact_name` **is** included in the drop, ruled 2026-08-23; the *cap* is still
conditional (`cap = k if exact_name is None else len(scored_recs)`) because that
path never over-fetched and a bundle expansion legitimately returns more than k.

**A proposal that was raised and rejected**: warning the agent when an
`exact_name` lookup returns empty because its one hit was dropped. Rejected
because the warning would have been misleading. `Name_Space.extern_if`
(`name_space.ML:295-315`) already tries the fully qualified spelling without the
uniqueness requirement as its last fallback; `??.` means **no** spelling resolves
to the entity here, not "the short name is shadowed, try the long one". There is
no action the agent could take differently, so there is nothing to tell it. The
per-entity diagnostic still goes to the log, which is for humans.

## State at 2026-08-23, before compaction

**Committed** (superproject `5152e39`, `aa07a03`; `Semantic_Embedding`
`dd22e1b`, `ba1e1a1`; `Isabelle_RPC` `352192a`): this plan's earlier revisions,
`THEORY_HASH_REKEY_PLAN.md` §8 rewritten as a pointer, the integrated
`INFRA_FILTER_REWORK_PLAN.md`, the infra-filter instrumentation, the SKILL fixes.

**Uncommitted and mine**: `contrib/Isa-Mini/IsaMini/AoA/model.py` (+52 −5,
requirement 2, syntax-checked, not run) and this file. Backups in the scratchpad:
`model.py.bak`, `agent_server.ML.bak`,
`INFRA_FILTER_REWORK_PLAN.pre-integration.md`.

**Uncommitted and NOT mine** — do not sweep in: `contrib/Isa-Mini`'s
`driver_openai_api.py` and `translator`, `AOA_CLAUDECODE_DRIVER_SURROGATE_BUG.md`,
`data/*`, and the several root `*_PLAN.md` files belonging to other sessions.

**Permissions in force**: `isabelle build` is approved **for the sessions this
work needs** (granted 2026-08-23; earlier a narrower grant covered
`contrib/_se_check/SE_Check` only). Never add `-c` or `-f`. `isabelle-mcp` is
also available for compile-checking. Note that `SE_Check` does **not** cover
`contrib/Isa-Mini/Agent/agent_server.ML` — its session is
`HOL + Isabelle_RPC + Performant_Isabelle_ML` and compiles only
`Semantic_Embedding/Tools/*`. Checking `agent_server.ML` needs the
`Minilang_AoA` chain, whose heaps (`Minilang`, `Minilang_Translator`) are in the
stale list and `Minilang_AoA` was never built.

## Still open

1. **Does requirement 1 cover the third by-name path?**
   `semantics.py:1530` `query_by_name_raw` -> `mk_query_by_name_tool` (`:1620`),
   used by the **interpretation agent** (`semantic_interpretation.py:1165`). Its
   context is the theory being interpreted, not a proof state, so "render live"
   may mean something different there, or nothing at all. Not put to the user
   yet.
2. **Should the cached theorem pass re-check accessibility at query time?**
   Answered in practice by the decision above — once `??.` entities are dropped
   at display, the cached pass's gap no longer reaches the agent, and the only
   residue (a wasted ranking slot) is absorbed by the over-fetch. Recorded here
   because the gap itself is real and documented at
   `semantic_store.ML:1290-1298`: the cached fold (`context.ML:1303-1327`)
   applies `scope_ok`, `name_filter`, `prop_matches`, `target_type_filter` and the
   stale-member drop, but **not** `filter_opt`, so its entries carry the
   accessibility verdict of the theory-load context
   (`update_thm_cache`, `semantic_store.ML:2316-2353`, runs at
   `Theory.at_begin`/`at_end` in `Context.Theory thy`).

## Session state, 2026-08-20

This document belongs to the session doing the work. It came out of a
conversation about something else — the `infra_filter` theory marking, now
consolidated into `contrib/Semantic_Embedding/INFRA_FILTER_REWORK_PLAN.md` under
this same session. **The two threads are separate work; do not conflate them.**

Nothing here has been implemented yet. Build permission in this session is
narrow: **`contrib/Isabelle2025-2/bin/isabelle build -d contrib/_se_check SE_Check`
only** (approved 2026-08-20). Any other `isabelle build` needs a fresh explicit
command.
