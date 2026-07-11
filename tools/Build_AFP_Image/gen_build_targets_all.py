"""Generate the AFP-ALL chained sessions under tools/Build_AFP_Image/AFP-DEP0.

AFP-DEP1 only contains theories that are imported at least once (`can_use`
requires a non-empty INFLUENCES set).  AFP-ALL builds on top of the DEP1 chain
top (AFP-DEP1-21) and adds *every remaining* theory -- chiefly the leaf
theories that nothing imports -- while the same example/test/own-tooling
filter as AFP-DEP1 still applies.

Reuses `has_examples` / `EXEMPT_SHORT` / `BASE_THEORIES` from gen_build_targets
(imported as a sibling module; its generation body is guarded by __main__ so
importing it has no side effects).

IMPORTANT: AFP-ALL is a cumulative chain (AFP-ALL-N = AFP-ALL-(N-1) + ...), so
once a step's heap is built, changing ANY earlier step's ROOT invalidates it.
Do NOT re-run this generator to drop a clashing theory -- that reshuffles the
whole partition. Instead remove the theory (and its dependents) from the
specific ROOT that lists it, in place. Regenerate only for a from-scratch
rebuild. The partition is deterministic (sorted), so a full regen at least
reproduces itself.
"""
import os
from data.isabelle import THEORIES, INFLUENCES, SESSIONS, session_of, short_name_of
from gen_build_targets import has_examples, EXEMPT_SHORT, BASE_THEORIES, CLASH_EXCLUDE

DEP1_BASE = 'AFP-DEP1-21'                       # chain top of the DEP1 image
DEP1_DIR  = './tools/Build_AFP_Image/AFP-DEP1'
OUT_DIR   = './tools/Build_AFP_Image/AFP-DEP0'
BATCH     = 384


def can_use_all(thy):
    """Like gen_build_targets.can_use but WITHOUT the "imported at least once"
    requirement.  The example/test, own-tooling and clash filters still apply."""
    return (thy not in CLASH_EXCLUDE
            and short_name_of(thy) not in EXEMPT_SHORT
            and not has_examples(thy))


# --- theories already present in the DEP1 image (listed in its ROOTs) ---------
covered = set(BASE_THEORIES)
for i in range(22):
    mode = None
    for line in open(f'{DEP1_DIR}/AFP-DEP1-{i}/ROOT').read().splitlines():
        t = line.strip()
        if t == 'sessions':
            mode = 's'; continue
        if t == 'theories':
            mode = 't'; continue
        if mode == 't' and t.startswith('"'):
            covered.add(t.strip('"'))

# --- everything that passes the filter but is not yet covered ------------------
remaining = set(t for t in THEORIES if can_use_all(t) and t not in covered)

# dependency edges restricted to `remaining` (deps outside remaining are already
# satisfied by the DEP1 image or provided via a declared session)
DEP = {t: set(d for d in THEORIES[t]['deps'] if d in remaining) for t in remaining}
ready = set(t for t in remaining if not DEP[t])

used_thys = set()
used_sessions = set()
step_count = 0
total = 0


def base_of_step():
    return DEP1_BASE if step_count == 0 else f'AFP-ALL-{step_count - 1}'


def emit_step():
    global step_count
    os.makedirs(f'{OUT_DIR}/AFP-ALL-{step_count}', exist_ok=True)
    with open(f'{OUT_DIR}/AFP-ALL-{step_count}/ROOT', 'w') as f:
        f.write(f'session "AFP-ALL-{step_count}" = "{base_of_step()}" +\n')
        f.write('sessions\n')
        for s in sorted(used_sessions):
            f.write(f'  "{s}"\n')
        f.write('theories\n')
        for t in sorted(used_thys):
            f.write(f'  "{t}"\n')
    used_thys.clear()
    used_sessions.clear()
    step_count += 1


def use_thy(thy):
    global total
    total += 1
    used_thys.add(thy)
    session = session_of(thy)
    if session != '':
        used_sessions.add(session)
    elif thy in SESSIONS:
        used_sessions.add(thy)          # bare (global) theory naming a session
    if len(used_thys) >= BATCH:
        emit_step()


os.makedirs(OUT_DIR, exist_ok=True)
with open(f'{OUT_DIR}/all_theories.lst', 'w') as f:
    while ready:
        best = None
        # deterministic order (sorted), so regenerating never reshuffles the
        # partition and already-built AFP-ALL-N heaps stay valid
        for thy in sorted(ready):
            if session_of(thy) in used_sessions:
                best = thy
                ready.remove(thy)
                break
        if not best:
            best = min(ready)
            ready.remove(best)
        f.write(f'{best}\n')
        use_thy(best)
        for ref in INFLUENCES[best]:
            if ref in DEP and best in DEP[ref]:
                DEP[ref].discard(best)
                if not DEP[ref]:
                    ready.add(ref)

# emit the trailing partial batch -- AFP-ALL must contain *all* theories
if used_thys:
    emit_step()

with open(f'{OUT_DIR}/ROOTS', 'w') as f:
    for i in range(step_count):
        f.write(f'AFP-ALL-{i}\n')

print(f'AFP-ALL total theories: {total}, steps: {step_count}')
