import sys
import os
from data.gen_data import THEORIES, all_theories_in_session, all_deps_of, deps_of, session_of, short_name_of

BASE = 'HOL-Library'
BASE_THEORIES = all_theories_in_session(BASE)

REFERENCES = {}
for thy, info in THEORIES.items():
    if thy not in REFERENCES:
        REFERENCES[thy] = set()
    deps = info['deps']
    for dep in deps:
        if dep not in REFERENCES:
            REFERENCES[dep] = set()
        REFERENCES[dep].add(thy)

def can_use(thy):
    session = session_of(thy)
    has_examples = 'Example' in thy or 'example' in thy or \
            session in ['HOL-Proofs-Extraction']
    #if has_examples:
    #    print(thy)
    #has_examples = False
    #for dep in all_deps_of(thy):
    #    if 'Nitpick_Examples' in THEORIES[dep]['path']:
    #        print(f'{dep} {short_name_of(dep)}')
    #        has_examples = True
    return REFERENCES[thy] and \
        short_name_of(thy) not in ['Isa-REPL', 'Auto_Sledgehammer', 'Minilang', 'MS_Translator', 'MS_Translator_Top',
                                   'Minilang_Base'] and \
        not has_examples

total_work = 0
for thy, ref in REFERENCES.items():
    if can_use(thy) and thy not in BASE_THEORIES:
        total_work += 1
print(f'Total work: {total_work}')

DEPENDENCIES = {}
for thy, info in THEORIES.items():
    DEPENDENCIES[thy] = set(info['deps'])

dep_counts = {}
ready_thys = set()
used_thys = set()
used_sessions = set()

step_count = 0
def emit_step():
    global step_count
    os.makedirs(f'./tools/Build_AFP_Image/AFP-DEP1/AFP-DEP1-{step_count}', exist_ok=True)
    with open(f'./tools/Build_AFP_Image/AFP-DEP1/AFP-DEP1-{step_count}/ROOT', 'w') as f:
        if step_count == 0:
            f.write(f'session \"AFP-DEP1-{step_count}\" = \"{BASE}\" +\n')
        else:
            f.write(f'session \"AFP-DEP1-{step_count}\" = \"AFP-DEP1-{step_count-1}\" +\n')
        f.write(f'sessions\n')
        for session in used_sessions:
            f.write(f'  \"{session}\"\n')
        f.write(f'theories\n')
        for thy in used_thys:
            f.write(f'  \"{thy}\"\n')
    used_thys.clear()
    used_sessions.clear()
    step_count += 1

def use_thy(thy):
    if thy not in BASE_THEORIES:
        used_thys.add(thy)
        session = session_of(thy)
        if session != '':
            used_sessions.add(session)
        if len(used_thys) >= 256:
            emit_step()


for thy, deps in DEPENDENCIES.items():
    if len(deps) == 0:
        ready_thys.add(thy)

while ready_thys:
    best = None
    for thy in ready_thys:
        if session_of(thy) in used_sessions:
            best = thy
            ready_thys.remove(thy)
            break
    if not best:
        best = ready_thys.pop()
    use_thy(best)
    for ref in REFERENCES[best]:
        DEPENDENCIES[ref].remove(best)
        if len(DEPENDENCIES[ref]) == 0 and can_use(ref):
            ready_thys.add(ref)

#for ref, dep in DEPENDENCIES.items():
#    if can_use(ref) and len(dep) != 0:
#        raise Exception(f'{ref} has dependencies: {dep}')

with open('./tools/Build_AFP_Image/AFP-DEP1/ROOTS', 'w') as f:
    for i in range(step_count):
        f.write(f'AFP-DEP1-{i}\n')
