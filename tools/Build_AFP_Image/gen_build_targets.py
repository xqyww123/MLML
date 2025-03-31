import sys
import os
from data.isabelle import THEORIES, INFLUENCES, all_theories_in_session, all_deps_of, deps_of, session_of, short_name_of

BASE = 'HOL-Library'
BASE_THEORIES = all_theories_in_session(BASE)

def can_use(thy):
    session = session_of(thy)
    exempted = 'Jinja' in thy or 'Prime_Test' in thy or \
                'Elliptic_Test' in thy or 'Rational_Root_Test' in thy or \
                thy in ['UPF.NormalisationTestSpecification', 'KAT_and_DRA.Conway_Tests',
                        'Shadow_DOM.Shadow_DOM_BaseTest', 'HOL-Analysis.Summation_Tests']
    info = THEORIES[thy]
    has_examples = not exempted and (\
            'Example' in thy or 'example' in thy or \
            'example' in info['path'] or \
            'Test' in thy or \
            session in ['HOL-Proofs-Extraction'])
    #if has_examples:
    #    print(thy)
    #has_examples = False
    #for dep in all_deps_of(thy):
    #    if 'Nitpick_Examples' in THEORIES[dep]['path']:
    #        print(f'{dep} {short_name_of(dep)}')
    #        has_examples = True
    ret = INFLUENCES[thy] and \
        short_name_of(thy) not in ['Isa_REPL', 'Auto_Sledgehammer', 'Minilang', 'MS_Translator', 'MS_Translator_Top',
                                   'Minilang_Base'] and \
        not has_examples
    if not ret and INFLUENCES[thy] and any(can_use(ref) for ref in INFLUENCES[thy]):
        print(f'cannot drop {thy} (influences: {INFLUENCES[thy]})')
        ret = True
    return ret


DEPENDENCIES = {}
for thy, info in THEORIES.items():
    DEPENDENCIES[thy] = set(info['deps'])

dep_counts = {}
ready_thys = set()
used_thys = set()
used_sessions = set()

step_count = 0
total_work = 0
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
    global total_work
    if thy not in BASE_THEORIES:
        total_work += 1
        used_thys.add(thy)
        session = session_of(thy)
        if session != '':
            used_sessions.add(session)
        if len(used_thys) >= 384:
            emit_step()


for thy, deps in DEPENDENCIES.items():
    if len(deps) == 0:
        ready_thys.add(thy)

with open('./tools/Build_AFP_Image/AFP-DEP1/all_theories.lst', 'w') as f:
    while ready_thys:
        best = None
        for thy in ready_thys:
            if session_of(thy) in used_sessions:
                best = thy
                ready_thys.remove(thy)
                break
        if not best:
            best = ready_thys.pop()
        f.write(f'{best}\n')
        use_thy(best)
        for ref in INFLUENCES[best]:
            DEPENDENCIES[ref].remove(best)
            if len(DEPENDENCIES[ref]) == 0 and can_use(ref):
                ready_thys.add(ref)

#for ref, dep in DEPENDENCIES.items():
#    if can_use(ref) and len(dep) != 0:
#        raise Exception(f'{ref} has dependencies: {dep}')

with open('./tools/Build_AFP_Image/AFP-DEP1/ROOTS', 'w') as f:
    for i in range(step_count):
        f.write(f'AFP-DEP1-{i}\n')

print(f'Total work: {total_work}')
