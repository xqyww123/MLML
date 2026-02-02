from sqlitedict import SqliteDict
import re

TYPES = {
    'Parse': [
        r'^exception Parse_Fail',
        r'^exception FAIL \(SOME fn\) raised \(line 167 of'
    ],
    'Unsupported - Meta': [
        r'^Conclusion in obtained context must be object-logic judgment',
        r'^exception OPR_FAIL \(INVALID_OPR, "Fail to atomize the proposition into HOL"\)',
        r'^Undeclared type constructor: "HOL.bool"'
    ],
    'Desugar Term': [
        r'^exception TERM raised \(line 1518',
        r'^exception TERM raised \(line 1434 '
    ],
    'Tactic': [
        r'^Failed to refine any pending goal$',
        r'^exception OPR_FAIL \(PROOF_FAIL, "Some proof obligation fails"\) raised',
        r'^Timeout after',
        r'^Failed to apply proof method',
        r'^Failed to apply initial proof method',
        r'Fail to apply the tactic',
        r'^No proof goal',
        r'^Failed to finish proof'
    ],
    'Tactic - FIX': [
        r'^exception ESORRY'
    ],
    'Unsupported - Command': [
        r'exception Unsupported "([^"]*)" raised'
    ],
    'Unsupported - Calculation': [
        r'Undefined fact: "calculation"'
    ],
    'Unsupported - undefined case': [
        r'^Undefined case'
    ],
    'Unsupported - invalid proof': [
        r'^incomplete MINSHELL script'
    ],
    'Unsupported - translation fail': [
        r'^exception Translation_Fail'
    ],
    'Unsupported - schematic variable': [
        r'^Unbound schematic variable',
    ],
    'Unsupported - subgoal parameters': [
        r'^More names than parameters in subgoal',
        r'^Excessive subgoal parameter specification',
    ],
    'Unsupported - bad arguments of methods': [
        r'^Bad arguments for method',
    ],
    'Unsupported - parsing': [
        r'^Ambiguous input produces',
        r'^Ambiguous input \(line',
    ],
    'Unsupported - bad processing about RULE': [
        r'exception OPR_FAIL \(PROOF_FAIL, "Fail to apply the rules"\)'
    ],
    'Bug - Fact Selection': [
        r'^Bad fact selection'
    ],
    'Bug - Ignore': [
        r'^exception IGNORE raised',
    ],
    'Bug - map_facts': [
        r'^BUG map_facts'
    ],
    'Bug - Pattern Match': [
        r'^exception match raised',
        r'Variable has two distinct types',
        r'expand_atom: ill-typed replacement',
        r'Pattern match failed',
    ],
    'Unknown - No such variable in theorem': [
        r'^No such variable in theorem'
    ],
    'Unsupported - induct rule': [
        r'Unable to figure out induct rule',
    ],
    'Unknown - malformed definition': [
        r'^BUG malformed definition',
    ],
    'Unknown - More instantiations than variables in theorem': [
        r'^More instantiations than variables in theorem'
    ],
    'Bug - Invariant': [
        r'^exception BROKEN_INVARIANT raised',
    ],
    'Bug - ONESHOT_ALREADY_SET': [
        r'^exception ONESHOT_ALREADY_SET raised',
    ],
    'Bug - UnequalLengths': [
        r'^exception UnequalLengths raised'
    ],
    'Bug - 3PLbwUDhTAGAvX/M+3jl3g': [
        r'^BUG 3PLbwUDhTAGAvX/M\+3jl3g'
    ],
    'Bug - CASES MP': [
        r'^BUG: CASES\' MP'
    ],
    'Bug - cannot parse the XXX fact': [
        r'^BUG cannot parse the'
    ],
    'Bug - case': [
        r'^BUG case'
    ],
    'Unknown - Too many parameters for case': [
        r'^Too many parameters for case'
    ],
    'Bug - Some subgoal is not paired': [
        r'^BUG Some subgoal is not paired'
    ],
    'Bug - fails to match the goal': [
        r'^BUG fails to match the goal'
    ],
    'Bug - insertion_hs_of': [
        r'^BUG insertion_hs_of'
    ],
    'Bug - bb5e': [
        r'^BUG bb5e'
    ],
    'Bug - insufficient separations': [
        r'^BUG insufficient separations'
    ],
    'Bug - sep': [
        r'^BUG sep'
    ],
    'Bug - fq23hl': [
        r'^BUG fq23hl'
    ],
    'Bug - h8KYedJsTC2jm63bGgXzfg': [
        r'^BUG h8KYedJsTC2jm63bGgXzfg'
    ],
    'Bug - XXX should be already eliminated here': [
        r'^BUG: \w* should be already eliminated here'
    ],
    'Bug - Option': [
        r'^exception Option raised',
    ],
    'Bug - Subscript': [
        r'^exception Subscript raised'
    ],
    'Bug - assumptions should have no attribute here.': [
        r'assumptions should have no attribute here'
    ],
    'Unknown - L3036': [
        r'^exception Match raised \(line 3036'
    ],
    'Unknown - L1972': [
        r'^exception Match raised \(line 1972'
    ],
    'Unknown - L2638': [
        r'^exception Match raised \(line 2638'
    ],
    'Unknown - Duplicate constant declaration':[
        r'^Duplicate constant declaration'
    ],
    'Unknown - dest_Trueprop': [
        r'^exception TERM raised \(line 196 of "~~/src/HOL/Tools/hologic.ML"\): dest_Trueprop'
    ],
    "Unknown - Morphism": [
        r'^exception MORPHISM'
    ],
    'Bug - BUG reduce_MPROOFs, unequal vs': [
        r'^BUG reduce_MPROOFs, unequal vs'
    ],
    'Unknown - No such variable in subgoal': [
        r'No such variable in subgoal'
    ],
    'Unknown - Undefined method (': [
        r'^Undefined method: "\("'
    ],
    'Unknown - Failed to retrieve literal fact': [
        r'^Failed to retrieve literal fact'
    ],
    'Unknown - Sort constraint inconsistent': [
        r'Sort constraint .* inconsistent'
    ],
    'Unknown - CTERM': [
        r'^exception CTERM',
    ],
    'Unknown - THM': [
        r'^exception THM',
    ],
    'Unknown - THEORY CONTEXT': [
        r'^Cannot join unrelated theory certificates',
        r'^exception CONTEXT \("Cannot transfer: not a super theory',
        r'^exception OPR_FAIL \(PROOF_FAIL, "Cannot join unrelated theory certificates',
    ],
    'Unknown - UNDEFINED FACT': [
        r'^Undefined fact',
    ],
    'Unknown - UNDEFINED CONSTANT': [
        r'^Undefined constant',
    ],
    'Unknown - type unification': [
        r'^Type unification failed',
    ],
    'Unknown - no current facts available': [
        r'^No current facts available',
    ],
    'Unknown - result contains obtained parameters': [
        r'^Result contains obtained parameters',
    ],
    'Uknown - duplicate fixed variable': [
        r'^Duplicate fixed variable',
    ],
    'Unknown - illegal application of proof command': [
        r'^Illegal application of proof command',
    ],
    'Unknown - incorrect number of VARS': [
        r'^exception OPR_FAIL \(INVALID_OPR, "Incorrect number of VARS"\)',
    ],
    'Unknown - ill-typed instantiation': [
        r'^Ill-typed instantiation',
    ],
    'Unknown - <markup>': [
        r'^exception OPR_FAIL \(PROOF_FAIL, "<markup>"\) raised',
    ],
    'Unknown - FOUND ?': [
        r'^exception FOUND \? raised \(line 47'
    ],
    'Unknown - PRF_FAIL': [
        r'^exception PRF_FAIL fn raised'
    ],
    'BAD_SOURCE': [
        r'^exception Bad_Source'
    ]
}

COUNTS = {}
def count_cat(cat):
    try:
        COUNTS[cat] += 1
    except KeyError:
        COUNTS[cat] = 1

def count_cats(s):
    segs = s.split(' - ')
    cats = [ ' - '.join(segs[:i+1]) for i in range(len(segs))]
    for cat in cats:
        count_cat(cat)

TOTAL_COUNT = 0

unsupported_commands = set()

with SqliteDict('./data/translation/results.db') as db:
    for key, value in db.items():
        (_,_,cat) = key.split(':')
        if cat != 'refined':
            continue
        (_,errs,_,_) = value
        if not errs:
            continue
        for err in errs:
            TOTAL_COUNT += 1
            reason = 0
            for failure_type, patterns in TYPES.items():
                for pattern in patterns:
                    mat = re.search(pattern, err)
                    if mat:
                        if failure_type == 'Unknown - UNDEFINED FACT' and err.startswith(r'Undefined fact: "calculation"'):
                            continue
                        if failure_type == 'Unsupported - Command':
                            unsupported_commands.add(mat.group(1).strip())
                        reason += 1
                        count_cats(failure_type)
            if reason == 0:
                print(f'UNKNOWN: {err}')
            if reason > 1:
                print(f'ERROR: multi error reason: {err}')
                exit(-1)

# TOTAL_COUNT -= COUNTS['Unknown']

print(f'Unsupported commands: {len(unsupported_commands)}')
print(unsupported_commands)
for cat, count in sorted(list(COUNTS.items()), key=lambda x: x[0]):
    print(f"{cat}: {count / TOTAL_COUNT * 100:.3f}%, {count}")