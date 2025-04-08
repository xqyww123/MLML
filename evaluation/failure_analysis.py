#!/usr/bin/env python3

import re
import sys
from sqlitedict import SqliteDict
from evaluation.evaluator import Result, Status
# from .evaluator import 

TYPES = {
    'Tactic Execution - Fails': [
        r'^Failed to finish proof', 
        r'^Failed to apply proof method', 
        r'Failed to apply initial proof method', 
        r'^Unable to figure out induct rule',
        r'^Failed to apply terminal proof method',
        r'^Tactic failed',
        r'^No matching coinduction rule found'
        r'^Unable to figure out induct rule',
        r'^exception THM 0 raised.*symmetric$'
    ],
    'Tactic Execution - Timeout': [r'^Timeout'],
    'Syntax Error - Undefined Fact': [r'^Undefined fact'],
    'Syntax Error - Term Lang - Type': [
        r'^Type unification failed', 
        r'^Undefined type name',
    ],
    'Syntax Error - Term Lang': [
        r'^Inner lexical error', 
        r'^Inner syntax error',
        r'^Ambiguous input',
        r'^Bad number of arguments for type constructor',
        r'^Undefined constant',
        r'^Ill-typed instantiation'
    ],
    'Hammer' : [
        r'^PROOF FAIL'
    ],
    'Syntax Error - Proof Lang - Fact Selection': [
        r'^Bad fact selection'
    ],
    'Syntax Error - Proof Lang - END Block': [
        r'^INVALID_OPR : This block should be closed by the END command.'
    ],
    'Syntax Error - Proof Lang': [
        r'^Outer syntax error',
        r'^Failed to refine any pending goal',
        r'^Undefined attribute',
        r'^Undefined case',
        r'^Malformed definition',
        r'^More arguments than parameters in instantiation of locale',
        r'assume: variables',
        r'^Induction argument not a variable',
        r'^Bad name binding',
        r'^Undefined method',
        r'^Too many parameters for case',
        r'^Rule has fewer conclusions than arguments given',
        r'^Undefined locale',
        r'^Unbound schematic variable',
        r'^Failed to retrieve literal fact',
        r'^ML error', # It's amazing, sometimes the model even tries to write ML?!
        r'^More names than parameters in subgoal!',
        # The following are for attribute subsystem
        r'^More instantiations than variables in theorem$', 
        r'^No such variable in theorem',
        r'OF: no unifiers',
        r'symmetric: no unifiers'
    ],
    'No proof generated or incomplete proof': [
        r'^exception Empty raised',
        r'^None$'
    ],
    'Other': [r'^exception Interrupt_Breakdown raised$']
}


def analyze_failure(result_path : str):
    counts = {}
    total = 0
    def count_cat(cat):
        nonlocal counts
        try:
            counts[cat] += 1
        except KeyError:
            counts[cat] = 1
    with SqliteDict(result_path) as db:
        for key, result in db.items():
            if result.status == Status.FAIL:
                err = str(result.error)
                total += 1
                find_reason = 0
                for failure_type, patterns in TYPES.items():
                    for pattern in patterns:
                        if re.search(pattern, err):
                            segs = failure_type.split(' - ')
                            cats = [ ' - '.join(segs[:i+1]) for i in range(len(segs))]
                            for cat in cats:
                                count_cat(cat)
                            count_cat(failure_type + ' - ' + str(pattern))
                            find_reason += 1
                            break
                if find_reason == 0:
                    count_cat('Unknown')
                    print(f"[{key}] Unknown failure: {err}")
                elif find_reason > 1:
                    print(f"[{key}] Multiple failure types: {err}")
    for cat, count in sorted(list(counts.items()), key=lambda x: x[0]):
        print(f"{cat}: {count / total * 100:.3f}%")

if __name__ == "__main__":
    if len(sys.argv) <= 1:
        print("Usage: python evaluation/failure_analysis.py <result_path>")
        sys.exit(1)
    target_path = sys.argv[1]
    analyze_failure(target_path)