#!/usr/bin/env python3

import json
import re
import sys
from sqlitedict import SqliteDict
from evaluation.evaluator import Result, Status
from transformers import AutoTokenizer
# from .evaluator import 

TYPES = {
    'Tactic Execution - Fails': [
        r'^Failed to finish proof \(line (\d+) of',
        r'^Failed to apply proof method \(line (\d+) of', 
        r'Failed to apply initial proof method \(line (\d+) of', 
        r'^Unable to figure out induct rule',
        r'^Failed to apply terminal proof method \(line (\d+) of',
        r'^Tactic failed',
        r'^No matching coinduction rule found'
        r'^Unable to figure out induct rule',
        r'^exception THM 0 raised.*symmetric$',
        r'^PROOF FAIL : Fail to apply the rules',
        r'^PROOF FAIL : Fail to apply the tactic',
    ],
    'Tactic Execution - Timeout': [
        r'^Timeout',
        r'^timed out'
    ],
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
    'Hammer Fail' : [
        r'^PROOF FAIL : Proof fails and Sledgehammer is disable due to debugging',
        r'^PROOF FAIL : Timeout',
        r'^PROOF FAIL : Fail to prove the goal',
        r'Fail to prove the goal',
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
        r'symmetric: no unifiers',
        r'^exception Match raised \(line 482 of', # recursive proofs generated
        r'^Already at bottom of proof', # mismatched bracket

        r'^INVALID_OPR : Incorrect number of VARS',
        r'^Bad context for command',
    ],
    'No proof generated or incomplete proof': [
        r'^exception Empty raised',
        r'^None$'
    ],
    'Other': [r'^exception Interrupt_Breakdown raised$']
}


def analyze_failure(result_path : str, response_path : str, model_name : str, max_length : int):

    responses = {}
    with open(response_path, "r", encoding="utf-8") as f:
        for line in f:
            data = json.loads(line)
            responses[str(data["index"])] = data

    tokenizer = AutoTokenizer.from_pretrained(model_name)
    def length_of(response):
        ret = len(tokenizer.encode(response['response'])) + len(tokenizer.encode(response['prelude'])) + len(tokenizer.encode(response['goal']))
        return ret


    counts = {}
    total = 0
    def count_cat(cat):
        nonlocal counts
        try:
            counts[cat] += 1
        except KeyError:
            counts[cat] = 1
    def count_cats(s):
        segs = s.split(' - ')
        cats = [ ' - '.join(segs[:i+1]) for i in range(len(segs))]
        for cat in cats:
            count_cat(cat)

    with SqliteDict(result_path) as db:
        for key, result in db.items():
            #length = length_of(responses[key])
            #if length >= 4000:
            #    #print(f"----------------------------------\n[{key}] Length: {length}\n{tokenizer.encode(responses[key])}")
            #    print(f"[{key}] Length: {length}")
            #continue
            if result.status == Status.FAIL:
                err = str(result.error)
                total += 1
                find_reason = 0
                found_cats = set()
                for failure_type, patterns in TYPES.items():
                    for pattern in patterns:
                        mat = re.search(pattern, err)
                        if mat:
                            find_reason += 1
                            # Check if the match object has a group 1
                            if 'Tactic Execution - Fails' in failure_type and len(mat.groups()) >= 1:
                                line_number = int(mat.group(1))
                                line = responses[key]['response'].split('\n')[line_number - 1].strip()
                                if 'auto_sledgehammer' in line:
                                    count_cats('Hammer Fail')
                                    found_cats.add('Hammer Fail')
                                else:
                                    count_cats(failure_type + ' - ' + str(pattern))
                                    found_cats.add(failure_type + ' - ' + str(pattern))
                            else:
                                count_cats(failure_type + ' - ' + str(pattern))
                                found_cats.add(failure_type + ' - ' + str(pattern))
                            break
                if re.search(r'^exception FAIL \(SOME fn\) raised', err) or re.search(r'^exception ABORT fn raised', err) or re.search(r'^Proof not finished', err):
                    find_reason += 1
                    if length_of(responses[key]) >= max_length:
                        count_cats('Exceeds Window')
                        found_cats.add('Exceeds Window')
                    else:
                        count_cats(r'Syntax Error - Proof Lang - ^exception FAIL \(SOME fn\) raised | ^exception ABORT fn raised | ^Proof not finished')
                        found_cats.add(r'Syntax Error - Proof Lang - ^exception FAIL \(SOME fn\) raised | ^exception ABORT fn raised | ^Proof not finished')

                if find_reason == 0:
                    count_cats('Unknown')
                    print(f"[{key}] Unknown failure: {err}")
                elif find_reason > 1:
                    print(f"[{key}] Multiple failure types ({find_reason}): {err}\n{found_cats}\n")
    for cat, count in sorted(list(counts.items()), key=lambda x: x[0]):
        print(f"{cat}: {count / total * 100:.3f}%, {count}")

if __name__ == "__main__":
    if len(sys.argv) <= 1:
        print("Usage: python evaluation/failure_analysis.py <result_path> <response_path> <model_name>")
        sys.exit(1)
    analyze_failure(sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4]))
