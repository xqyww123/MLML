#!/bin/python

import json
import os
import sys
from IsaREPL import Client, Position, REPLFail
from Isa_Mini import Mini
import csv
import logging
from enum import Enum
from data import prelude_of, PISA_DATA
from sqlitedict import SqliteDict

class Result(Enum):
    SUCCESS = "SUCCESS"
    FAIL = "FAIL"
    CASE_NOT_AVAILABLE = "CASE_NOT_AVAILABLE"

class CaseNotAvailable(Exception):
    """Exception raised when a test case is not available."""
    def __init__(self, message="The requested test case is not available"):
        self.message = message
        super().__init__(self.message)

def PISA_prelude(index):
    try:
        pos_before, pos, statement = PISA_DATA[index]
        prelude = prelude_of(pos_before.file, pos_before.line)
        return prelude
    except KeyError:
        raise CaseNotAvailable(f"MiniLang_PISA: case {index} not available")

class MiniLang_Base:
    def __init__(self, addr):
        self.addr = addr
        self.mini = None

    def __enter__(self):
        if self.mini:
            self.mini.__enter__()
        return self

    def __exit__(self, exc_type, exc_value, traceback):
        if self.mini:
            self.mini.__exit__(exc_type, exc_value, traceback)
        return None
    
    def start_case(self, category, index):
        raise NotImplementedError("start_case must be implemented by subclass")
    
    def validate(self, category, index, srcs):
        try:
            self.start_case(category, index)
        except CaseNotAvailable:
            return Result.CASE_NOT_AVAILABLE
        result = Result.FAIL
        for src in srcs:
            try:
                response, error = self.repl.eval(src)
                if not error and response:
                    if not response[-1][3][3]:
                        result = Result.SUCCESS
                        break
            except REPLFail:
                pass
        return result

    def move_to(self, file, line, column):
        if self.mini:
            self.mini.close()
        pos = (os.path.abspath(file), line, column)
        self.mini = Mini(self.addr, 'HOL', pos)
        self.mini.set_timeout(900 * 1000)

    def reset_eval(self, src):
        if self.mini:
            self.mini.close()
        self.mini = Mini(self.addr, 'HOL')
        self.mini.eval(src)
        self.mini.set_timeout(900 * 1000)

    def reset(self):
        if self.mini:
            self.mini.close()
        self.mini = None

class MiniLang_PISA(MiniLang_Base):
    def start_case(self, category, index):
        if category != "test":
            raise ValueError(f"MiniLang_PISA: only support test category")
        try:
            pos_before, pos, statement = PISA_DATA[index]
        except KeyError:
            raise CaseNotAvailable(f"MiniLang_PISA: case {index} not available")
        self.move_to(pos.file, pos.line, pos.column)
    

#    @classmethod
#    def print_state(response):
#        ret, finished = response
#        state = Mini.parse_prooftree(ret[2])
#        new_items = Mini.parse_item(ret[0])
#        rich.print_json(json.dumps(state, indent=2))
#        if ret[1]:
#            console.print('enter case ' + ret[1], style='bold grey66')
#        if ret[0][0] or ret[0][1]:
#            console.print('newly introduced: ' + json.dumps(new_items, indent=2), style='bold grey66')
#        if finished:
#            console.print('All goals are proven', style='bold green')
#
#    def pretty_print(self, src):
#        MiniLang_PISA.print_state(self.eval(src))


class Isar_Base:
    def __init__(self, addr):
        self.addr = addr
        self.repl = Client(addr, 'HOL')

    def __enter__(self):
        self.repl.__enter__()
        return self

    def __exit__(self, exc_type, exc_value, traceback):
        self.repl.__exit__(exc_type, exc_value, traceback)
        return None

    def move_to(self, file, line, column=0):
        if self.repl:
            self.repl.close()
        self.repl = Client(self.addr, 'HOL')
        self.repl.eval_file (os.path.abspath(file), line, column)
    
    def reset_eval(self, src):
        if self.repl:
            self.repl.close()
        self.repl = Client(self.addr, 'HOL')
        self.repl.eval(src)

    def start_case(self, category, index):
        raise NotImplementedError("start_case must be implemented by subclass")

    def validate(self, category, index, srcs):
        try:
            self.start_case(category, index)
        except CaseNotAvailable:
            return (Result.CASE_NOT_AVAILABLE, None)
        result = (Result.FAIL, None)
        for src in srcs:
            try:
                response, error = self.repl.eval(src, timeout=600000)
                print(error)
                if error:
                    result = (Result.FAIL, error)
                elif response and not response[-1][3][3]:
                    result = (Result.SUCCESS, None)
                    break
            except REPLFail as E:
                result = (Result.FAIL, E)
                print(E)
                pass
        return result

    def reset(self):
        if self.repl:
            self.repl.close()
        self.repl = None

class Isar_PISA(Isar_Base):
    def start_case(self, category, index):
        if category != "test":
            raise ValueError(f"Isar_PISA: only support test category")
        try:
            pos_before, pos, statement = PISA_DATA[index]
        except KeyError:
            raise CaseNotAvailable(f"Isar_PISA: case {index} not available")
        self.move_to(pos.file, pos.line, pos.column)


#if __name__ == "__main__":
#    print('self-testing')
#
#    with MiniLang_PISA("127.0.0.1:6666") as test:
#        assert(test.validate("test", 0, ["END"]) == Result.SUCCESS)
#        assert(test.validate("test", 29, ["END"]) == Result.CASE_NOT_AVAILABLE)
#        assert(test.validate("test", 1, ["UNFOLD echelon_form_upt_k_def END WITH assms"]) == Result.SUCCESS)
#
#    with Isar_PISA("127.0.0.1:6666") as test:
#        assert(test.validate("test", 0, ["by simp"]) == Result.SUCCESS)
#        assert(test.validate("test", 29, ["by simp"]) == Result.CASE_NOT_AVAILABLE)
#        assert(test.validate("test", 1, ["using assms unfolding echelon_form_upt_k_def by auto"]) == Result.SUCCESS)


def preprocess_MiniF2F(addr):
    with Client(addr, 'HOL') as c:
        def parse(path):
            with open(path, 'r', encoding='utf-8') as file:
                commands = c.fast_lex(file.read())
            # Find the first theorem command
            theorem_index = -1
            for idx, (_, command) in enumerate(commands):
                if command.strip().startswith("theorem"):
                    theorem_index = idx
                    break

            if theorem_index == -1:
                raise Exception(f"MiniF2F: No theorem found in {path}")
            
            src = '\n'.join([command[1] for command in commands[:theorem_index+1]])
            return src
        def mk_dataset(path):
            validate_files = [f for f in os.listdir(path)]
            validation_set = {}
            for file in validate_files:
                src = parse(f'{path}/{file}')
                name, _ = os.path.splitext(os.path.basename(file))
                validation_set[name] = src
            return validation_set
        validate_set = mk_dataset('./data/miniF2F/isabelle/valid')
        test_set = mk_dataset('./data/miniF2F/isabelle/test')
        with open('cache/miniF2F_validation.json', 'w', encoding='utf-8') as f:
            json.dump(validate_set, f, ensure_ascii=False, indent=4)
        with open('cache/miniF2F_test.json', 'w', encoding='utf-8') as f:
            json.dump(test_set, f, ensure_ascii=False, indent=4)

#if not os.path.isfile('cache/miniF2F_validation.json') or not os.path.isfile('cache/miniF2F_test.json'):
#    preprocess_MiniF2F("127.0.0.1:6666")
#
#if __name__ == "__main__":
#    with open('cache/miniF2F_validation.json', 'r', encoding='utf-8') as f:
#        MINIF2F_VALIDATION = json.load(f)
#    with open('cache/miniF2F_test.json', 'r', encoding='utf-8') as f:
#        MINIF2F_TEST = json.load(f)
#
#
#class MiniLang_MiniF2F(MiniLang_Base):
#    def start_case(self, category, index):
#        if category not in ["test", "valid"]:
#            raise ValueError(f"MiniLang_MiniF2F: only support test and valid category")
#        dataset = MINIF2F_VALIDATION if category == "valid" else MINIF2F_TEST
#        try:
#            src = dataset[index]
#        except KeyError:
#            raise CaseNotAvailable(f"MiniLang_MiniF2F: case {index} not available")
#        self.reset_eval(src)
#
#class Isar_MiniF2F(Isar_Base):
#    def start_case(self, category, index):
#        if category not in ["test", "valid"]:
#            raise ValueError(f"Isar_MiniF2F: only support test and valid category") 
#        dataset = MINIF2F_VALIDATION if category == "valid" else MINIF2F_TEST
#        try:
#            src = dataset[index]
#        except KeyError:
#            raise CaseNotAvailable(f"Isar_MiniF2F: case {index} not available")
#        self.reset_eval(src)
#
#if __name__ == "__main__":
#    print('self-testing MiniF2F')
#    with MiniLang_MiniF2F("127.0.0.1:6666") as test:
#        assert(test.validate("valid", "aime_1983_p9", [
#            r"""DEFINE y where "y=x * sin x"
#            HAVE fact0: "12 \<le> (9 * y^2 + 4) / y" 
#                HAVE fact1: "y>0" UNFOLD y_def END WITH sin_gt_zero assms
#                HAVE fact2: "0 \<le> (3 * y - 2)^2" END
#            END WITH fact1 fact2 field_simps power2_eq_square
#            UNFOLD y_def
#            END WITH fact0 power2_eq_square algebra_simps
#            """
#            ]) == Result.SUCCESS)
#
#    with Isar_MiniF2F("127.0.0.1:6666") as test:
#        assert(test.validate("valid", "aime_1983_p9", [
#            r""" proof -
#    define y where "y=x * sin x"
#    have "12 \<le> (9 * y^2 + 4) / y" 
#    proof -
#        have "y>0" using assms unfolding y_def 
#        by (simp add: sin_gt_zero)
#        moreover have "0 \<le> (3 * y - 2)^2" by auto
#        ultimately show ?thesis unfolding power2_eq_square
#        by (auto simp:field_simps)
#    qed
#    then show ?thesis unfolding y_def 
#        by (auto simp:power2_eq_square algebra_simps)
#    qed"""
#        ]) == Result.SUCCESS)


def eval_pisa(result_path, response_path, evaluator):
    success = 0
    unavailable = 0
    total = 0
    results = []
    def print_state():
        success_rate = success / (total-unavailable) if total - unavailable > 0 else 0
        unavailable_rate = unavailable / total if total > 0 else 0
        print(f"Success: {success_rate}, Unavailable: {unavailable_rate}")
    with SqliteDict(result_path, autocommit=True) as db:
        with evaluator as test:
            with open(response_path, "r", encoding="utf-8") as f: 
                for line in f:
                    data = json.loads(line)
                    print(f"evaluating {data['index']}")
                    if data["index"] in db and db[data["index"]] != Result.CASE_NOT_AVAILABLE and db[data['index']] != 0:
                        result, err = db[data["index"]]
                    else:
                        try:
                            result, err = test.validate("test", data["index"], [data["response"]])
                            db[data["index"]] = (result, err)
                        except REPLFail as E:
                            test.reset()
                            print(E)
                            result = Result.CASE_NOT_AVAILABLE
                    if result == Result.SUCCESS:
                        success += 1
                    elif result == Result.CASE_NOT_AVAILABLE:
                        unavailable += 1
                    total += 1
                    results.append(result)
                    print_state()
    print_state()
    return results


if __name__ == "__main__":
    print('self-test passed')
if __name__ == "__main__" and len(sys.argv) > 1 and sys.argv[1] == "eval-mini-pisa":
    eval_pisa('./evaluation/minilang_pisa_result.db', './evaluation/minilang_response.jsonl', MiniLang_PISA("127.0.0.1:6666"))
elif __name__ == "__main__" and len(sys.argv) > 1 and sys.argv[1] == "eval-isar-pisa":
    eval_pisa('./evaluation/isar_pisa_result.db', './evaluation/isar_response.jsonl', Isar_PISA("127.0.0.1:6666"))
elif __name__ == "__main__":
    print("Usage: python lib_test.py eval-mini-pisa|eval-isar-pisa")
    exit()
