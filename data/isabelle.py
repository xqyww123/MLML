from sqlitedict import SqliteDict
import os
import logging
import json
from IsaREPL import Client, Position, REPLFail
import csv
import sys
import re
from typing import Tuple  # Add this import for Tuple type
import time
from . import language
from . import proof_context
from . import premise_selection

# Configure logging to print to screen
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    datefmt='%Y-%m-%d %H:%M:%S'
)

if not os.path.exists('cache'):
    os.makedirs('cache')

with open('./data/sessions.json', 'r') as f:
    SESSIONS = json.load(f)

with open('./data/theories.json', 'r') as f:
    # key: long name
    # value: {'deps':[long names], 'path':file_name}
    THEORIES = json.load(f)
    THEORIES_IN_FILE = {}
    for long_name, info in THEORIES.items():
        path = info['path']
        if path not in THEORIES_IN_FILE:
            THEORIES_IN_FILE[path] = []
        THEORIES_IN_FILE[path].append(long_name)

INFLUENCES = {}
for thy, info in THEORIES.items():
    if thy not in INFLUENCES:
        INFLUENCES[thy] = set()
    deps = info['deps']
    for dep in deps:
        if dep not in INFLUENCES:
            INFLUENCES[dep] = set()
        INFLUENCES[dep].add(thy)

def deps_of(thy, depth=1, ret = None):
    """
    @return: `depth`-th generation dependencies of `thy`.
        Specially, `deps_of(thy, depth=i)` returns all dependencies of `thy` if i is negative.
    @param depth: the generation of dependencies to return.
    @example:
    deps_of(thy, depth=0) returns the `thy` itself.
    deps_of(thy, depth=1) returns the `thy` and its immediate dependencies.
    deps_of(thy, depth=2) returns the deps_of(thy,depth=1) and the immediate dependencies of deps_of(thy,depth=1).
    """
    if ret is None:
        ret = set()
    if thy in ret:
        return ret
    ret.add(thy)
    if depth != 0:
        try:
            for dep in THEORIES[thy]['deps']:
                deps_of(dep, depth=depth-1, ret=ret)
        except KeyError:
            pass
    return ret

def session_of(thy):
    return '.'.join(thy.split('.')[:-1])

def short_name_of(thy):
    return thy.split('.')[-1]

def all_theories_in_session(session_name):
    ret = set()
    try:
        thys = SESSIONS[session_name]['theories']
    except KeyError:
        thys = SESSIONS[session_name]
    for thy in thys:
        ret.add(thy)
        ret.update(deps_of(thy, depth=-1))
    return ret

def location_of(thy):
    try:
        return THEORIES[thy]['path']
    except KeyError:
        return None

def topological_sort():
    ranks = {}
    def ranking(thy):
        if thy in ranks:
            return ranks[thy]
        else:
            rank = 0
            for dep in deps_of(thy):
                rank = max(rank, ranking(dep))
            rank += 1
            ranks[thy] = rank
            return rank
    sorted_thy = sorted(THEORIES, key=lambda x: ranking(x))
    with open('data/sorted_thy.txt', 'w') as f:
        for thy in sorted_thy:
            f.write(f"{thy}\n")

if not os.path.exists('data/sorted_thy.txt'):
    logging.info('Topological sorting of theories')
    topological_sort()

with open('data/sorted_thy.txt', 'r') as f:
    SORTED_THY = f.read().splitlines()

def collect_declarations():
    declarations = {}
    with SqliteDict('./data/translation/declarations.db') as db:
        for key, command in db.items():
            match key.split(':'):
                case (file,line,ofs):
                    # this `ofs` is the offset in the entire file stream, instead of the line.
                    if file not in declarations:
                        declarations[file] = []
                    declarations[file].append((int(line), int(ofs), command))
    declarations = {k: sorted(v, key=lambda x: x[1]) for k, v in declarations.items()}
    with open('data/declarations.json', 'w') as f:
        json.dump(declarations, f)

if not os.path.exists('data/declarations.json'):
    logging.info('Collecting declarations')
    collect_declarations()

with open('data/declarations.json', 'r') as f:
    DECLARATIONS = json.load(f) # a map from file paths to declarations which are tuples of (line, offset, command), sorted by the position of occurence

def prelude_of(file, line, dep_depth=1, use_proofs=False, use_comments=True, maxsize=None, length_of=len, camlize=False) -> str:
    """
    @param file: the path to the theory file
    @param dep_depth: if the prelude shall include the declarations of the dependencies of the theory,
        `dep_depth` indicates the generation of the dependencies to include.
        For example, `dep_depth=1` means the immediate dependencies of the theory;
        `dep_depth=2` means the immediate dependencies and the dependencies of the immediate dependencies;
        `dep_depth=None` means no dependencies shall be included.
    @param use_proofs:
        Set `use_proofs` to 'isar' to use Isar proofs;
        Set `use_proofs` to 'isar-SH*' to use isar-SH* proofs (isar-SH* is the thor-style Isar based on an improved Sledgehammer);
        Set `use_proofs` to 'minilang' to use minilang proofs.
        Set `use_proofs` to False to not use any proofs.
    """
    prelude0 = []
    try:
        prelude0 = [(x[0],x[2]) for x in DECLARATIONS[file] if x[0] < line]
    except KeyError:
        pass

    dep_thys = set()
    if dep_depth:
        try:
            thys = THEORIES_IN_FILE[file]
        except KeyError:
            thys = []
        for thy in thys:
            deps_of(thy, depth=dep_depth, ret=dep_thys)
        for thy in thys:
            dep_thys.remove(thy)
        
    prelude = []
    for dep in dep_thys:
        try:
            for decl in DECLARATIONS[location_of(dep)]:
                prelude.append((decl[0], decl[2]))
        except KeyError:
            pass
    prelude += prelude0

    _, PISA_AT = load_pisa_data()

    # add proofs
    if use_proofs:
        with SqliteDict('./data/translation/results.db') as db:
            ret = []
            size = 0
            for reverse_idx, (line, command) in enumerate(reversed(prelude)):
                idx = len(prelude) - 1 - reverse_idx
                if use_proofs and (idx == 0 or line != prelude[idx-1][0]) and (file, line) not in PISA_AT:
                    try:
                        (proof, err, _, _) = db[f"{file}:{line}:{use_proofs}"]
                        if camlize and language.is_minilang(use_proofs):
                            proof = language.camlize_minilang(proof)
                        if not use_comments:
                            proof = language.remove_comments(proof)
                        if not err:
                            seg = f"{command.strip()}\n{proof.strip()}\n\n"
                            if maxsize is not None and size + length_of(seg) >= maxsize:
                                break
                            ret.append(seg)
                            size += length_of(seg)
                    except KeyError:
                        if command.startswith('lemma') or command.startswith('theorem') or command.startswith('corollary'):
                            continue
                        seg = f"{command.strip()}\n\n"
                        if maxsize is not None and size + length_of(seg) >= maxsize:
                            break
                        size += length_of(seg)
                        ret.append(seg)
                else:
                    seg = f"{command.strip()}\n\n"
                    if maxsize is not None and size + length_of(seg) >= maxsize:
                        break
                    size += length_of(seg)
                    ret.append(seg)
            ret.reverse()
    else:
        ret = []
        for _, command in prelude:
            ret.append(command)
            ret.append('\n')
    # Remove leading 'end\n\n' elements
    while ret and ret[0].strip() == 'end':
        ret.pop(0)
            
    return ''.join(ret).strip()


def common_prefix(a, b):
    i, j = 0, 0  # Iterators for strings a and b
    match_len = 0  # Length of the matched prefix in a
    
    # Scan through both strings simultaneously
    while i < len(a) and j < len(b):
        # Skip whitespace in string a
        while i < len(a) and a[i] in ' \n':
            i += 1
        if i >= len(a):
            break
            
        # Skip whitespace in string b
        while j < len(b) and b[j] in ' \n':
            j += 1
        if j >= len(b):
            break
            
        # Compare non-whitespace characters
        if a[i] != b[j]:
            break
            
        # Move to next characters
        i += 1
        j += 1
        match_len = i  # Update the match length to current position in a
    
    return a[:match_len]


PISA_TEST_PATH="./data/PISA"

def preprocess_PISA(addr):
    with Client(addr, 'HOL') as c:
        def read_PISA(i):
            src_path = PISA_TEST_PATH+'/test_name_'+str(i)+'.json'
            with open(src_path, 'r', encoding='utf-8') as file:
                [[path,lemma]] = json.load(file)
            prefix = "/home/ywu/afp-2021-02-11/"
            if path.startswith(prefix):
                path = "./contrib/afp-2025-02-12/" + path[len(prefix):]
            if not os.path.isfile(path):
                raise FileNotFoundError(f"PISA {i}: theory not found: {path}")

            with open(path, 'r', encoding='utf-8') as file:
                commands = c.fast_lex(file.read())

            match_index = -1
            for idx, (_, command) in enumerate(commands):
                if command.startswith('qualified'):
                    command = command[len('qualified'):].strip()
                if command.startswith('private'):
                    command = command[len('private'):].strip()
                # Remove newlines and consecutive spaces in command
                command = command.replace('\n', ' ')
                command = re.sub(r'\s+', ' ', command).strip()

                common = common_prefix(lemma, command)

                if common == lemma or \
                    ' ' in common and ':' in common and i not in [557, 2656, 2674, 961, 1641, 2237, 1907] and \
                    (len(common) > 20 or re.match(r'^lemma \w+.*:', common)):
                    #if common != lemma:
                    #    print(f"PISA {i} inequal\n{common}\n{command}\n{lemma}\n")
                    match_index = idx
                    #print(f"PISA {i}: {common}")
                    break
            if match_index == -1:
                raise ValueError(f"PISA {i}: Cannot find {lemma}")
            else:
                pos_before = commands[match_index][0]
                pos = commands[match_index + 1][0]

            # Get the position of the next command if available

            pos_before.file = path
            pos.file = path
            return (pos_before, pos, commands[match_index][1])

        csv_file_path = "data/pisa_test.csv"
        with open(csv_file_path, 'w', newline='', encoding='utf-8') as csvfile:
            csv_writer = csv.writer(csvfile)
            csv_writer.writerow(['Index', 'Position_before', 'Position', 'Statement'])  # Write header
            for i in range(3000):
                try:
                    position_before, position, statement = read_PISA(i)
                    csv_writer.writerow([i, position_before, position, statement])  # Write each result immediately
                except (ValueError, FileNotFoundError) as e:
                    print(f"Error processing PISA {i}: {e}")

PISA_DATA_CACHE = None

def load_pisa_data():
    global PISA_DATA_CACHE
    if PISA_DATA_CACHE is not None:
        return PISA_DATA_CACHE
    data = {}
    PISA_AT = {}
    csv_file_path = "data/pisa_test.csv"
    # Check if the CSV file exists
    if not os.path.isfile(csv_file_path):
        print(f"{csv_file_path} not found. Running preprocess_PISA...")
        preprocess_PISA("127.0.0.1:6666")

    with open(csv_file_path, 'r', encoding='utf-8') as csvfile:
        csv_reader = csv.reader(csvfile)
        next(csv_reader)  # Skip the header
        for row in csv_reader:
            index, pos_spec, pos_proof, statement = row
            pos_spec = Position.from_s(pos_spec)
            pos_proof = Position.from_s(pos_proof)
            data[int(index)] = (pos_spec, pos_proof, statement)
            PISA_AT[(pos_spec.file, pos_spec.line)] = int(index)
    PISA_DATA_CACHE = (data, PISA_AT)
    return PISA_DATA_CACHE

#ISAR_PROOFS = SqliteDict('isar_proofs.db')
#ISAR_PROOF_LEN = len(ISAR_PROOFS)

_ISAR_PROOF_INDEX_CACHE = None

def load_ISAR_PROOF_INDEX():
    global _ISAR_PROOF_INDEX_CACHE
    if _ISAR_PROOF_INDEX_CACHE is not None:
        return _ISAR_PROOF_INDEX_CACHE
    indexes = {}
    if os.path.isfile('cache/isar_proofs.idx'):
        with open('cache/isar_proofs.idx', 'r', encoding='utf-8') as f:
            for line in f:
                file, line, column, prf_line, prf_column = line.split(':')
                indexes[Position(int(line), int(column), file)] = Position(int(prf_line), int(prf_column), file)
        _ISAR_PROOF_INDEX_CACHE = indexes
        return _ISAR_PROOF_INDEX_CACHE
    else:
        with SqliteDict('./data/translation/results.db') as db:
            logging.info(f"Loading Isar proof index")
            for key, value in db.items():
                match key.split(':'):
                    case (file,line,'origin'):
                        (origin, _, proof_pos, spec_column) = value
                        spec_pos = Position(int(line), spec_column, file)
                        indexes[spec_pos] = Position.from_s(proof_pos)
        with open('cache/isar_proofs.idx', 'w', encoding='utf-8') as f:
            for pos, proof_pos in indexes.items():
                f.write(f"{pos.file}:{pos.line}:{pos.column}:{proof_pos.line}:{proof_pos.column}\n")
    _ISAR_PROOF_INDEX_CACHE = indexes
    return indexes

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
        with open('data/miniF2F_validation.json', 'w', encoding='utf-8') as f:
            json.dump(validate_set, f, ensure_ascii=False, indent=4)
        with open('data/miniF2F_test.json', 'w', encoding='utf-8') as f:
            json.dump(test_set, f, ensure_ascii=False, indent=4)

if not os.path.isfile('data/miniF2F_validation.json') or not os.path.isfile('data/miniF2F_test.json'):
    preprocess_MiniF2F("127.0.0.1:6666")

_MINIF2F_VALIDATION = None
_MINIF2F_TEST = None

def get_MINIF2F_VALIDATION():
    global _MINIF2F_VALIDATION
    if _MINIF2F_VALIDATION is None:
        with open('data/miniF2F_validation.json', 'r', encoding='utf-8') as f:
            _MINIF2F_VALIDATION = json.load(f)
    return _MINIF2F_VALIDATION

def get_MINIF2F_TEST():
    global _MINIF2F_TEST
    if _MINIF2F_TEST is None:
        with open('data/miniF2F_test.json', 'r', encoding='utf-8') as f:
            _MINIF2F_TEST = json.load(f)
    return _MINIF2F_TEST


class CaseNotAvailable(Exception):
    """Exception raised when an evaluation case is not available."""
    def __init__(self, idx, message="The requested evaluation case is not available"):
        self.idx = idx
        self.message = message
        super().__init__(self.message)

class Data:

    def index_type(self) -> type:
        raise NotImplementedError("index_type must be implemented by subclass")

    def all_cases(self): # -> enumerate[Index]:
        raise NotImplementedError("all_cases must be implemented by subclass")
    
    def is_available(self, index) -> bool:
        return index in self.all_cases()

    def goal_of(self, index) -> str:
        raise NotImplementedError("goal_of must be implemented by subclass")

    def prelude_of(self, index, dep_depth=1, use_proofs=False, use_comments=True, maxsize=None):
        """
        @param file: the path to the theory file
        @param dep_depth: if the prelude shall include the declarations of the dependencies of the theory,
            `dep_depth` indicates the generation of the dependencies to include.
            For example, `dep_depth=1` means the immediate dependencies of the theory;
            `dep_depth=2` means the immediate dependencies and the dependencies of the immediate dependencies;
            `dep_depth=None` means no dependencies shall be included.
        @param use_proofs:
            Set `use_proofs` to 'isar' to use Isar proofs;
            Set `use_proofs` to 'isar-SH*' to use isar-SH* proofs (isar-SH* is the thor-style Isar based on an improved Sledgehammer);
            Set `use_proofs` to 'minilang' to use minilang proofs.
            Set `use_proofs` to False to not use any proofs.
        """
        raise NotImplementedError("prelude_of must be implemented by subclass")

    def proof_of(self, index, lang : str, comments = True) -> str:
        raise NotImplementedError("proof_of must be implemented by subclass")

class PISA_Data(Data):
    def __init__(self):
        self.db = SqliteDict('./data/translation/results.db')

    def close(self):
        self.db.close()

    def __exit__(self, exc_type, exc_value, traceback):
        self.close()
    
    def __enter__(self):
        return self

    def index_type(self) -> type:
        return int

    def all_cases(self): # -> enumerate[Index]:
        PISA_DATA, PISA_AT = load_pisa_data()
        return PISA_DATA.keys()
    
    def goal_of(self, index : int) -> str:
        PISA_DATA, PISA_AT = load_pisa_data()
        try:
            (_, _, goal) = PISA_DATA[index]
            return goal
        except KeyError:
            raise CaseNotAvailable(index)

    def context_of(self, index : int, pp : str = 'typed-nv_pretty') -> str:
        pos = self.goal_pos_of(index)
        ret = proof_context.get_context(pos.file, pos.line)
        if ret is None:
            print(pos)
        return ret

    def premise_of(self, index : int, pp : str, method : str) -> list[str]:
        pos = self.goal_pos_of(index)
        return premise_selection.premise_of(method, pp, pos.file, pos.line)

    def prelude_of(self, index : int, dep_depth=None, use_proofs=False, use_comments=True, maxsize=None, length_of=len, camlize=False):
        pos = self.goal_pos_of(index)
        return prelude_of(pos.file, pos.line, dep_depth, use_proofs, use_comments, maxsize, length_of, camlize)

    def prelude_of(self, index : int, dep_depth=1, use_proofs=False, use_comments=True, maxsize=None, length_of=len, camlize=False) -> str:
        PISA_DATA, PISA_AT = load_pisa_data()
        try:
            (pos_spec, _, _) = PISA_DATA[index]
            return prelude_of(pos_spec.file, pos_spec.line, dep_depth, use_proofs, use_comments, maxsize, length_of, camlize)
        except KeyError:
            raise CaseNotAvailable(index)

    def goal_pos_of(self, index : int) -> Position:
        PISA_DATA, PISA_AT = load_pisa_data()
        try:
            (pos_spec, _, _) = PISA_DATA[index]
            return pos_spec
        except KeyError:
            raise CaseNotAvailable(index)

    def proof_pos_of(self, index : int) -> Position:
        PISA_DATA, PISA_AT = load_pisa_data()
        try:
            (_, pos_proof, _) = PISA_DATA[index]
            return pos_proof
        except KeyError:
            raise CaseNotAvailable(index)
    
    def proof_of(self, index : int, lang : str, comments = True, camlize = False) -> str:
        language.chk_lang_supported(lang)
        try:
            pos_spec = self.goal_pos_of(index)
            (proof, err, _, _) = self.db[f"{pos_spec.file}:{pos_spec.line}:{lang}"]
            if err:
                raise CaseNotAvailable(index)
            if not comments:
                proof = language.remove_comments(proof)
            if camlize and language.is_minilang(lang):
                proof = language.camlize_minilang(proof)
            return proof
        except KeyError:
            raise CaseNotAvailable(index)

_AFP_CASES_CACHE = None

def _load_AFP_CASES_CACHE():
    global _AFP_CASES_CACHE
    if _AFP_CASES_CACHE is not None:
        return _AFP_CASES_CACHE
    if os.path.isfile('cache/afp_proofs.idx'):
        with open('cache/afp_proofs.idx', 'r', encoding='utf-8') as f:
            _AFP_CASES_CACHE = {Position.from_s(line.strip()) for line in f}
            return _AFP_CASES_CACHE
    PISA_DATA, _ = load_pisa_data()
    s = set(load_ISAR_PROOF_INDEX().keys())
    for _, (pos_spec, pos_proof, statement) in PISA_DATA.items():
        if pos_spec not in s:
            logging.warning(f"PISA {pos_spec} not in ISAR proof index")
        s.discard(pos_spec)
    _AFP_CASES_CACHE = s
    with open('cache/afp_proofs.idx', 'w', encoding='utf-8') as f:
        for pos in _AFP_CASES_CACHE:
            f.write(f"{pos.file}:{pos.line}\n")
    return _AFP_CASES_CACHE 

class AFP_Data(Data):
    def __init__(self):
        self.db = SqliteDict('./data/translation/results.db')
        self._all_cases = _load_AFP_CASES_CACHE()

    def close(self):
        self.db.close()

    def __exit__(self, exc_type, exc_value, traceback):
        self.close()
    
    def __enter__(self):
        return self

    def index_type(self) -> type:
        return Position
    
    def all_cases(self) -> set[Position]:
        return self._all_cases

    def goal_of(self, index : Position) -> str:
        try:
            (goal, _, _, _) = self.db[f"{index.file}:{index.line}:goal"]
            return goal
        except KeyError:
            raise CaseNotAvailable(index)

    def premise_of(self, index : Position, pp : str, method : str) -> list[str]:
        return premise_selection.premise_of(method, pp, index.file, index.line)

    def context_of(self, index : Position, pp : str = 'typed-nv_pretty') -> str:
        return proof_context.get_context(index.file, index.line, pp)

    def prelude_of(self, index : Position, dep_depth=None, use_proofs=False, use_comments=True, maxsize=None, length_of=len, camlize=False):
        return prelude_of(index.file, index.line, dep_depth, use_proofs, use_comments, maxsize, length_of, camlize)

    def goal_pos_of(self, index : Position):
        return index

    def proof_pos_of(self, index : Position):
        try:
            return load_ISAR_PROOF_INDEX()[index]
        except KeyError:
            raise CaseNotAvailable(index)
    
    def proof_of(self, index : Position, lang : str, comments = True, camlize = False) -> str:
        language.chk_lang_supported(lang)
        try:
            (proof, err, _, _) = self.db[f"{index.file}:{index.line}:{lang}"]
            if err:
                raise CaseNotAvailable(index)
            if not comments:
                proof = language.remove_comments(proof)
            if camlize and language.is_minilang(lang):
                proof = language.camlize_minilang(proof)
            return proof
        except KeyError:
            raise CaseNotAvailable(index)

class MiniF2F_Data(Data):
    def index_type(self) -> type:
        return Tuple[str, str]
    
    def all_cases(self): # -> enumerate[Index]:
        validation = get_MINIF2F_VALIDATION().keys()
        test = get_MINIF2F_TEST().keys()
        return {('valid', idx) for idx in validation} | {('test', idx) for idx in test}
    
    def goal_of(self, index) -> str:
        raise NotImplementedError("TODO")
    
    def prelude_of(self, index, dep_depth=None, use_proofs=False, use_comments=True, maxsize=None, camlize=False):
        if dep_depth is not None:
            raise ValueError("dep_depth must be None. MiniF2F does not support dependency depth")
        if use_proofs:
            raise ValueError("use_proofs must be False. MiniF2F does not support proofs")
        if maxsize is not None:
            raise ValueError("maxsize must be None. MiniF2F does not support maxsize")
        raise NotImplementedError("TODO")

def get_data_class(data_source):
    if data_source.lower() == "afp":
        return AFP_Data
    elif data_source.lower() == "pisa":
        return PISA_Data
    else:
        logging.error(f"Invalid data source: {data_source}. Using AFP_Data as default.")
        return AFP_Data
