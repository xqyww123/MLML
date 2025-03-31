from sqlitedict import SqliteDict
import os
import logging
import json
from IsaREPL import Client, Position, REPLFail
import csv
import sys

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

def deps_of(thy):
    try:
        return THEORIES[thy]['deps']
    except KeyError:
        return []

def session_of(thy):
    return '.'.join(thy.split('.')[:-1])

def short_name_of(thy):
    return thy.split('.')[-1]

def all_deps_of(thy, ret=set()):
    for dep in deps_of(thy):
        if dep not in ret:
            ret.add(dep)
            ret.update(all_deps_of(dep, ret))
    return ret

def all_theories_in_session(session_name):
    ret = set()
    try:
        thys = SESSIONS[session_name]['theories']
    except KeyError:
        thys = SESSIONS[session_name]
    for thy in thys:
        ret.add(thy)
        ret.update(all_deps_of(thy))
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
    with open('cache/sorted_thy.txt', 'w') as f:
        for thy in sorted_thy:
            f.write(f"{thy}\n")

if not os.path.exists('cache/sorted_thy.txt'):
    logging.info('Topological sorting of theories')
    topological_sort()

with open('cache/sorted_thy.txt', 'r') as f:
    SORTED_THY = f.read().splitlines()

def collect_declarations():
    declarations = {}
    with SqliteDict('./cache/translation/declarations.db') as db:
        for key, command in db.items():
            match key.split(':'):
                case (file,line,ofs):
                    # this `ofs` is the offset in the entire file stream, instead of the line.
                    if file not in declarations:
                        declarations[file] = []
                    declarations[file].append((int(line), int(ofs), command))
    declarations = {k: sorted(v, key=lambda x: x[1]) for k, v in declarations.items()}
    with open('cache/declarations.json', 'w') as f:
        json.dump(declarations, f)

if not os.path.exists('cache/declarations.json'):
    logging.info('Collecting declarations')
    collect_declarations()

with open('cache/declarations.json', 'r') as f:
    DECLARATIONS = json.load(f)


def prelude_of(file, line):
    prelude0 = []
    try:
        prelude0 = [x[2] for x in DECLARATIONS[file] if x[0] < line]
    except KeyError:
        pass
    dep_thys = set()
    try:
        thys = THEORIES_IN_FILE[file]
    except KeyError:
        thys = []
    for thy in thys:
        try:
            dep_thys.update(deps_of(thy))
        except KeyError:
            pass
    prelude = []
    for dep in dep_thys:
        try:
            for decl in DECLARATIONS[location_of(dep)]:
                prelude.append(decl[2])
        except KeyError:
            pass
    prelude += prelude0
    return '\n'.join(prelude)


PISA_TEST_PATH="./data/PISA"

def preprocess_PISA(addr):
    with Client(addr, 'HOL') as c:
        def read_PISA(i):
            src_path = PISA_TEST_PATH+'/quick_test_name_'+str(i)+'.json'
            if not os.path.isfile(src_path):
                src_path = PISA_TEST_PATH+'/test_name_'+str(i)+'.json'
            with open(src_path, 'r', encoding='utf-8') as file:
                [[path,lemma]] = json.load(file)
            prefix = "/home/ywu/afp-2021-02-11/"
            if path.startswith(prefix):
                path = "./contrib/afp-2025-02-12/" + path[len(prefix):]
            else:
                raise ValueError(f"PISA {i}: Exceptional JSON format")
            if not os.path.isfile(path):
                raise FileNotFoundError(f"PISA {i}: theory not found: {path}")

            with open(path, 'r', encoding='utf-8') as file:
                commands = c.fast_lex(file.read())

            match_index = -1
            for idx, (_, command) in enumerate(commands):
                common_prefix_length = 0
                while (common_prefix_length < len(command) and
                       common_prefix_length < len(lemma) and
                       command[common_prefix_length] == lemma[common_prefix_length]):
                    common_prefix_length += 1

                # Get the common prefix
                common_prefix = command[:common_prefix_length]

                # Check if it's a qualified prefix
                if common_prefix.startswith('qualified') or common_prefix.startswith('private'):
                    # For qualified prefixes, require at least two spaces
                    if common_prefix_length > 0 and common_prefix.count(' ') >= 2:
                        match_index = idx
                        break
                else:
                    # For non-qualified prefixes, require at least one space
                    if common_prefix_length > 0 and ' ' in common_prefix:
                        match_index = idx
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

def read_pisa_data():
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
    return data, PISA_AT

PISA_DATA, PISA_AT = read_pisa_data()

#ISAR_PROOFS = SqliteDict('isar_proofs.db')
#ISAR_PROOF_LEN = len(ISAR_PROOFS)

def get_ISAR_PROOFS():
    global ISAR_PROOFS_CACHE
    if ISAR_PROOFS_CACHE is not None:
        return ISAR_PROOFS_CACHE
    ISAR_PROOFS = {}
    with SqliteDict('./cache/translation/results.db') as db:
        for key, value in db.items():
            match key.split(':'):
                case (file,line):
                    spec_pos = Position(int(line),0,file)
                    (data, _, proof_pos) = value
                    proof_pos = Position.from_s(proof_pos)
                    ISAR_PROOFS[spec_pos] = (proof_pos, data['goal'], data['origin'])
    ISAR_PROOFS_CACHE = ISAR_PROOFS
    return ISAR_PROOFS

def get_ISAR_TRAINING_DATA():
    global ISAR_TRAINING_DATA_CACHE
    if ISAR_TRAINING_DATA_CACHE is not None:
        return ISAR_TRAINING_DATA_CACHE
    ISAR_PROOFS = get_ISAR_PROOFS()
    ISAR_TRAINING_DATA = {
        spec_pos: (proof_pos, data['goal'], data['origin'])
        for spec_pos, (proof_pos, data, _) in ISAR_PROOFS.items()
        if (spec_pos.file, spec_pos.line) not in PISA_AT
    }
    ISAR_TRAINING_DATA_CACHE = ISAR_TRAINING_DATA
    return ISAR_TRAINING_DATA

def gen_fine_tune_data_isar():
    ISAR_TRAINING_DATA = get_ISAR_TRAINING_DATA()
    count = 0
    with open('cache/fine_tune_data_isar.jsonl', 'w') as f:
        for spec_pos, (proof_pos, spec, proof) in ISAR_TRAINING_DATA.items():
            f.write(json.dumps({'prelude': prelude_of(spec_pos.file, spec_pos.line),
                                'goal': spec,
                                'proof': proof}) + '\n')
            count += 1
    print(f"Generated {count} fine-tune cases in cache/fine_tune_data_isar.jsonl")

if __name__ == '__main__' and len(sys.argv) > 1 and sys.argv[1] == 'fine-tune-isar-data':
    gen_fine_tune_data_isar()
    exit()

def gen_cases():
    ISAR_TRAINING_DATA = get_ISAR_TRAINING_DATA()
    goal_of = {}
    with open('cache/goal_of.txt', 'w') as f:
        for spec_pos, (proof_pos, spec, proof) in ISAR_TRAINING_DATA.items():
            goal_of[(proof_pos.file, proof_pos.line)] = spec
            f.write(f"{proof_pos.file}:{proof_pos.line}:{spec}\n")
    num = 0
    with open('cache/fine_tune_data_minilang.jsonl', 'w') as f:
        with SqliteDict('cache/translation/results.db') as db:
            for key, value in db.items():
                match key.split(':'):
                    case (file,line):
                        try:
                            (data, _, _) = value
                            prelude = prelude_of(file, int(line))
                            num += 1
                            f.write(json.dumps({
                                'prelude': prelude,
                                'goal': data['goal'],
                                'proof': data['refined']
                            }) + '\n')
                        except KeyError:
                            pass
    print(f"Generated {num} cases in cache/fine_tune_data_minilang.jsonl")

if __name__ == '__main__' and len(sys.argv) > 1 and sys.argv[1] == 'fine-tune-minilang-data':
    gen_cases()
    exit()

#def gen_test_cases():
#    num = 0
#    with open('cache/test_data_pisa.jsonl', 'w') as f:
#        for idx, (pos_before, pos, statement) in PISA_DATA.items():
#            num += 1
#            f.write(json.dumps({
#                'index': idx,
#                'prelude': prelude_of(pos.file, pos.line),
#                'goal': statement,
#            }) + '\n')
#    print(f"Generated {num} cases in cache/test_data_pisa.jsonl")
#
#if __name__ == '__main__' and len(sys.argv) > 1 and sys.argv[1] == 'test-pisa':
#    gen_test_cases()
#    exit()
#
