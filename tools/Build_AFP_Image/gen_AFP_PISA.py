import os
import csv
from IsaREPL import Client

with open('./tools/Build_AFP_Image/AFP-DEP1/all_theories.lst', 'r') as f:
    existing_theories = [line.strip() for line in f.readlines()]

repl = Client('127.0.0.1:6666', 'HOL')

TARGETS = set()
SESSIONS = set()

with open('./data/pisa_test.csv', 'r') as f:
    csv_reader = csv.reader(f)
    next(csv_reader)
    for row in csv_reader:
        file = os.path.abspath(row[1].split(':')[0])
        file_name = os.path.splitext(file.split('/')[-1])[0]
        session = repl.session_name_of(file)
        theory = f"{session}.{file_name}"
        if theory not in existing_theories:
            TARGETS.add(theory)
            SESSIONS.add(session)
            print(f"{theory} is not in AFP-DEP1")

os.makedirs('./tools/Build_AFP_Image/AFP-DEP1/AFP-1-PISA', exist_ok=True)
with open('./tools/Build_AFP_Image/AFP-DEP1/AFP-1-PISA/ROOT', 'w') as f:
    f.write("""session "AFP-1-PISA" = "AFP-DEP1-19" +\n sessions\n""")
    for session in SESSIONS:
        f.write(f"""  "{session}"\n""")
    f.write("""theories\n""")
    for target in TARGETS:
        f.write(f"""  "{target}"\n""")

with open('./tools/Build_AFP_Image/AFP-DEP1/AFP-1-PISA/all_theories.lst', 'w') as f:
    for target in TARGETS:
        f.write(f"{target}\n")

repl.close()

