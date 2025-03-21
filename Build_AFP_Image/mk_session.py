with open('./Build_AFP_Image/dep1_sessions', 'r') as f:
    lines = f.readlines()
with open('./Build_AFP_Image/dep1_theories', 'r') as f:
    theories = f.readlines()

SESSIONS = '\n'.join(['"' + line.strip() + '"' for line in lines])
THEORIES = '\n'.join(['"' + line.strip() + '"' for line in theories])
ROOT = f"""
session "AFP-DEP1" = HOL +
    sessions
{SESSIONS}
    theories
{THEORIES}
"""
with open('./Build_AFP_Image/AFP-DEP1/ROOT', 'w') as f:
    f.write(ROOT)
