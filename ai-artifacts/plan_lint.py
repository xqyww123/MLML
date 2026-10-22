"""Check-only lint for a plan file (round-30 relaxation R5): every per-round bullet in sections 10
and 11 (a line starting `- **第N轮`) must end with its own closing marker `（第N轮条止）`, no other
round's marker may appear inside it, and no round header may appear before the previous bullet's
marker.  Reports only; never rewrites (CLAUDE.md forbids scripted edits to plan documents).
Usage: python3 plan_lint.py LIGHT_LOCALE_PLAN_REVnn.md"""
import re, sys
lines = open(sys.argv[1], encoding='utf-8').read().split('\n')
HEADER = re.compile(r'^- \*\*第([一二三四五六七八九十]+)轮')
MARKER = re.compile(r'（第([一二三四五六七八九十]+)轮条止）')
problems = []
h, rnd = None, None
def close(end):
    """`end` is the 1-based number of the bullet's last line."""
    assert h is not None
    last = lines[end - 1]
    m = MARKER.search(last)
    if not m or not last.rstrip().endswith(f'（第{rnd}轮条止）'):
        problems.append(f'line {h}: bullet 第{rnd}轮 does not end with （第{rnd}轮条止） (last line {end})')
    for n in range(h, end):  # markers inside the bullet other than on its last line
        for mm in MARKER.finditer(lines[n - 1]):
            problems.append(f'line {n}: marker （第{mm.group(1)}轮条止） inside bullet 第{rnd}轮 before its end')
for i, line in enumerate(lines, 1):
    m = HEADER.match(line)
    if m:
        if h: close(i - 1)
        h, rnd = i, m.group(1)
    elif h and re.match(r'^(- |#|$)', line):
        close(i - 1); h = None
if h: close(len(lines))
# Advisory notes (round-31 relaxation R10), sections 0-9 only (everything before the "## 10." heading):
# (a) a numeral that merely counts enumerated callers/users/readers/uses; (b) an R-label with no
# round (第N轮) in the same clause.  They are reported, never rewritten, and do not affect the exit code.
notes = []
end_body = next((i for i, l in enumerate(lines, 1) if re.match(r'^## 10\.', l)), len(lines) + 1)
COUNT = re.compile(r'(调用者|使用者|读者|用途)有?[一二三四五六七八九十两]+(处|个|条)')
RLABEL = re.compile(r'(?<![A-Za-z0-9_`])R\d+(?!\d)')
# (c)-(e) reserved terms (round-36 relaxation R3): a bare 联合检查 (not 逐位置联合检查) should mean only
# stock's :429 check; 副本 should be followed by 1 or 2; a class count next to 载体/候选 is barred by R9.
BARE_JOINT = re.compile(r'(?<!逐位置)联合检查')
COPY = re.compile(r'那份副本|步的副本|定义体的副本')  # the §3.2 sense; 局部副本/theory 层副本 are ordinary uses
CLASS_COUNT = re.compile(r'(载体|候选)[^。；]{0,12}?[三四五]类|[三四五]类[^。；]{0,12}?(载体|候选)')
for i, line in enumerate(lines[:end_body - 1], 1):
    for m in COUNT.finditer(line):
        notes.append(f'line {i}: counting numeral "{m.group(0)}"')
    for m in RLABEL.finditer(line):
        clause = re.split(r'[；。]', line[max(0, m.start() - 160):m.start()])[-1]
        if '轮' not in clause:
            notes.append(f'line {i}: R-label "{m.group(0)}" without a round in its clause')
    if BARE_JOINT.search(line):
        notes.append(f'line {i}: bare 联合检查 (confirm it means the :429 check)')
    for m in COPY.finditer(line):
        notes.append(f'line {i}: 副本 not followed by 1/2 at col {m.start()}')
    for m in CLASS_COUNT.finditer(line):
        notes.append(f'line {i}: class count "{m.group(0)}"')
# (f) numbering convention (section 11 (31), round 8): the body of the rev 37 plan keeps one line per
# line of the committed baseline, so that every "plan line N" in the leaves and in section 11 stays
# valid -- every hunk against the baseline replaces k lines by k lines at the same position; the
# only pure addition allowed is one block after the baseline's section 11 end.  Check-only.
import os, subprocess
BASELINE, BODY_END = '1ac31973', 7842
if os.path.basename(sys.argv[1]) == 'LIGHT_LOCALE_PLAN_REV37.md':
    path = os.path.abspath(sys.argv[1])
    repo = os.path.dirname(os.path.dirname(path))
    diff = subprocess.run(['git', '-C', repo, 'diff', '--no-color', '--no-ext-diff', '--no-textconv', '-U0',
                           BASELINE, '--', os.path.relpath(path, repo)], capture_output=True, text=True)
    if diff.returncode != 0:
        problems.append('numbering: git diff against ' + BASELINE + ' failed: ' + diff.stderr.strip())
    hunks = re.findall(r'^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@', diff.stdout, re.M)
    if diff.stdout.strip() and not hunks:
        problems.append('numbering: the diff output has no parsable hunk header')
    additions = 0
    for a, k, b, n in hunks:
        a, k, b, n = int(a), int(k or '1'), int(b), int(n or '1')
        # the appended block: either a pure addition after the baseline's last section-11 line, or
        # that last line edited in place together with the block (one merged hunk)
        if a >= BODY_END and (k == 0 and b == a + 1 or k == 1 and b == a):
            additions += 1
            if additions > 1: problems.append(f'numbering: a second addition at baseline line {a}')
        elif a != b or k != n:
            problems.append(f'numbering: hunk -{a},{k} +{b},{n} changes the body line count (baseline {BASELINE})')
for p in problems: print(p)
for n in notes: print('note:', n)
print(f'{len(problems)} problem(s), {len(notes)} note(s)')
sys.exit(1 if problems else 0)
