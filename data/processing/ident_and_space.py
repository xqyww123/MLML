import re
from sqlitedict import SqliteDict

def norm_space(prf):
    
    protected_regions = []
    stack = []
    for match in re.finditer(r'"|\\<open>|\\<close>', prf):
        if len(stack) == 0:
            match match.group(0):
                case '"':
                    stack.append((0, match.start()))
                case '\\<open>':
                    stack.append((1, match.start()))
                case '\\<close>':
                    print("error: \\<close> outside of \\<open>")
                    exit(1)
        else:
            match match.group(0):
                case '"':
                    head, pos = stack[-1]
                    if head == 0:
                        stack.pop()
                        if len(stack) == 0:
                            protected_regions.append((pos, match.end()))
                    else:
                        stack.append((0, match.start()))
                case '\\<open>':
                    stack.append((1, match.start()))
                case '\\<close>':
                    while len(stack) > 0 and stack[-1][0] == 0:
                        stack.pop()
                    if len(stack) == 0:
                        print("error: \\<close> outside of \\<open>")
                        exit(1)
                    else:
                        _, pos = stack.pop()
                        if len(stack) == 0:
                            protected_regions.append((pos, match.end()))
    
    # Process the string in parts, skipping protected regions
    result = []
    last_end = 0
    modified = False
    
    for start, end in protected_regions:
        # Process unprotected part
        if start > last_end:
            unprotected = prf[last_end:start]
            # Apply whitespace normalizations to unprotected parts
            new_unprotected = re.sub(r'\s*\[ ', '[', unprotected)
            new_unprotected = re.sub(r'\s*\(\s+', '(', new_unprotected)
            new_unprotected = re.sub(r'(\d) , (\d)', r'\1,\2', new_unprotected)
            new_unprotected = re.sub(r'(\d) , (\d)', r'\1,\2', new_unprotected)
            new_unprotected = re.sub(r'\s+,', ',', new_unprotected)
            new_unprotected = re.sub(r'(\d) \- ', r'\1-', new_unprotected)
            new_unprotected = re.sub(r'\s+\]', ']', new_unprotected)
            new_unprotected = re.sub(r'\s+\)', ')', new_unprotected)
            
            if new_unprotected != unprotected:
                modified = True
            
            result.append(new_unprotected)
        
        # Add the protected part unchanged
        result.append(prf[start:end])
        last_end = end
    
    # Process any remaining unprotected part after the last protected region
    if last_end < len(prf):
        unprotected = prf[last_end:]
        new_unprotected = re.sub(r'\s*\[ ', '[', unprotected)
        new_unprotected = re.sub(r'\s*\(\s+', '(', new_unprotected)
        new_unprotected = re.sub(r'(\d) , (\d)', r'\1,\2', new_unprotected)
        new_unprotected = re.sub(r'(\d) , (\d)', r'\1,\2', new_unprotected)
        new_unprotected = re.sub(r'\s+,', ',', new_unprotected)
        new_unprotected = re.sub(r'(\d) - ', r'\1-', new_unprotected)
        new_unprotected = re.sub(r'\s+\]', ']', new_unprotected)
        new_unprotected = re.sub(r'\s+\)', ')', new_unprotected)
        
        if new_unprotected != unprotected:
            modified = True
        
        result.append(new_unprotected)
    
    if modified:
        return (modified, ''.join(result))
    else:
        return (modified, prf)

INDENT = {
    'next': (0, -2),
    'have': (2, 0),
    'hence': (2, 0),
    'show': (2, 0),
    'thus': (2, 0),
    'consider': (2, 0),
    'obtain': (2, 0),
    'subgoal': (2, 0),
}

def mk_indent(lines):
    indent = 0
    persistent_indent = 0
    new_lines = []
    prefix = ''
    for line in lines:
        # Get the first word of the line
        pat = re.search(r'[a-z]+', line)
        if not pat:
            new_lines.append(line)
            match line.strip():
                case '{':
                    first_word = '{'
                case '}':
                    first_word = '}'
                case _:
                    continue
        else:
            first_word = pat.group(0)
        if first_word in ['from', 'with', 'then', 'ultimately', 'also', 'moreover', 'finally']:
            prefix += line + ' '
            continue
        match first_word:
            case 'proof':
                persistent_indent += 2
                indent = 0
                i2 = -2
            case 'qed':
                persistent_indent = max(0, persistent_indent - 2)
                indent = 0
                i2 = 0
            case '{':
                indent = 0
                i2 = 0
            case '}':
                indent = 0
                i2 = 0
            case _:
                try:
                    _, i2 = INDENT[first_word]
                    indent = 0
                except KeyError:
                    i2 = 0
        is_comment = line.strip().startswith('(*')
        new_line = ' ' * (persistent_indent + indent + i2) + (prefix if not is_comment else '') + line
        if not is_comment:
            prefix = ''
        try:
            i1, _ = INDENT[first_word]
            indent = i1
        except KeyError:
            pass
        new_lines.append(new_line)
    if persistent_indent != 0:
        print(f"indent is not 0: {lines}")
    return new_lines

def norm_prf(prf):
    lines = prf.split('\n')
    new_lines = []
    modified = False
    for line in lines:
        # if line.strip().startswith('by (auto_sledgehammer'):
        if line.strip().startswith('END') or line.strip().startswith('NEXT'):
            (m, new_line) = norm_space(line)
        else:
            (m, new_line) = (False, line)
        new_lines.append(new_line)
        modified = modified or m
    if modified:
        return (modified, '\n'.join(new_lines))
    else:
        return (modified, prf)

def remove_auto2():
    bad_keys = []
    bad_count = 0
    total = 0
    with SqliteDict('cache/translation/results.db') as db:
        for key, value in db.items():
            match key.split(':'):
                case (_, _, cat):
                    if cat in ['goal']:
                        continue
                    (prf, err, _) = value
                    if err:
                        continue
                    if ('@proof' in prf or '@qed' in prf or '@have' in prf):
                        bad_keys.append(key)
                        bad_count += 1
                    total += 1
                    if total % 1000 == 0:
                        print(f"{bad_count / total:.2%}")
        print(f"{bad_count / total:.2%}")
        for key in bad_keys:
            del db[key]
        db.commit()

def normalize_space():
    total = 0
    count = 0
    to_modify = []
    with SqliteDict('cache/translation/results.db') as db:
        for key, value in db.items():
            match key.split(':'):
                case (_, _, cat):
                    if cat in ['goal']:
                        continue
                    (prf, err, pos) = value
                    if err:
                        continue
                    (modified, prf) = norm_prf(prf)
                    if modified:
                        count += 1
                        to_modify.append((key, (prf, err, pos)))
                    total += 1
                    if total % 1000 == 0:
                        print(f"{count / total:.2%}")
        for key, value in to_modify:
            db[key] = value
        db.commit()
    print(f"{count / total:.2%}")


def press_dots(lines):
    """
    If a line is just a single '.' or '..', append it to the previous line.
    """
    result = []
    i = 0
    while i < len(lines):
        if i > 0 and lines[i].strip() in ['.', '..']:
            # Append the '.' or '..' to the previous line
            result[-1] += ' ' + lines[i].strip()
        else:
            result.append(lines[i])
        i += 1
    return result

def make_indent():
    to_modify = {}
    with SqliteDict('cache/translation/results.db') as db:
        total = 0
        for key, value in db.items():
            match key.split(':'):
                case (file, line, 'origin'):
                    (prf, err, pos) = value
                    if err:
                        continue
                    lines = prf.split('\n')
                    lines = press_dots(lines)
                    lines = mk_indent(lines)
                    prf = '\n'.join(lines)
                    to_modify[key] = (prf, err, pos)
                    total += 1
                    if total % 10000 == 0:
                        print(f"{total}")
        total = 0
        for key, value in to_modify.items():
            db[key] = value
            total += 1
            if total % 100 == 0:
                db.commit()
                print(f"{total}")
        db.commit()

def clean():
    count = 0
    with SqliteDict('cache/translation/results.db') as db:
        for key in db:
            match key.split(':'):
                case (file, line, 'isar-SH*-idt'):
                    del db[key]
                    count += 1
                    if count % 100 == 0:
                        print(f"{count}")
    db.commit()

def copy():
    count = 0
    to_add = {}
    with SqliteDict('cache/translation/results.db') as db:
        for key, value in db.items():
            match key.split(':'):
                case (file, line, 'origin'):
                    to_add[f"{file}:{line}:origin-noindent"] = value
                    count += 1
                    if count % 100 == 0:
                        print(f"{count}")
        count = 0
        for key, value in to_add.items():
            db[key] = value
            count += 1
            if count % 100 == 0:
                db.commit()
                print(f"{count}")
        db.commit()

def norm_question_mark():
    total = 0
    count = 0
    to_modify = {}
    with SqliteDict('cache/translation/results.db') as db:
        for key, value in db.items():
            (prf, err, pos) = value
            if err:
                continue
            prf2 = prf.replace('show?', 'show ?').replace('thus?', 'thus ?').replace('by(', 'by (').replace('apply(', 'apply (')
            if prf2 != prf:
                count += 1
                to_modify[key] = (prf2, err, pos)
            total += 1
            if total % 1000 == 0:
                print(f"{count / total:.2%}, {total}")
        total = 0
        for key, value in to_modify.items():
            db[key] = value
            total += 1
            if total % 100 == 0:
                db.commit()
                print(f"{total}")
        db.commit()
    print(f"{total}")

def norm_spaces_inside():
    total = 0
    count = 0
    to_modify = {}
    with SqliteDict('cache/translation/results.db') as db:
        for key, value in db.items():
            _,_,cat = key.split(':')
            #if cat not in ['origin', 'origin-noindent', 'isar-SH*-noindent', 'isar-SH*']:
            #    continue
            (prf, err, pos) = value
            if err:
                continue
            lines = prf.split('\n')
            new_lines = []
            for line in lines:
                indent = len(line) - len(line.lstrip(' '))
                line = re.sub(r'\s+', ' ', line)
                line = ' ' * indent + line
                new_lines.append(line)
            new_prf = '\n'.join(new_lines)
            if new_prf != prf:
                count += 1
                to_modify[key] = (new_prf, err, pos)
            total += 1
            if total % 1000 == 0:
                print(f"{count / total:.2%}, {total}")
        #total = 0
        #for key, value in to_modify.items():
        #    db[key] = value
        #    total += 1
        #    if total % 100 == 0:
        #        db.commit()
        #        print(f"{total}")
        #db.commit()

        print(f"{count / total:.2%}, {count}, {total}")

norm_spaces_inside()
exit(1)

def data_processing():
    remove_auto2()
    normalize_space()
    make_indent()

make_indent()