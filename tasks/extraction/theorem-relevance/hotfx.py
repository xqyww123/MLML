from sqlitedict import SqliteDict, decode
import re
import sqlite3
        
def fix_datatype(code : str) -> str:
    # code has a format like:
    # datatype ?'a::type list = Nil | Cons \<open>hd: ?'a::type\<close> \<open>tl: ?'a::type list\<close>          mapper: \<open>list.map\<close> predicate: \<open>list_all\<close> relation: \<open>list_all2\<close> set: \<open>set\<close>
    # 从头开始扫描 code，找到第一个 '='，然后获得其位置前最近的单词（如上述例子中输出 'list'）
    code = code.split('          ')[0]
    # eq_pos = code.find('=')
    # if eq_pos == -1:
    #     raise ValueError("No '=' found in the code")
    # # 向前找到等号前的部分
    # before_eq = code[:eq_pos]
    # # 以空白为分隔，找到最后一个单词
    # import re
    # words = re.findall(r'\b\w+\b', before_eq)
    # if words:
    #     datatype_name = words[-1]
    # else:
    #     raise ValueError("No word found in the code before '='")
    #     # 从后往前扫描 code，找到最后一个 predicate: \<open>...\<close> 并替换 ... 为 pred_{datatype_name}
    # # 使用正则在字符串中查找所有 match
    # # Match literal backslash before <open> and <close> (\\<open> in raw string matches \<open> in actual string)
    # predicate_matches = list(re.finditer(r'predicate: \\<open>(.*?)\\<close>', code))
    # if predicate_matches:
    #     last_predicate = predicate_matches[-1]
    #     start, end = last_predicate.span(1)
    #     code = code[:start] + f'pred_{datatype_name}' + code[end:]
    
    code = re.sub(r'\\<open>un_.*?: ', r'\\<open>', code)
    #code = code.replace('::type', '')
    return code

def constant_of_fact(fact : str) -> str:
    # Find the position of the first '=' or '<equiv>' or '<longleftrightarrow>' in the fact string
    # 从头开始找到 <open> 的结束位置
    open_pos = fact.find(r'\<open>')
    if open_pos == -1:
        raise ValueError("No '\\<open>' found in the fact")
    open_pos += len(r'\<open>')

    equal_pos = fact.find('=')
    equiv_pos = fact.find(r'\<equiv>')
    longleftrightarrow_pos = fact.find(r'\<longleftrightarrow>')

    # Prepare a list of found positions (ignoring those not found)
    positions = [pos for pos in [equal_pos, equiv_pos, longleftrightarrow_pos] if pos != -1]
    if positions:
        eq_pos = min(positions)
    else:
        eq_pos = len(fact)
    longrightarrow_pos = fact.rfind(r'\<Longrightarrow>', open_pos, eq_pos)
    qualifier_pos = fact.rfind(r'. ', open_pos, eq_pos)
    pos = open_pos
    if longrightarrow_pos >= pos:
        pos = longrightarrow_pos + len(r'\<Longrightarrow>')
    if qualifier_pos >= pos:
        pos = qualifier_pos + len('. ')
    # 从 pos 开始寻找第一个单词
    match = re.search(r'\b\w+\b', fact[pos:eq_pos])
    if not match:
        return ''
    constant = match.group(0)
    return constant

def fix_fact(fact : str) -> str:
    return fact
    #return fact.replace('::type', '')

def fix_ctxt(ctxt, bodies):
    cmds = [cmd for cmd in ctxt.split("\n\n\n") if cmd]
    def m(cmd : str) -> tuple[int, str]:
        if cmd.startswith('notation '):
            return (0, cmd)
        elif cmd.startswith('class '):
            return (1, cmd)
        elif cmd.startswith('datatype'):
            return (2, fix_datatype(cmd))
        elif cmd.startswith('fact '):
            head = constant_of_fact(cmd)
            cmd = fix_fact(cmd)
            if head == '':
                return (3, cmd)
            found_in_bodies = any(re.search(r'\b{}\b'.format(re.escape(head)), body) for body in bodies)
            if found_in_bodies:
                return (3, cmd)
            else:
                return (4, cmd)
        else:
            return (2, cmd)
    cmds = [m(cmd) for cmd in cmds]
    cmds.sort(key=lambda x: x[0])
    cmds = [cmd for _, cmd in cmds]
    return "\n\n\n".join(cmds + [''])

import re
from io import StringIO

def remove_type_annot(code : str) -> str:
    # Use re.split with capturing group to split by delimiters while keeping them
    # This way, "other words" are everything between delimiters (including single ':')
    pattern = r'(::|\\<open>|\\<close>|,|\(|\)|\[|\]|;|. |{|})'
    tokens = re.split(pattern, code)
    ret = StringIO()
    #typ = StringIO()
    stack = []
    mode = True
    def write(token):
        nonlocal mode
        if mode:
            ret.write(token)
        else:
            pass
            #typ.write(token)
    for token in tokens:
        match token:
            case '(' | '\\<open>' | '[' | '{':
                stack.append(token)
                write(token)
            case '::':
                if mode:
                    stack.append(token)
                    mode = False
                else:
                    pass
                    #typ.write(token)
            case ')' | '\\<close>' | ']' | '}':
                while True:
                    last = stack.pop()
                    match last:
                        case '(' | '\\<open>' | '[' | '{':
                            break
                            # if (token == ')' and last == '(') or (token == '\\<close>' and last == '\\<open>'):
                            #     break
                            # else:
                            #     raise ValueError(f"Cannot remote type annotation: {last} != {token}")
                        case '::':
                            mode = True
                        case _:
                            raise ValueError(f"BUG remove_type_annot 01")
                write(token)
            case ',' | ';' | '. ':
                if len(stack) > 0:
                    last = stack[-1]
                    match last:
                        case '(' | '\\<open>' | '[' | '{':
                            pass
                        case '::':
                            stack.pop()
                            mode = True
                        case _:
                            raise ValueError(f"BUG remove_type_annot 02")
                write(token)
            case _:
                write(token)
    code2 = ret.getvalue()
    ret.close()
    return code2

db_conn = sqlite3.connect('data/premise_relevance.db')
db_cursor = db_conn.cursor()
db_cursor.execute('SELECT COUNT(*) FROM "unnamed"')
TOTAL = db_cursor.fetchone()[0]

with SqliteDict('data/premise_relevance.fix.db') as db:
    db_cursor.execute('SELECT key, value FROM "unnamed" ORDER BY RANDOM() LIMIT 100')
    for i, (key, value) in enumerate(db_cursor):
        value = decode(value)
        fixed_value = []
        for goal, (ctxt, prems, goal_acs) in value:
            hyps, concl = goal
            #ctxt = fix_ctxt(ctxt, hyps + [concl])
            concl = remove_type_annot(concl)
            fixed_value.append((goal, (ctxt, prems, goal_acs)))
        #db[key] = fixed_value
        if i % 1000 == 0:
            print(f"Processed {i} keys {TOTAL}")
            #db.commit()
    #db.commit()
db_conn.close()

db_conn = sqlite3.connect('data/premise_info.db')
db_cursor = db_conn.cursor()
db_cursor.execute('SELECT COUNT(*) FROM "unnamed"')
TOTAL = db_cursor.fetchone()[0]

with SqliteDict('data/premise_info.fix.db') as db:
    db_cursor.execute('SELECT key, value FROM "unnamed"')
    for i, (key, value) in enumerate(db_cursor):
        ctxt, acs = decode(value)
        ctxt = fix_ctxt(ctxt, [key])
        db[key] = (ctxt, acs)
        if i % 1000 == 0:
            print(f"Processed {i} keys {TOTAL}")
            db.commit()
    db.commit()
db_conn.close()
