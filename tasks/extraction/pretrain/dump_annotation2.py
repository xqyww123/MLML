#!/usr/bin/env python3
from sqlitedict import SqliteDict
import json
import os
import argparse
from IsaREPL import Client
from data.isabelle import PISA_Data

parser = argparse.ArgumentParser(description='Dump annotations from database')
parser.add_argument('db_path', help='Path to the annotations database file')
parser.add_argument('output_path', help='Path to the output JSONL file')
args = parser.parse_args()

TARGET_PP = 'T2S3'

ANNOTATIONS_CACHE_FILE = args.db_path + '.cache.json'

ANNOTATIONS = {}

data_provider = PISA_Data()
PISA_entries = {}
for i in data_provider.all_cases():
    proof_pos = data_provider.proof_pos_of(i)
    end_pos = data_provider.end_pos_of(i)
    with open(proof_pos.file, 'r', encoding="latin-1") as f:
        contents = f.readlines()
    if proof_pos.file == './contrib/Isabelle2024/src/HOL/Library/Multiset_Order.thy':
        pass
    proof_offset = proof_pos.offset_of(contents)
    end_offset = end_pos.offset_of(contents)
    if proof_pos.file not in PISA_entries:
        PISA_entries[proof_pos.file] = []
    PISA_entries[proof_pos.file].append((proof_offset, end_offset))
for _, value in PISA_entries.items():
    value.sort(key=lambda x: x[0])

# if os.path.exists(ANNOTATIONS_CACHE_FILE):
#     # 从缓存文件读取
#     with open(ANNOTATIONS_CACHE_FILE, 'r') as f:
#         ANNOTATIONS = json.load(f)
# else:
#     print(f"Cache missing, reading from database")
# 从数据库读取并生成缓存
with SqliteDict(args.db_path) as db:
    TOTAL = len(db)
    for i, (key, value) in enumerate(db.items()):
        if i % 1000 == 0:
            print(f"Processed {i} keys {TOTAL}")
        (file, _) = key.split(':')
        (pos_begin, pos_end, pp_code) = value
        if file not in ANNOTATIONS:
            ANNOTATIONS[file] = []
        store = ANNOTATIONS[file]
        store.append((pos_begin, pos_end, pp_code))
# # 保存到缓存文件
# with open(ANNOTATIONS_CACHE_FILE, 'w') as f:
#     json.dump(ANNOTATIONS, f)

def annotate(origin_file_path):
    if origin_file_path not in ANNOTATIONS:
        return None
    annotations = ANNOTATIONS[origin_file_path]
    with open(origin_file_path, 'r', encoding="latin-1") as f:
        content = f.read()
    if origin_file_path in PISA_entries:
        ret = []
        entries = PISA_entries[origin_file_path]
        for begin_offset, end_offset, pp_code in annotations:
            meet = False
            for i, j in entries:
                if not (end_offset < i or j < begin_offset):
                    meet = True
            if not meet:
                ret.append((begin_offset, end_offset, pp_code))
        for i, j in entries:
            ret.append((i, j, 'sorry'))
        annotations = ret
    annotations = sorted(annotations, key=lambda x: -x[0])
    for begin_offset, end_offset, pp_code in annotations:
        indent = 0
        i = begin_offset - 1
        while i >= 0 and content[i] != '\n':
            if content[i] == ' ' or content[i] == '\t':
                indent += 1
            else:
                indent = 0
            i -= 1
        indent_str = ' ' * indent
        if isinstance(pp_code, str):
            code = pp_code
        else:
            code = pp_code[TARGET_PP]
        code_lines = code.split('\n')
        code_lines = [indent_str + line for line in code_lines]
        code_str = '\n'.join(code_lines)
        content = content[:begin_offset] + code_str + content[end_offset+1:]
    return content

import hashlib
TOTAL = len(ANNOTATIONS)
with open(args.output_path, 'w') as f:
    for i, (key, value) in enumerate(ANNOTATIONS.items()):
        if i % 1000 == 0:
            print(f"Processed {i} keys {TOTAL}")
        original_path = key
        if key.startswith("./contrib/"):
            key = key[len("./contrib/"):]
        if key.startswith("afp-2025-02-12/"):
            repo = 'afp-2025-02-12'
        elif key.startswith("Isabelle2024/"):
            repo = 'Isabelle2024'
        else:
            repo = 'unknown'
        content = annotate(original_path)
        content = Client.pretty_unicode(content)
        sha = hashlib.sha256((content or "").encode('utf-8')).hexdigest()
        f.write(json.dumps({"text": content, "meta": {"path": key, "repo": repo, "sha": sha}}))
        f.write("\n")
        if i % 1000 == 0:
            print(f"Processed {i}/{TOTAL}")
    pass

# thy_files = glob.glob(os.path.join(AFP_PATH, '**', '*.thy'), recursive=True)
# for source_thy_file in thy_files:
#     thy_file = os.path.relpath(source_thy_file, AFP_PATH)
#     target_file_path = os.path.join(TARGET_AFP, thy_file)
#     key = f"./contrib/afp-2025-02-12/thys/{thy_file}"
#     print(f"Annotating {target_file_path}")
#     annotate(source_thy_file, target_file_path, key)
# 
# thy_files = glob.glob(os.path.join(STDLIB_PATH, '**', '*.thy'), recursive=True)
# for source_thy_file in thy_files:
#     thy_file = os.path.relpath(source_thy_file, STDLIB_PATH)
#     target_file_path = os.path.join(TARGET_STDLIB, thy_file)
#     key = f"./contrib/Isabelle2024/src/HOL/{thy_file}"
#     print(f"Annotating {target_file_path}")
#     annotate(source_thy_file, target_file_path, key)