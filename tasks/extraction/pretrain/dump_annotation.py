#!/usr/bin/env python3
from sqlitedict import SqliteDict
import json
import os

AFP_PATH = '/lustre/scratch/users/qiyuan.xu/MLML_data/pretrain/isabelle/origin/afp-2025-02-12'
TARGET_AFP = '/lustre/scratch/users/qiyuan.xu/MLML_data/pretrain/isabelle/annotated/afp-2025-02-12'
STDLIB_PATH = '/lustre/scratch/users/qiyuan.xu/MLML_data/pretrain/isabelle/origin/stdlib'
TARGET_STDLIB = '/lustre/scratch/users/qiyuan.xu/MLML_data/pretrain/isabelle/annotated/stdlib'

TARGET_PP = 'T2S3'

ANNOTATIONS_CACHE_FILE = '/lustre/scratch/users/qiyuan.xu/MLML_data/annotations_cache.json'

ANNOTATIONS = {}

if os.path.exists(ANNOTATIONS_CACHE_FILE):
    # 从缓存文件读取
    with open(ANNOTATIONS_CACHE_FILE, 'r') as f:
        ANNOTATIONS = json.load(f)
else:
    print(f"Cache missing, reading from database")
    # 从数据库读取并生成缓存
    with SqliteDict('/lustre/scratch/users/qiyuan.xu/MLML_data/annotations_on_original_isar.db') as db:
        for key, value in db.items():
            (file, _) = key.split(':')
            if file not in ANNOTATIONS:
                ANNOTATIONS[file] = {}
            store = ANNOTATIONS[file]
            for (line, column, _, _), pps in value[0]:
                if line not in store:
                    store[line] = {}
                store[line][column] = pps
    # 保存到缓存文件
    with open(ANNOTATIONS_CACHE_FILE, 'w') as f:
        json.dump(ANNOTATIONS, f)

import glob
import io

def retract_trailing_spaces(buf: io.StringIO) -> None:
    buf.seek(0, io.SEEK_END)  # Ensure we're at the end of the buffer
    pos = buf.tell()
    while pos > 0:
        buf.seek(pos - 1)
        ch = buf.read(1)
        if ch != ' ' and ch != '\t':
            break
        pos -= 1
    buf.seek(pos)
    buf.truncate()

def annotate(origin_file_path, target_file_path, key):
    if key not in ANNOTATIONS:
        return False
    annotations = ANNOTATIONS[key]
    with open(origin_file_path, 'r') as f:
        content = f.read()
    line = 1
    column = 1
    i = 0
    LEN = len(content)
    indent = 0
    leading_spaces = True
    buf = io.StringIO()
    def write(annot):
        nonlocal buf
        nonlocal indent
        lines = annot.split('\n')
        for line in lines:
            buf.write(line)
            buf.write('\n')
            for _ in range(indent):
                buf.write(' ')
    while i < LEN:
        if line in annotations:
            store = annotations[line]
            while i < LEN and content[i] != '\n':
                c = content[i]
                buf.write(c)
                if column in store:
                    # now we need to insert the annotation
                    annot = store[column][TARGET_PP]
                    if not leading_spaces:
                        retract_trailing_spaces(buf)
                        buf.write('\n')
                        for _ in range(indent):
                            buf.write(' ')
                    write(annot)
                    for pp in pps:
                        print(pp)
                if leading_spaces:
                    if c == ' ':
                        indent += 1
                    elif c == '\t':
                        indent += 4
                    else:
                        leading_spaces = False
                i += 1
                column += 1
            if i != LEN:
                buf.write(content[i])
                line += 1
                column = 1
        else:
            while i < LEN and content[i] != '\n':
                buf.write(content[i])
                i += 1
            if i != LEN:
                buf.write(content[i])
                line += 1
                column = 1
                leading_spaces = True
                indent = 0
    with open(target_file_path, 'w') as f:
        f.write(buf.getvalue())

thy_files = glob.glob(os.path.join(AFP_PATH, '**', '*.thy'), recursive=True)
for source_thy_file in thy_files:
    thy_file = os.path.relpath(source_thy_file, AFP_PATH)
    target_file_path = os.path.join(TARGET_AFP, thy_file)
    key = f"./contrib/afp-2025-02-12/thys/{thy_file}"
    print(f"Annotating {target_file_path}")
    annotate(source_thy_file, target_file_path, key)

thy_files = glob.glob(os.path.join(STDLIB_PATH, '**', '*.thy'), recursive=True)
for source_thy_file in thy_files:
    thy_file = os.path.relpath(source_thy_file, STDLIB_PATH)
    target_file_path = os.path.join(TARGET_STDLIB, thy_file)
    key = f"./contrib/Isabelle2024/src/HOL/{thy_file}"
    print(f"Annotating {target_file_path}")
    annotate(source_thy_file, target_file_path, key)