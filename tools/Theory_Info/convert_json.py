#! /usr/bin/env python3
import msgpack
import json
import os
def norm_file(file):
    if os.path.isabs(file):
        try:
            rel_path = os.path.relpath(file, os.getcwd())
            file = './' + rel_path if not rel_path.startswith('.') else rel_path
            return file
        except ValueError:
            return file


# Load the MessagePack file
with open('./sessions.msgpack', 'rb') as f:
    raw_sessions = msgpack.load(f)

def parse_session (data):
    return {
        'deps': data[0],
        'theories': data[1],
    }

sessions = {s: parse_session(raw_sessions[s]) for s in raw_sessions}
# Write to JSON with pretty formatting
with open('./data/sessions.json', 'w') as f:
    json.dump(sessions, f, indent=2)


with open('theories.msgpack', 'rb') as f:
    raw_theories = msgpack.load(f)

def parse_theory (data):
    return {
        'deps': data[1],
        'path': norm_file(data[0]),
    }

theories = {t: parse_theory(raw_theories[t]) for t in raw_theories}

with open('./data/theories.json', 'w') as f:
    json.dump(theories, f, indent=2)
