import re
from sqlitedict import SqliteDict
import json

def clean_makrup(code : str) -> str:
    """
    Cleans markup by removing control characters and extracting content between \0x05 markers.
    
    Args:
        code (str): The input string that may contain control characters
        
    Returns:
        str: The cleaned string with content between \0x05 markers extracted
    """
    if '\x05' not in code:
        return None
    
    # Extract substrings between \x05 markers
    extracted_parts = re.findall(r'\x05([^\x05]*)\x05', code)
    
    cleaned_code = re.sub(r'\x05[^\x05]*\x05', '', code)

    # Check if any extracted part has the specific format with \u0006 delimiters
    for part in extracted_parts:
        if '\u0006' in part:
            # Check for the specific format pattern
            pattern = r'\u0006input\u0006delimited=[^\x06]*\u0006line=[^\x06]*\u0006offset=[^\x06]*\u0006end_offset=[^\x06]*\u0006file=[^\x06]*'
            if not re.match(pattern, part) and part != '\x06':
                raise ValueError(f"Something wrong {part}, {code}")
    
    if extracted_parts:
        return cleaned_code.replace('\x7f', '\"')
    else:
        return None


def clean_markup_from_db():
    total = 0
    count = 0
    to_modify = {}
    with SqliteDict('cache/translation/results.db') as db:
        for key, value in db.items():
            _, _, cat = key.split(':')
            (prf, err, pos, spec_column) = value
            prf2 = clean_makrup(prf)
            total += 1
            if prf2:
                count += 1
                to_modify[key] = (prf2, err, pos, spec_column)
            if total % 1000 == 0:
                print(f"{total}, {count}, {count/total:.2%}")
        total = 0
        for key, value in to_modify.items():
            db[key] = value
            total += 1
            if total % 100 == 0:
                db.commit()
                print(total)
        db.commit()
    print(f"{total}, {count}")


def norm_proof(path):
    entries = []
    with open(path, 'r') as f:
        for line in f:
            data = json.loads(line)
            prf = data['response']
            eot_index = prf.find('<|EOT|>')
            if eot_index != -1:
                prf = prf[:eot_index]
            prf2 = clean_makrup(prf)
            prf = prf2 if prf2 else prf
            data['response'] = prf
            entries.append(data)
    with open(path+".norm", 'w') as f:
        for entry in entries:
            f.write(json.dumps(entry) + '\n')

norm_proof('./evaluation/isar-SH*-DS_response.jsonl')
exit()

