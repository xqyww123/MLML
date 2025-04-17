import re

LANGS = {
    'origin': 'original Isabelle/Isar',
    'isar-SH*': 'Isar with SH*',
    'refined': 'Minilang + SH*',
    'raw': 'Minilang - SH*',
    'untyp_refined': 'Untyped Minilang + SH*',
    'untyp_raw': 'Untyped Minilang - SH*',
    'isar-SH': 'Isar-SH',
    'isar-SH*-idt': 'Isar-SH*-idt'
}

def chk_lang_supported(lang : str) -> bool:
    if lang not in LANGS:
        raise ValueError(f"Unsupported language: {lang}. Can only be one of\n{LANGS}")

def is_minilang(lang : str) -> bool:
    return lang in ['refined', 'raw', 'untyp_refined', 'untyp_raw']

def remove_comments(text : str) -> str:
    lines = text.split('\n')
    filtered_lines = [line for line in lines if not re.match(r'\s*\(\*.*\*\)\s*', line)]
    return '\n'.join(filtered_lines)

CAMLIZE_MAP = {
    'HAVE': 'Have',
    'CONSIDER': 'Consider',
    'CRUSH': 'Crush',
    'NEXT': 'Next',
    'END': 'End',
    'SIMP': 'Simp',
    'UNFOLD': 'Unfold',
    'APPLY': 'Apply',
    'DEFINE': 'Define',
    'LET': 'Let',
    'NOTATION': 'Notation',
    'RULE': 'Rule',
    'CHOOSE': 'Choose',
    'OPEN_MODULE': 'OpenModule',
    'CONFIG': 'Note',
    'INDUCT': 'Induct',
    'CASE_SPLIT': 'CaseSplit',
    'HAMMER': 'Hammer',
    'INTRO': 'Intro',
}

# Cached compiled regex patterns
_WITH_PATTERN = re.compile(r'\bWITH\b')
_WITHOUT_PATTERN = re.compile(r'\bWITHOUT\b')
_CAMLIZE_PATTERNS = {}

@staticmethod
def _init_camlize_patterns():
    # Initialize the patterns if not already done
    if not _CAMLIZE_PATTERNS:
        for key in CAMLIZE_MAP:
            # Match key at the beginning of a line, preserving leading whitespace
            _CAMLIZE_PATTERNS[key] = re.compile(r'^(\s*)\b' + re.escape(key) + r'\b', re.MULTILINE)

@staticmethod
def camlize_minilang(src : str) -> str:
    """
    Minilang keywords can be either full-captilized or camel-cased.
    Minilang evaluator accepts both.
    This function converts them to camel-cased keywords.
    """
    # Initialize patterns if not already done
    _init_camlize_patterns()
    
    # Replace first word of each line if it's in CAMLIZE_MAP
    result = src
    for key, value in CAMLIZE_MAP.items():
        # Use cached pattern
        result = _CAMLIZE_PATTERNS[key].sub(r'\1' + value, result)
    
    # Replace WITH with With and WITHOUT with Without
    result = _WITH_PATTERN.sub('With', result)
    result = _WITHOUT_PATTERN.sub('Without', result)
    
    return result