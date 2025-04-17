from transformers import AutoTokenizer
from data.tokenizer import is_codepoint_supported
from IsaREPL import SYMBOLS
from isabelle import Data

def mk_unicode_table(model_name):
    tokenizer = AutoTokenizer.from_pretrained(model_name)
    ret = {}
    for symbol, unicode in SYMBOLS.items():
        if is_codepoint_supported(tokenizer, unicode):
            ret[symbol] = unicode
        else:
            print(f"{unicode} {symbol} is not supported by {model_name}")
        # num = is_codepoint_supported(tokenizer, unicode)
        # alt = is_codepoint_supported(tokenizer, symbol)
        # if num <= 3 or not alt:
        #     ret[symbol] = unicode
        # else:
        #     print(f"{unicode} {symbol} is not supported by {model_name} (unicode = {num}, ascii = {alt})")
    return ret

def translate_unicode(table, text):
    """
    Translates ASCII symbols to their Unicode equivalents based on the provided table.
    
    Args:
        table: Dictionary mapping ASCII symbols to Unicode equivalents
        text: The text to translate
        
    Returns:
        Text with ASCII symbols replaced by their Unicode equivalents
    """
    if not table:
        return text
    
    import re
    
    # Create a pattern for all symbols in the table
    # We need to escape special regex characters
    pattern = '|'.join(re.escape(symbol) for symbol in table.keys())
    
    # Define a replacement function
    def replace_match(match):
        return table[match.group(0)]
    
    # Perform all replacements in a single pass
    return re.sub(pattern, replace_match, text)

# table = mk_unicode_table('deepseek-ai/DeepSeek-Prover-V1.5-Base')
# dest = translate_unicode(table, "xx \<rightarrow> yy")
# print(dest)