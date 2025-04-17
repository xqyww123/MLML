from transformers import AutoTokenizer

def check_tokenizer_type(model_name):
    """
    加载指定模型的 tokenizer 并检查其具体类型
    """
    tokenizer = AutoTokenizer.from_pretrained(model_name)
    
    # 打印 tokenizer 的类型
    print(f"Tokenizer 类型: {type(tokenizer).__name__}")
    print(f"Tokenizer 基类: {type(tokenizer).__bases__}")
    
    # 检查 tokenizer 的词汇表大小和特殊标记
    print(f"词汇表大小: {tokenizer.vocab_size}")
    print(f"所有特殊标记: {tokenizer.all_special_tokens}")
    print(f"特殊标记映射: {tokenizer.special_tokens_map}")
    
    # 查看 tokenizer 的配置参数
    print(f"\nTokenizer 配置:")
    for key, value in tokenizer.init_kwargs.items():
        print(f"  {key}: {value}")
    
    return tokenizer

def count_tokens(text, model_name):
    """
    计算文本使用Deepseek tokenizer后的token数量
    
    Args:
        text (str): 要计算的文本
        model_name (str): 使用的模型名称
    
    Returns:
        int: token数量
    """
    # 加载tokenizer
    tokenizer = AutoTokenizer.from_pretrained(model_name)
    
    # 只获取token数量，不进行其他处理
    tokens = tokenizer.encode(text)
    token_count = len(tokens)
    
    return token_count


def is_codepoint_supported(tokenizer, codepoint):
    """
    检查给定tokenizer是否支持特定Unicode字符或码点
    
    Args:
        tokenizer: 用于检查的tokenizer
        codepoint (int or str): Unicode码点(整数)或单个字符(字符串)
    
    Returns:
        int or False: 若支持则返回实际token数量(排除特殊token)，否则返回False
    """
    # 将输入统一转换为字符
    try:
        char = codepoint if isinstance(codepoint, str) else chr(codepoint)
    except (ValueError, OverflowError):
        return False
    
    # 处理多字符字符串
    if isinstance(codepoint, str) and len(codepoint) > 1:
        # 获取原始token列表
        #tokens = tokenizer.encode(char)
        # 获取不包含特殊token的token列表
        tokens_no_special = tokenizer.encode(char, add_special_tokens=False)
        
        if codepoint in tokenizer.decode(tokens_no_special):
            return len(tokens_no_special)  # 返回不包含特殊token的数量
        else:
            return False
    
    # 编码单个字符并检查能否正确恢复
    #tokens = tokenizer.encode(char)
    tokens_no_special = tokenizer.encode(char, add_special_tokens=False)
    decoded = tokenizer.decode(tokens_no_special)
    
    # 如果字符可以被恢复，返回非特殊token数量，否则返回False
    return len(tokens_no_special) if char in decoded else False


def tokenize_text(text, tokenizer, verbose=False):
    """
    使用指定的 tokenizer 对输入文本进行分词
    
    Args:
        text (str): 输入文本
        tokenizer: 预加载的 tokenizer，如果为 None 则加载默认的
        verbose (bool): 是否打印详细的 token 信息
    """
    
    # 对输入文本进行分词
    encoding = tokenizer(text, return_tensors="pt")
    token_ids = encoding.input_ids[0]
    
    # 获取 token 字符串
    tokens = []
    for token_id in token_ids:
        token = tokenizer.decode([token_id])
        tokens.append(token)
    
    # 如果请求，打印详细信息
    if verbose:
        print(f"\n输入文本: {text}")
        print(f"Token 数量: {len(tokens)}")
        print("\nToken 详情:")
        for i, (token, token_id) in enumerate(zip(tokens, token_ids)):
            print(f"Token {i+1}: '{token}' (ID: {token_id})")
    
    return tokens, token_ids.tolist(), text

if __name__ == "__main__":
    #tokenizer = check_tokenizer_type('EleutherAI/llemma_34b')
    tokenizer = check_tokenizer_type('deepseek-ai/DeepSeek-Prover-V1.5-Base')
    
    text = """Have "(h, U) \<in> B \<and> card (snd (h, U)) = Suc m" unfolding assms(3)
    End With aaa ccc(1) Without zx
    Consider xx where a:"xx < 1"
    CaseSplit
    CASE_SPLIT
    CASESPLIT
    Induct
    Next
    NEXT
    END
    End
    DEFINE
    Define
    WITHOUT
    Without
    WITH
    With
    """
    
    print("正在对文本进行分词...")
    tokens, token_ids, text = tokenize_text(text, tokenizer, True)
    
    print(f"输入文本: {text}")
    print(f"总 token 数: {len(tokens)}")
    print(f"Token ID: {token_ids}")