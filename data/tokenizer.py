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

tokenizer = check_tokenizer_type('EleutherAI/llemma_34b')


text = """Have "(h, U) \<in> B \<and> card (snd (h, U)) = Suc m" unfolding assms(3)
End With aaa ccc(1) Without zx
Consider xx where a:"xx < 1"
CaseSplit
Induct
Next
Unfold"""

print("正在对文本进行分词...")
tokens, token_ids, text = tokenize_text(text, tokenizer, True)

print(f"输入文本: {text}")
print(f"总 token 数: {len(tokens)}")
print(f"Token ID: {token_ids}")