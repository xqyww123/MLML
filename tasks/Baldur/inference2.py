from vllm import LLM, SamplingParams
from typing import List, Optional, Dict, Any
import torch
import json

def load_data(data_path: str):
    with open(data_path, 'r') as file:
        data = [json.loads(line) for line in file]
    return data

def format_prompts(data: List[Dict[str, Any]]):
    #lemma_prompt_format = """<s>system\nYou are an AI programming assistant, and you only answer questions related to computer science. For politically sensitive questions, security and privacy issues, and other non-computer science questions, you will refuse to answer.\n</s>\n<s>user\nPRELUDE:\n{prelude}\nGOAL:\n{goal}</s>\n<s>assistant\n"""
    deepseek_prompt_format = """You are an AI programming assistant, utilizing the Deepseek Coder model, developed by Deepseek Company, and you only answer questions related to computer science. For politically sensitive questions, security and privacy issues, and other non-computer science questions, you will refuse to answer.\n### Instruction:\nPRELUDE:\n{prelude}\nGOAL:\n{goal}\n### Response:\n"""
    lemma_prompt_format = deepseek_prompt_format
    prompts = []
    for d in data:
        prompt = lemma_prompt_format.format(prelude=d["prelude"], goal=d["goal"])
        prompts.append(prompt)
    return prompts

def load_model(
    model_name_or_path: str,
    tensor_parallel_size: int = 1,
    gpu_memory_utilization: float = 0.9,
    max_model_len: Optional[int] = None,
    quantization: Optional[str] = None,
    **kwargs: Any
) -> LLM:
    """
    Load a model using VLLM with specified configuration.
    
    Args:
        model_name_or_path: Path to the model or model identifier from huggingface.co/models
        tensor_parallel_size: Number of GPUs to use for tensor parallelism
        gpu_memory_utilization: Fraction of GPU memory to use
        max_model_len: Maximum sequence length for the model
        quantization: Quantization method to use (e.g., "awq", "squeezellm")
        **kwargs: Additional arguments to pass to LLM
    
    Returns:
        LLM: The loaded model
    """
    try:
        # Configure sampling parameters
        
        # Load the model with float16 dtype explicitly for V100 GPUs
        llm = LLM(
            model=model_name_or_path,
            tensor_parallel_size=tensor_parallel_size,
            #pipeline_parallel_size=1,
            #pipeline_parallel_size=2,
            #distributed_executor_backend="ray",
            gpu_memory_utilization=gpu_memory_utilization,
            #max_model_len=4096,
            quantization=quantization,
            dtype=torch.float16,  # Explicitly use float16 instead of the default bfloat16
            max_num_seqs=4,
            **kwargs
        )
        
        return llm
        
    except Exception as e:
        raise RuntimeError(f"Failed to load model: {str(e)}")

if __name__ == "__main__":
    # Example usage
    model = load_model(
        #model_name_or_path="anonymous6435/deepseek-prover-isar",
        model_name_or_path="anonymous6435/deepseek-prover-minilang",
        #model_name_or_path="deepseek-ai/DeepSeek-Prover-V2-7B",
        tensor_parallel_size=1,  # Adjust based on your GPU setup
        gpu_memory_utilization=0.98,
        #quantization="bitsandbytes"
    )

    data = load_data("request.jsonl")


    sampling_params = SamplingParams(
        temperature=0,
        max_tokens=4096,
        stop=["<|EOT|>"],
        #stop=["<｜end▁of▁sentence｜>"],
        skip_special_tokens=True,
    )

    prompts = format_prompts(data)

    responses = model.generate(prompts, sampling_params)
    # Get text from responses
    generated_texts = [response.outputs[0].text for response in responses]

    full_responses = []
    for response, d in zip(generated_texts, data):
        full_responses.append({
            "index": d["index"],
            "prelude": d["prelude"],
            "goal": d["goal"],
            "response": response
        })
    
    # Write to JSONL file (each JSON object on a separate line)
    with open("responses.jsonl", "w") as f:
        for item in full_responses:
            f.write(json.dumps(item) + "\n")


    
    

