#!/bin/env python3
import torch
import argparse
import json
import os
import numpy as np
from tqdm import tqdm
from transformers import AutoModelForCausalLM, AutoTokenizer, pipeline
from datasets import Dataset

# Valid dataset options
VALID_DATASETS = ['minilang', 'minilang-no-SH', 'isar', 'isar-SH']
VALID_BASE_MODELS = ['llemma', 'deepseek']

# Parse command line arguments
parser = argparse.ArgumentParser(description='Run inference with a specified model and JSONL dataset')
parser.add_argument('--base_model', type=str, required=True, choices=VALID_BASE_MODELS,
                    help='Base model to use (llemma or deepseek)')
parser.add_argument('--dataset', type=str, required=True, choices=VALID_DATASETS,
                    help='Dataset to use (one of: minilang, minilang-no-SH, isar, isar-SH)')
parser.add_argument('--output', type=str, 
                    help='Output file to save results (defaults to results_{base_model}_{dataset}.jsonl)')
parser.add_argument('--max_samples', type=int, default=None,
                    help='Maximum number of samples to process (default: all)')
parser.add_argument('--max_new_tokens', type=int, default=2048,
                    help='Maximum number of new tokens to generate')
parser.add_argument('--temperature', type=float, default=0.0,
                    help='Temperature for sampling (default: 0.0)')
parser.add_argument('--top_p', type=float, default=0.9,
                    help='Top-p sampling parameter (default: 0.9)')
parser.add_argument('--seed', type=int, default=42,
                    help='Random seed for reproducibility')
parser.add_argument('--custom_model', type=str, 
                    help='Override with a custom model name/path (for advanced users)')
parser.add_argument('--batch_size', type=int, default=1,
                    help='Batch size for processing examples (default: 1)')
parser.add_argument('--device_map', type=str, default="auto",
                    help='Device map strategy for model distribution (auto, balanced, balanced_low_0, sequential) or specific mapping')
parser.add_argument('--gpu_ids', type=str, default=None,
                    help='Comma-separated list of GPU IDs to use (e.g., "0,1,2"). If not provided, all available GPUs will be used.')
parser.add_argument('--max_memory', type=str, default=None,
                    help='Maximum memory per GPU, comma-separated string (e.g., "24GiB,24GiB"). Helps with balancing model across GPUs.')
parser.add_argument('--num_workers', type=int, default=4,
                    help='Number of workers for DataLoader (default: 4)')
args = parser.parse_args()

if not torch.cuda.is_available():
    print("WARNING: CUDA not available, using CPU which will be much slower")

# Set random seed for reproducibility
torch.manual_seed(args.seed)
np.random.seed(args.seed)

# Setup GPU devices if specified
device_map = args.device_map
max_memory = None

if args.gpu_ids:
    os.environ["CUDA_VISIBLE_DEVICES"] = args.gpu_ids
    print(f"Using GPUs: {args.gpu_ids}")
    
    # Count available devices after setting CUDA_VISIBLE_DEVICES
    num_gpus = torch.cuda.device_count()
    print(f"Number of available GPUs: {num_gpus}")

# Parse max_memory if provided
if args.max_memory:
    max_memory_parts = args.max_memory.split(',')
    max_memory = {}
    for i, mem in enumerate(max_memory_parts):
        max_memory[i] = mem.strip()
    print(f"Using max memory configuration: {max_memory}")

# Construct the JSONL filename based on the selected dataset
jsonl_filename = f"eval_data_{args.dataset}.jsonl"
jsonl_path = os.path.join('tasks/Baldur/eval', jsonl_filename)

if not os.path.exists(jsonl_path):
    raise FileNotFoundError(f"JSONL file not found: {jsonl_path}")

# Load the JSONL file
print(f"Loading JSONL file: {jsonl_path}")
data = []
with open(jsonl_path, 'r') as f:
    for line in f:
        try:
            data.append(json.loads(line.strip()))
        except json.JSONDecodeError as e:
            print(f"Error decoding JSON line: {e}")
            continue

print(f"Number of examples: {len(data)}")

# Set model name based on base_model and dataset
if args.custom_model:
    model_name = args.custom_model
    print(f"Using custom model: {model_name}")
else:
    # For minilang-no-SH or isar-SH, use the base name (minilang or isar)
    model_name = f"haonan-li/{args.dataset}-{args.base_model}-7b"
    print(f"Using model: {model_name} (constructed from base_model={args.base_model}, dataset={args.dataset})")

# Determine output file
if args.output:
    output_file = args.output
else:
    output_file = f"tasks/Baldur/eval/results_{args.base_model}_{args.dataset}.jsonl"

# Load model and tokenizer
print(f"Loading model and tokenizer...")
tokenizer = AutoTokenizer.from_pretrained(model_name, trust_remote_code=True)

# Load model with configured device map
print(f"Loading model with device_map={device_map}")
model_load_kwargs = {
    "device_map": device_map,
    "torch_dtype": torch.bfloat16,
    "trust_remote_code": True,
    "low_cpu_mem_usage": True
}

# Add max_memory if configured
if max_memory:
    model_load_kwargs["max_memory"] = max_memory

model = AutoModelForCausalLM.from_pretrained(
    model_name,
    **model_load_kwargs
)

# Display model distribution across devices
if hasattr(model, "hf_device_map"):
    print("Model distribution across devices:")
    for module_name, device in model.hf_device_map.items():
        print(f"  {module_name}: {device}")

# Format prompt with the fixed format
def format_prompt(example):
    prelude = example['prelude']
    goal = example['goal']
    
    prompt = f"""<s>system\nYou are an AI programming assistant, and you only answer questions related to computer science. For politically sensitive questions, security and privacy issues, and other non-computer science questions, you will refuse to answer.\n</s>\n<s>user\nPRELUDE:\n{prelude}\nGOAL:\n{goal}</s>\n<s>assistant\n"""
#    
#    f"""<s>system
#You are an AI programming assistant, and you only answer questions related to computer science. For politically sensitive questions, security and privacy issues, and other non-computer science questions, you will refuse to answer.
#</s>
#<s>user
#PRELUDE:
#{prelude}
#GOAL:
#{goal.strip()}</s>
#<s>assistant
#"""
    return prompt

# Process samples
sample_count = len(data) if args.max_samples is None else min(args.max_samples, len(data))
data_subset = data[:sample_count]

print(f"Processing {sample_count} examples with temperature={args.temperature}, top_p={args.top_p}, batch_size={args.batch_size}")

# Prepare dataset for more efficient processing
def preprocess_function(examples):
    # Format the prompts for each example
    prompts = [format_prompt(ex) for ex in examples]
    return {"prompt": prompts, "example": examples}

# Convert to HuggingFace Dataset format
hf_dataset = Dataset.from_dict({"example": data_subset})
hf_dataset = hf_dataset.map(
    lambda x: {"prompt": format_prompt(x["example"])},
    batched=False
)

# Setup pipeline for text generation
text_gen = pipeline(
    "text-generation",
    model=model,
    tokenizer=tokenizer,
    device_map=device_map,
)
print(f"Model and tokenizer loaded successfully.")

# Run inference on dataset
with open(output_file, 'w') as f_out:
    # Process dataset with optimized batching
    for i in tqdm(range(0, len(hf_dataset), args.batch_size), desc="Processing batches"):
        batch = hf_dataset[i:min(i+args.batch_size, len(hf_dataset))]
        prompts = batch["prompt"]
        examples = batch["example"]
        
        try:
            # Generate responses for the batch
            batch_outputs = text_gen(
                prompts,
                max_new_tokens=4096,
                do_sample=True, # if args.temperature > 0 else False,
                #top_p=args.top_p,
                temperature=0.1,
                batch_size=args.batch_size
            )
            
            # Process each example in the batch
            for example, prompt, outputs in zip(examples, prompts, batch_outputs):
                # Get the generated text
                generated_text = outputs[0]["generated_text"]
                print(generated_text)
                print('----------------------------\n\n')
                
                # Remove the prompt from the generated text to get just the model's response
                if generated_text.startswith(prompt):
                    response = generated_text[len(prompt):].strip()
                else:
                    response = generated_text
                print(response)
                print('----------------------------\n\n')
                
                # Save result
                result = {
                    'index': example['index'],
                    'response': response
                }
                
                # Write to output file
                f_out.write(json.dumps(result) + '\n')
                
        except Exception as e:
            print(f"Error processing batch starting at index {i}: {e}")

print(f"Inference complete. Results saved to {output_file}")

