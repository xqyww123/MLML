#! /usr/bin/env python3
import argparse
import json
import logging
import os
import sys
from pathlib import Path
from transformers import AutoTokenizer

# Default supported text file extensions
DEFAULT_FILE_EXTENSIONS = ['.txt', '.py', '.json', '.jsonl', '.md', '.thy', '.ml', '.mm', '.lean']

# ANSI color codes
class Colors:
    RESET = '\033[0m'
    BOLD = '\033[1m'
    RED = '\033[91m'
    GREEN = '\033[92m'
    YELLOW = '\033[93m'
    BLUE = '\033[94m'
    MAGENTA = '\033[95m'
    CYAN = '\033[96m'
    WHITE = '\033[97m'
    GRAY = '\033[90m'

class ColoredFormatter(logging.Formatter):
    """Custom formatter to add colors to log messages"""
    
    COLORS = {
        'DEBUG': Colors.GRAY,
        'INFO': Colors.RESET,
        'WARNING': Colors.YELLOW,
        'ERROR': Colors.RED,
        'CRITICAL': Colors.RED + Colors.BOLD,
    }
    
    def format(self, record):
        # Format the message
        message = super().format(record)
        
        # Add color if output is to a terminal
        if sys.stdout.isatty():
            # Determine color based on message content and level
            color = self.COLORS.get(record.levelname, Colors.RESET)
            
            # Special coloring for specific message patterns
            if record.levelname == 'ERROR' or 'ERROR:' in message:
                color = Colors.RED + Colors.BOLD
            elif record.levelname == 'WARNING' or 'Warning:' in message:
                color = Colors.YELLOW
            elif '[1/' in message or 'Statistics complete!' in message:
                # Progress and summary messages
                color = Colors.CYAN
            elif 'Using model:' in message or 'Total' in message:
                # Header and summary info
                color = Colors.GREEN
            
            return f"{color}{message}{Colors.RESET}"
        else:
            return message

# Configure logging with colored output
def setup_logging():
    """Setup colored logging"""
    handler = logging.StreamHandler(sys.stdout)
    handler.setFormatter(ColoredFormatter('%(message)s'))
    
    logger = logging.getLogger(__name__)
    logger.setLevel(logging.INFO)
    logger.addHandler(handler)
    return logger

logger = setup_logging()

def check_tokenizer_type(model_name):
    """
    Load the tokenizer for the specified model and check its type
    """
    tokenizer = AutoTokenizer.from_pretrained(model_name)
    
    # Print tokenizer type
    logger.info(f"Tokenizer type: {type(tokenizer).__name__}")
    logger.info(f"Tokenizer base classes: {type(tokenizer).__bases__}")
    
    # Check tokenizer vocabulary size and special tokens
    logger.info(f"Vocabulary size: {tokenizer.vocab_size}")
    logger.info(f"All special tokens: {tokenizer.all_special_tokens}")
    logger.info(f"Special tokens map: {tokenizer.special_tokens_map}")
    
    # View tokenizer configuration parameters
    logger.info(f"\nTokenizer configuration:")
    for key, value in tokenizer.init_kwargs.items():
        logger.info(f"  {key}: {value}")
    
    return tokenizer

def count_tokens(text, model_name=None, tokenizer=None):
    """
    Count the number of tokens in text using the specified tokenizer
    
    Args:
        text (str): Text to count tokens for
        model_name (str, optional): Model name to use, ignored if tokenizer is provided
        tokenizer: Pre-loaded tokenizer, if None then model_name will be used to load
    
    Returns:
        tuple: (token_count, tokens, decoded_text) where:
            token_count: Number of tokens
            tokens: List of token IDs
            decoded_text: Text decoded from tokens
    """
    # Load tokenizer if not provided
    if tokenizer is None:
        if model_name is None:
            raise ValueError("Must provide model_name or tokenizer")
        tokenizer = AutoTokenizer.from_pretrained(model_name)
    
    # Encode text to tokens
    tokens = tokenizer.encode(text, add_special_tokens=False)
    token_count = len(tokens)
    
    # Decode tokens back to text to check if it can be restored
    decoded_text = tokenizer.decode(tokens)
    
    return token_count, tokens, decoded_text


def check_text_restoration(original_text, decoded_text, file_path):
    """
    Check if decoded text matches original text and report all differences
    
    Args:
        original_text (str): Original text
        decoded_text (str): Text decoded from tokens
        file_path (Path): File path for error reporting
    
    Returns:
        bool: True if texts match, False otherwise
    """
    if original_text == decoded_text:
        return True
    
    # Find all differences
    differences = []
    max_len = max(len(original_text), len(decoded_text))
    min_len = min(len(original_text), len(decoded_text))
    
    i = 0
    while i < max_len:
        if i >= len(original_text) or i >= len(decoded_text):
            # One text is longer
            differences.append((i, i, max_len))
            break
        
        if original_text[i] != decoded_text[i]:
            # Found a difference, find where it ends
            diff_start = i
            
            # Find where the difference ends (where they match again)
            diff_end = i + 1
            for j in range(i + 1, min(max_len, i + 100)):  # Check up to 100 chars ahead
                if j >= len(original_text) or j >= len(decoded_text):
                    diff_end = j
                    break
                if original_text[j] == decoded_text[j]:
                    diff_end = j
                    break
                diff_end = j + 1
            
            differences.append((diff_start, diff_end, diff_end))
            i = diff_end
        else:
            i += 1
    
    # Report all differences (limit to first 10 to avoid too much output)
    logger.error(f"  ERROR: Text cannot be fully restored in {file_path} ({len(differences)} difference(s) found)")
    
    for idx, (diff_start, diff_end_orig, diff_end_dec) in enumerate(differences[:10]):
        # Get context: 10 characters before and after the difference
        start_pos = max(0, diff_start - 10)
        end_pos_orig = min(len(original_text), diff_end_orig + 10)
        end_pos_dec = min(len(decoded_text), diff_end_dec + 10)
        
        # Show original and decoded text around the difference
        original_snippet = original_text[start_pos:end_pos_orig]
        decoded_snippet = decoded_text[start_pos:end_pos_dec]
        
        # Show the actual difference
        orig_diff = original_text[diff_start:diff_end_orig] if diff_start < len(original_text) else ""
        dec_diff = decoded_text[diff_start:diff_end_dec] if diff_start < len(decoded_text) else ""
        
        logger.error(f"    Difference #{idx + 1} at position {diff_start}:")
        logger.error(f"      Context (10 chars before/after): ...{original_snippet}...")
        logger.error(f"      Original: {repr(orig_diff)}")
        logger.error(f"      Decoded:  {repr(dec_diff)}")
    
    if len(differences) > 10:
        logger.error(f"    ... and {len(differences) - 10} more difference(s)")
    
    return False


def tokenize_text(text, tokenizer, verbose=False):
    """
    Tokenize input text using the specified tokenizer
    
    Args:
        text (str): Input text
        tokenizer: Pre-loaded tokenizer, if None then load default
        verbose (bool): Whether to print detailed token information
    """
    
    # Tokenize input text
    encoding = tokenizer(text, return_tensors="pt")
    token_ids = encoding.input_ids[0]
    
    # Get token strings
    tokens = []
    for token_id in token_ids:
        token = tokenizer.decode([token_id])
        tokens.append(token)
    
    # Print detailed information if requested
    if verbose:
        logger.info(f"\nInput text: {text}")
        logger.info(f"Token count: {len(tokens)}")
        logger.info("\nToken details:")
        for i, (token, token_id) in enumerate(zip(tokens, token_ids)):
            logger.info(f"Token {i+1}: '{token}' (ID: {token_id})")
    
    return tokens, token_ids.tolist(), text


def pretty_print_tokenize(text, tokenizer):
    """
    Tokenize text from stdin and pretty print the results
    
    Args:
        text (str): Input text to tokenize
        tokenizer: Pre-loaded tokenizer
    """
    # Tokenize the text
    encoding = tokenizer(text, add_special_tokens=False)
    token_ids = encoding.input_ids
    
    # Get token strings and IDs as lists
    # Handle both list and tensor cases
    if hasattr(token_ids, 'tolist'):
        token_id_list = token_ids.tolist()
        # If it's a tensor, might have batch dimension - get first item if nested
        if isinstance(token_id_list, list) and len(token_id_list) > 0 and isinstance(token_id_list[0], list):
            token_id_list = token_id_list[0]
    elif isinstance(token_ids, list):
        # Handle case where it might be nested (batch dimension)
        if len(token_ids) > 0 and isinstance(token_ids[0], list):
            token_id_list = token_ids[0]
        else:
            token_id_list = token_ids
    else:
        token_id_list = list(token_ids)
        if len(token_id_list) > 0 and isinstance(token_id_list[0], list):
            token_id_list = token_id_list[0]
    
    # Get token strings - use decode to get readable text, and convert_ids_to_tokens for raw token pieces
    decoded_tokens = [tokenizer.decode([tid]) for tid in token_id_list]
    
    # Try to get raw token pieces (may include special markers like ## for WordPiece or ▁ for SentencePiece)
    try:
        token_pieces = tokenizer.convert_ids_to_tokens(token_id_list)
    except:
        token_pieces = decoded_tokens
    
    # Use decoded tokens for display, but note if raw token piece differs
    token_strings = decoded_tokens
    
    # Calculate column widths for pretty printing
    max_index_width = max(5, len(str(len(token_id_list))) if token_id_list else 5)  # At least "Index" width
    max_id_width = max(7, max(len(str(tid)) for tid in token_id_list) if token_id_list else 7)  # At least "Token ID" width
    max_token_repr_width = max(20, max(len(repr(ts)) for ts in token_strings) if token_strings else 20)  # At least "Token String (repr)" width
    
    # Print header
    print()
    print("=" * 80)
    print(f"{Colors.CYAN}{Colors.BOLD}Tokenization Results{Colors.RESET}")
    print("=" * 80)
    print()
    
    # Print input text
    print(f"{Colors.GREEN}{Colors.BOLD}Input Text:{Colors.RESET}")
    print("-" * 80)
    print(repr(text))
    print()
    
    # Print statistics
    print(f"{Colors.GREEN}{Colors.BOLD}Statistics:{Colors.RESET}")
    print("-" * 80)
    print(f"  Total tokens: {Colors.CYAN}{len(token_id_list)}{Colors.RESET}")
    print(f"  Input length: {Colors.CYAN}{len(text)}{Colors.RESET} characters")
    if len(text) > 0:
        print(f"  Tokens per character: {Colors.CYAN}{len(token_id_list) / len(text):.3f}{Colors.RESET}")
    print()
    
    # Print token table
    print(f"{Colors.GREEN}{Colors.BOLD}Token Details:{Colors.RESET}")
    print("-" * 80)
    if token_id_list:
        print(f"{'Index':<{max_index_width}} {'Token ID':<{max_id_width}} {'Decoded Text (repr)':<{max_token_repr_width}} {'Decoded Text (raw)'} {'Token Piece'}")
        print("-" * 80)
    else:
        print("(No tokens)")
        print("-" * 80)
    
    for idx, (token_id, decoded_str, token_piece) in enumerate(zip(token_id_list, token_strings, token_pieces)):
        # Format decoded token string for display
        decoded_repr = repr(decoded_str)
        
        # Show raw decoded text (handle non-printable characters)
        if decoded_str.isprintable() or all(c in '\n\t\r' or c.isprintable() for c in decoded_str):
            decoded_raw = decoded_str
            # Replace common whitespace for visibility
            decoded_raw = decoded_raw.replace('\n', '\\n').replace('\t', '\\t').replace('\r', '\\r')
        else:
            decoded_raw = f"{Colors.GRAY}[contains non-printable]{Colors.RESET}"
        
        # Truncate if too long
        max_raw_display = 30
        if len(decoded_raw) > max_raw_display:
            decoded_raw = decoded_raw[:max_raw_display] + "..."
        
        # Show token piece (may differ from decoded text for subword tokenizers)
        piece_display = repr(token_piece) if token_piece != decoded_str else f"{Colors.GRAY}(same){Colors.RESET}"
        if len(piece_display) > 25:
            piece_display = piece_display[:22] + "..."
        
        # Color code: use cyan for indices, yellow for IDs, reset for strings
        idx_str = f"{Colors.CYAN}{idx:<{max_index_width}}{Colors.RESET}"
        id_str = f"{Colors.YELLOW}{token_id:<{max_id_width}}{Colors.RESET}"
        repr_str = f"{decoded_repr:<{max_token_repr_width + 2}}"
        
        print(f"{idx_str}  {id_str}  {repr_str} {decoded_raw:<32} {piece_display}")
    
    print("-" * 80)
    print()
    
    # Show decoded text for verification
    decoded_text = tokenizer.decode(token_id_list)
    can_restore = (text == decoded_text)
    
    print(f"{Colors.GREEN}{Colors.BOLD}Decoded Text (for verification):{Colors.RESET}")
    print("-" * 80)
    print(repr(decoded_text))
    print()
    
    if can_restore:
        print(f"{Colors.GREEN}✓ Text can be fully restored from tokens{Colors.RESET}")
    else:
        print(f"{Colors.RED}✗ Text cannot be fully restored from tokens{Colors.RESET}")
        print(f"{Colors.YELLOW}  (Original and decoded texts differ){Colors.RESET}")
    print()
    print("=" * 80)


def count_file_tokens(file_path, tokenizer, verbose=False, show_progress=False, file_index=None, total_files=None, cumulative_tokens=0, check_restoration=True):
    """
    Count tokens in a single file
    
    Args:
        file_path (Path): File path
        tokenizer: Pre-loaded tokenizer
        verbose (bool): Whether to show file information
        show_progress (bool): Whether to show progress information
        file_index (int, optional): Current file index (1-based)
        total_files (int, optional): Total number of files
        cumulative_tokens (int): Cumulative token count so far
        check_restoration (bool): Whether to check if text can be restored (default: True)
    
    Returns:
        tuple: (token count, file info dict) or None if failed
    """
    try:
        # Read file content
        with open(file_path, 'r', errors='ignore') as f:
            content = f.read()
        
        # Count tokens and check if text can be restored
        token_count, tokens, decoded_text = count_tokens(content, tokenizer=tokenizer)
        
        # Check if text can be restored (if enabled)
        can_restore = True
        if check_restoration:
            can_restore = check_text_restoration(content, decoded_text, file_path)
        
        file_info = {
            'path': str(file_path),
            'tokens': token_count,
            'can_restore': can_restore
        }
        
        # Show progress with cumulative tokens
        if show_progress:
            progress_info = ""
            if file_index is not None and total_files is not None:
                progress_info = f"[{file_index}/{total_files}] "
            cumulative = cumulative_tokens + token_count
            logger.info(f"{progress_info}{file_path}: {token_count:,} tokens (cumulative: {cumulative:,})")
        elif verbose:
            logger.info(f"  {file_path}: {token_count:,} tokens")
        
        return token_count, file_info
    
    except Exception as e:
        if show_progress or verbose:
            error_msg = f"  Warning: Cannot read file {file_path}: {e}"
            if show_progress and file_index is not None and total_files is not None:
                error_msg = f"[{file_index}/{total_files}] {error_msg}"
            logger.warning(error_msg)
        return None, None


def count_directory_tokens(directory, tokenizer, file_extensions=None, verbose=False, base_path=None, show_progress=False, file_index_start=0, total_files=None, cumulative_tokens=0, check_restoration=True):
    """
    Count total tokens in all files under a directory
    
    Args:
        directory (Path): Directory path to count
        tokenizer: Pre-loaded tokenizer
        file_extensions (list, optional): List of file extensions to count, if None then count all text files
        verbose (bool): Whether to show statistics for each file
        base_path (Path, optional): Base path for calculating relative paths
        show_progress (bool): Whether to show progress information
        file_index_start (int): Starting file index for progress display
        total_files (int, optional): Total number of files across all paths
        cumulative_tokens (int): Cumulative token count so far
        check_restoration (bool): Whether to check if text can be restored (default: True)
    
    Returns:
        tuple: (total token count, file count, file details list)
    """
    if not directory.exists():
        raise ValueError(f"Directory does not exist: {directory}")
    if not directory.is_dir():
        raise ValueError(f"Path is not a directory: {directory}")
    
    total_tokens = 0
    file_count = 0
    file_details = []
    
    # Default supported text file extensions
    if file_extensions is None:
        file_extensions = DEFAULT_FILE_EXTENSIONS
    
    # Base path for displaying relative paths
    if base_path is None:
        base_path = directory
    
    # Collect all files first
    all_files = []
    for file_path in directory.rglob('*'):
        if file_path.is_file():
            # Check file extension
            if file_extensions and file_path.suffix not in file_extensions:
                continue
            all_files.append(file_path)
    
    # Process each file
    current_cumulative = cumulative_tokens
    for idx, file_path in enumerate(all_files):
        current_index = file_index_start + idx + 1 if show_progress else None
        token_count, file_info = count_file_tokens(
            file_path, tokenizer, verbose, show_progress, 
            current_index, total_files, current_cumulative, check_restoration
        )
        
        if token_count is not None:
            total_tokens += token_count
            current_cumulative += token_count
            file_count += 1
            # Update path to relative path
            if file_info:
                file_info['path'] = str(file_path.relative_to(base_path))
                file_details.append(file_info)
    
    return total_tokens, file_count, file_details


def count_path_tokens(path, tokenizer, file_extensions=None, verbose=False, base_path=None, show_progress=False, file_index_start=0, total_files=None, cumulative_tokens=0, check_restoration=True):
    """
    Count tokens in a path (file or directory)
    
    Args:
        path (str or Path): File or directory path
        tokenizer: Pre-loaded tokenizer
        file_extensions (list, optional): List of file extensions to count
        verbose (bool): Whether to show detailed information
        base_path (Path, optional): Base path for calculating relative paths
        show_progress (bool): Whether to show progress information
        file_index_start (int): Starting file index for progress display
        total_files (int, optional): Total number of files across all paths
        cumulative_tokens (int): Cumulative token count so far
        check_restoration (bool): Whether to check if text can be restored (default: True)
    
    Returns:
        tuple: (total token count, file count, file details list)
    """
    path = Path(path)
    
    if not path.exists():
        raise ValueError(f"Path does not exist: {path}")
    
    if base_path is None:
        base_path = path.parent if path.is_file() else path
    
    if path.is_file():
        # Handle single file
        if file_extensions and path.suffix not in file_extensions:
            return 0, 0, []
        
        current_index = file_index_start + 1 if show_progress else None
        token_count, file_info = count_file_tokens(
            path, tokenizer, verbose, show_progress, 
            current_index, total_files, cumulative_tokens, check_restoration
        )
        
        if token_count is not None and file_info:
            file_info['path'] = str(path.relative_to(base_path))
            return token_count, 1, [file_info]
        else:
            return 0, 0, []
    
    elif path.is_dir():
        # Handle directory
        return count_directory_tokens(
            path, tokenizer, file_extensions, verbose, base_path, 
            show_progress, file_index_start, total_files, cumulative_tokens, check_restoration
        )
    
    else:
        raise ValueError(f"Path is neither a file nor a directory: {path}")


def cmd_count(args):
    """
    Handle the 'count' subcommand - count tokens in files/directories
    """
    try:
        if args.verbose:
            logger.info(f"Using model: {args.model}")
            if args.ext:
                logger.info(f"File extensions: {args.ext}")
            logger.info(f"Number of paths: {len(args.paths)}")
            logger.info("")
        
        # Load tokenizer
        if args.verbose:
            logger.info(f"Loading tokenizer: {args.model}")
        tokenizer = AutoTokenizer.from_pretrained(args.model)
        if args.verbose:
            logger.info("")
        
        # First, collect all files to count total for progress display
        all_files_list = []
        file_extensions = args.ext if args.ext else DEFAULT_FILE_EXTENSIONS
        
        for path_str in args.paths:
            path = Path(path_str)
            if not path.exists():
                continue
            
            if path.is_file():
                if not file_extensions or path.suffix in file_extensions:
                    all_files_list.append(path)
            elif path.is_dir():
                for file_path in path.rglob('*'):
                    if file_path.is_file():
                        if not file_extensions or file_path.suffix in file_extensions:
                            all_files_list.append(file_path)
        
        total_files = len(all_files_list)
        show_progress = True  # Always show progress
        logger.info("")
        
        # Count all paths
        total_tokens = 0
        total_file_count = 0
        all_file_details = []
        path_results = []
        file_index = 0
        files_cannot_restore = []  # List of files that cannot be restored
        
        for path_str in args.paths:
            path = Path(path_str)
            
            if args.verbose:
                path_type = "file" if path.is_file() else "directory" if path.is_dir() else "unknown"
                logger.info(f"Processing path ({path_type}): {path}")
            
            try:
                tokens, file_count, file_details = count_path_tokens(
                    path,
                    tokenizer,
                    file_extensions=args.ext,
                    verbose=args.verbose,
                    show_progress=show_progress,
                    file_index_start=file_index,
                    total_files=total_files,
                    cumulative_tokens=total_tokens,
                    check_restoration=not args.skip_restoration_check
                )
                
                total_tokens += tokens
                total_file_count += file_count
                file_index += file_count
                all_file_details.extend(file_details)
                
                # Collect files that cannot be restored
                for detail in file_details:
                    if 'can_restore' in detail and not detail.get('can_restore', True):
                        files_cannot_restore.append(detail.get('path', 'unknown'))
                
                path_results.append({
                    'path': str(path),
                    'tokens': tokens,
                    'file_count': file_count
                })
                
                if args.verbose:
                    logger.info(f"  -> {file_count} files, {tokens:,} tokens\n")
            
            except Exception as e:
                logger.error(f"  Error: Cannot process path {path}: {e}")
                if args.verbose:
                    logger.info("")
                continue
        
        # Print summary information
        logger.info("")
        logger.info("=" * 60)
        logger.info("Statistics complete!")
        logger.info("=" * 60)
        
        if args.verbose:
            logger.info("\nPath statistics:")
            for result in path_results:
                logger.info(f"  {result['path']}: {result['file_count']} files, {result['tokens']:,} tokens")
            logger.info("")
        
        logger.info(f"Total file count: {total_file_count}")
        logger.info(f"Total token count: {total_tokens:,}")
        if total_file_count > 0:
            logger.info(f"Average per file: {total_tokens // total_file_count:,} tokens")
        logger.info("=" * 60)
        
        # Report files that cannot be restored
        if not args.skip_restoration_check and files_cannot_restore:
            logger.info("")
            logger.error(f"Files that cannot be fully restored: {len(files_cannot_restore)}")
            logger.error("-" * 60)
            for file_path in sorted(files_cannot_restore):
                logger.error(f"  {file_path}")
            logger.error("-" * 60)
        
        return 0
        
    except Exception as e:
        logger.error(f"Error: {e}")
        import traceback
        if args.verbose:
            traceback.print_exc()
        return 1


def cmd_tokenize(args):
    """
    Handle the 'tokenize' subcommand - tokenize text from stdin and pretty print
    """
    try:
        # Load tokenizer
        tokenizer = AutoTokenizer.from_pretrained(args.model)
        
        # Read from stdin
        text = sys.stdin.read()
        pretty_print_tokenize(text, tokenizer)
        return 0
        
    except Exception as e:
        logger.error(f"Error: {e}")
        import traceback
        traceback.print_exc()
        return 1


def cmd_count_jsonl(args):
    """
    Handle the 'count-jsonl' subcommand - count tokens for text field in each JSON object
    """
    try:
        if args.verbose:
            logger.info(f"Using model: {args.model}")
            logger.info(f"Input JSONL file: {args.jsonl_file}")
            logger.info("")
        
        # Load tokenizer
        if args.verbose:
            logger.info(f"Loading tokenizer: {args.model}")
        tokenizer = AutoTokenizer.from_pretrained(args.model)
        if args.verbose:
            logger.info("")
        
        jsonl_path = Path(args.jsonl_file)
        if not jsonl_path.exists():
            logger.error(f"Error: JSONL file does not exist: {jsonl_path}")
            return 1
        
        # Statistics
        total_objects = 0
        total_tokens = 0
        path_token_map = {}  # path -> token count
        objects_without_text = []
        objects_without_path = []
        
        # Read and process JSONL file
        logger.info(f"Processing JSONL file: {jsonl_path}")
        logger.info("")
        
        with open(jsonl_path, 'r', encoding='utf-8') as f:
            for line_num, line in enumerate(f, 1):
                line = line.strip()
                if not line:
                    continue
                
                try:
                    obj = json.loads(line)
                except json.JSONDecodeError as e:
                    logger.warning(f"  Warning: Skipping invalid JSON at line {line_num}: {e}")
                    continue
                
                # Extract text and path fields
                text = obj.get('text', '')
                path = obj.get('meta', {}).get('path', None)
                
                if not text:
                    objects_without_text.append(line_num)
                    if args.verbose:
                        logger.warning(f"  Warning: Object at line {line_num} has no 'text' field")
                    continue
                
                if path is None:
                    objects_without_path.append(line_num)
                    if args.verbose:
                        logger.warning(f"  Warning: Object at line {line_num} has no 'path' field")
                    # Use line number as fallback key
                    path = f"<no_path_line_{line_num}>"
                
                # Count tokens for text field
                token_count, _, _ = count_tokens(text, tokenizer=tokenizer)
                
                # Accumulate statistics
                total_objects += 1
                total_tokens += token_count
                
                # Log with path as key
                if args.verbose:
                    logger.info(f"  [{line_num}] {path}: {token_count:,} tokens (cumulative: {total_tokens:,})")
                else:
                    # Show progress for non-verbose mode
                    if line_num % 100 == 0 or line_num == 1:
                        logger.info(f"  Processing line {line_num}... (cumulative: {total_tokens:,} tokens)")
                
                # Group by path (if same path appears multiple times, sum tokens)
                if path in path_token_map:
                    path_token_map[path] += token_count
                else:
                    path_token_map[path] = token_count
        
        # Print summary
        logger.info("")
        logger.info("=" * 60)
        logger.info("Statistics complete!")
        logger.info("=" * 60)
        logger.info("")
        
        logger.info(f"Total objects processed: {total_objects}")
        logger.info(f"Total token count: {total_tokens:,}")
        if total_objects > 0:
            logger.info(f"Average tokens per object: {total_tokens // total_objects:,}")
        logger.info("")
        
        if objects_without_text:
            logger.warning(f"Objects without 'text' field: {len(objects_without_text)}")
        if objects_without_path:
            logger.warning(f"Objects without 'path' field: {len(objects_without_path)}")
        
        # Print token count by path
        logger.info("")
        logger.info(f"{Colors.GREEN}{Colors.BOLD}Token count by path:{Colors.RESET}")
        logger.info("-" * 60)
        
        # # Sort by token count (descending) or by path (ascending)
        # if args.sort_by_tokens:
        #     sorted_paths = sorted(path_token_map.items(), key=lambda x: x[1], reverse=True)
        # else:
        #     sorted_paths = sorted(path_token_map.items(), key=lambda x: x[0])
        
        # for path, tokens in sorted_paths:
        #     logger.info(f"  {path}: {tokens:,} tokens")
        
        # logger.info("-" * 60)
        # logger.info(f"Total unique paths: {len(path_token_map)}")
        # logger.info("=" * 60)
        
        return 0
        
    except Exception as e:
        logger.error(f"Error: {e}")
        import traceback
        if args.verbose:
            traceback.print_exc()
        return 1


def main():
    """
    Main command-line function with subcommands
    """
    parser = argparse.ArgumentParser(
        description='Tokenize text or count tokens in files/directories',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Count tokens in files/directories (original functionality)
  python tokenizer.py count -m deepseek-ai/DeepSeek-Prover-V1.5-Base /path/to/dir
  python tokenizer.py count -m deepseek-ai/DeepSeek-Prover-V1.5-Base /path/to/file1.py /path/to/dir --verbose
  python tokenizer.py count -m deepseek-ai/DeepSeek-Prover-V1.5-Base dir1 dir2 file1.py --ext .py .json
  
  # Tokenize text from stdin (new functionality)
  python tokenizer.py tokenize -m deepseek-ai/DeepSeek-Prover-V1.5-Base
  echo "Hello world" | python tokenizer.py tokenize -m deepseek-ai/DeepSeek-Prover-V1.5-Base
  
  # Count tokens in JSONL file (new functionality)
  python tokenizer.py count-jsonl -m deepseek-ai/DeepSeek-Prover-V1.5-Base data.jsonl
  python tokenizer.py count-jsonl -m deepseek-ai/DeepSeek-Prover-V1.5-Base data.jsonl --verbose --sort-by-tokens
        """
    )
    
    subparsers = parser.add_subparsers(dest='command', help='Available commands', required=True)
    
    # 'count' subcommand - original functionality
    count_parser = subparsers.add_parser(
        'count',
        help='Count tokens in files or directories',
        description='Count total tokens in files or directories (supports multiple paths)'
    )
    count_parser.add_argument(
        '--model', '-m',
        type=str,
        required=True,
        help='Model name (e.g., deepseek-ai/DeepSeek-Prover-V1.5-Base)'
    )
    count_parser.add_argument(
        'paths',
        nargs='+',
        help='File or directory paths to count (can specify multiple)'
    )
    count_parser.add_argument(
        '--ext', '--extensions',
        nargs='+',
        default=None,
        help='List of file extensions to count (e.g., .py .json), defaults to common text files'
    )
    count_parser.add_argument(
        '--verbose', '-v',
        action='store_true',
        help='Show statistics for each file'
    )
    count_parser.add_argument(
        '--skip-restoration-check',
        action='store_true',
        help='Skip checking if text can be restored from tokens (faster, but won\'t report restoration issues)'
    )
    count_parser.set_defaults(func=cmd_count)
    
    # 'tokenize' subcommand - new functionality
    tokenize_parser = subparsers.add_parser(
        'tokenize',
        help='Tokenize text from stdin and pretty print results',
        description='Read text from stdin, tokenize it, and display detailed tokenization results'
    )
    tokenize_parser.add_argument(
        '--model', '-m',
        type=str,
        required=True,
        help='Model name (e.g., deepseek-ai/DeepSeek-Prover-V1.5-Base)'
    )
    tokenize_parser.set_defaults(func=cmd_tokenize)
    
    # 'count-jsonl' subcommand - new functionality
    count_jsonl_parser = subparsers.add_parser(
        'count-jsonl',
        help='Count tokens for text field in each JSON object from JSONL file',
        description='Read a JSONL file, count tokens for the "text" field of each object, and log by "path" field'
    )
    count_jsonl_parser.add_argument(
        '--model', '-m',
        type=str,
        required=True,
        help='Model name (e.g., deepseek-ai/DeepSeek-Prover-V1.5-Base)'
    )
    count_jsonl_parser.add_argument(
        'jsonl_file',
        type=str,
        help='Path to JSONL file to process'
    )
    count_jsonl_parser.add_argument(
        '--verbose', '-v',
        action='store_true',
        help='Show detailed information for each object'
    )
    count_jsonl_parser.add_argument(
        '--sort-by-tokens',
        action='store_true',
        help='Sort output by token count (descending) instead of by path (ascending)'
    )
    count_jsonl_parser.set_defaults(func=cmd_count_jsonl)
    
    args = parser.parse_args()
    
    # Call the appropriate handler function
    return args.func(args)


if __name__ == "__main__":
    exit(main())