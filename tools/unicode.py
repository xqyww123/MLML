#!/usr/bin/env python3
"""
Script to convert *.thy files between ASCII and Unicode notation.

Usage:
    python unicode.py --to-unicode dir1 dir2 file1.thy ...
    python unicode.py --to-ascii dir1 dir2 file1.thy ...
"""

import argparse
import glob
import os
from pathlib import Path
from IsaREPL import Client


def find_thy_files(paths):
    """Find all *.thy files in the given paths."""
    thy_files = []
    for path_str in paths:
        # If it's a .thy file directly, add it
        if path_str.endswith('.thy') and os.path.isfile(path_str):
            thy_files.append(Path(path_str))
        # Also search recursively for *.thy files
        pattern = os.path.join(path_str, '**', '*.thy')
        found = glob.glob(pattern, recursive=True)
        thy_files.extend([Path(f) for f in found])
    
    return sorted(set(thy_files))  # Remove duplicates and sort


def convert_file(file_path, to_unicode=True):
    """Convert a single .thy file."""
    try:
        # Read the file
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # Convert the content
        if to_unicode:
            converted = Client.unicode_of_ascii(content)
            direction = "unicode"
        else:
            converted = Client.ascii_of_unicode(content)
            direction = "ASCII"
        
        # Write the converted content
        with open(file_path, 'w', encoding='utf-8') as f:
            f.write(converted)
        
        print(f"✓ Converted {file_path} to {direction}")
        
        return True
    except Exception as e:
        print(f"✗ Error converting {file_path}: {e}")
        return False


def main():
    parser = argparse.ArgumentParser(
        description='Convert *.thy files between ASCII and Unicode notation',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Convert to unicode
  python unicode.py --to-unicode dir1/ dir2/ file.thy
  
  # Convert to ASCII
  python unicode.py --to-ascii dir1/ dir2/ file.thy
        """
    )
    
    # Direction flags (mutually exclusive)
    direction_group = parser.add_mutually_exclusive_group(required=True)
    direction_group.add_argument(
        '--to-unicode',
        action='store_true',
        help='Convert from ASCII to Unicode'
    )
    direction_group.add_argument(
        '--to-ascii',
        action='store_true',
        help='Convert from Unicode to ASCII'
    )
    
    parser.add_argument(
        'paths',
        nargs='+',
        help='Directories or files to process'
    )
    
    args = parser.parse_args()
    
    # Find all .thy files
    thy_files = find_thy_files(args.paths)
    
    if not thy_files:
        print("No .thy files found in the given paths.")
        return
    
    print(f"Found {len(thy_files)} .thy file(s) to process")
    print(f"Direction: {'ASCII → Unicode' if args.to_unicode else 'Unicode → ASCII'}")
    print()
    
    # Process each file
    success_count = 0
    for file_path in thy_files:
        if convert_file(file_path, to_unicode=args.to_unicode):
            success_count += 1
    
    print()
    print(f"Processed {success_count}/{len(thy_files)} files successfully")


if __name__ == '__main__':
    main()
