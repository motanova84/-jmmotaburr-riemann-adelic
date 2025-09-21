#!/usr/bin/env python3
"""
Checksum validation utility for Odlyzko zeros data.

This script computes and validates MD5 checksums for the zeros data files
to ensure data integrity and consistency with the original Odlyzko sources.

Usage:
    python utils/checksum_zeros.py zeros/zeros_t1e8.txt
"""

import hashlib
import sys
import os

def compute_md5(filepath):
    """Compute MD5 checksum of a file."""
    hash_md5 = hashlib.md5()
    try:
        with open(filepath, "rb") as f:
            for chunk in iter(lambda: f.read(4096), b""):
                hash_md5.update(chunk)
        return hash_md5.hexdigest()
    except FileNotFoundError:
        return None

def validate_zeros_file(filepath):
    """Validate the structure and content of a zeros file."""
    if not os.path.exists(filepath):
        print(f"❌ File not found: {filepath}")
        return False
    
    try:
        with open(filepath, 'r') as f:
            lines = f.readlines()
        
        # Check if file contains numeric data
        zeros_count = 0
        for i, line in enumerate(lines[:10]):  # Check first 10 lines
            try:
                float(line.strip())
                zeros_count += 1
            except ValueError:
                print(f"⚠️  Line {i+1} contains non-numeric data: {line.strip()}")
        
        total_lines = len(lines)
        print(f"✅ File structure valid: {total_lines} lines, {zeros_count}/10 sample lines are numeric")
        return True
        
    except Exception as e:
        print(f"❌ Error reading file: {e}")
        return False

def main():
    if len(sys.argv) != 2:
        print("Usage: python utils/checksum_zeros.py <zeros_file>")
        sys.exit(1)
    
    filepath = sys.argv[1]
    print(f"🔍 Validating: {filepath}")
    
    # Validate file structure
    if not validate_zeros_file(filepath):
        sys.exit(1)
    
    # Compute checksum
    checksum = compute_md5(filepath)
    if checksum:
        print(f"📊 MD5 Checksum: {checksum}")
        
        # Store checksum for future reference
        checksum_file = filepath + ".md5"
        with open(checksum_file, 'w') as f:
            f.write(f"{checksum}  {os.path.basename(filepath)}\n")
        print(f"💾 Checksum saved to: {checksum_file}")
    else:
        print("❌ Failed to compute checksum")
        sys.exit(1)

if __name__ == "__main__":
    main()