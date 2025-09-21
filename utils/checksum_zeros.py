"""
🧠 Copilot Prompt:
Create a checksum validation utility for zeros_t1e8.txt to ensure data integrity.

This script validates that:
- File exists and is readable
- Contains numeric values (one per line)
- Has reasonable size and format
- Basic sanity checks on zero values

Usage in GitHub Actions workflow for data validation.
"""

import os
import sys
import hashlib


def validate_zeros_file(filename="zeros/zeros_t1e8.txt"):
    """Validate the zeros file for basic integrity."""
    
    if not os.path.exists(filename):
        print(f"❌ Zeros file not found: {filename}")
        return False
    
    print(f"✅ Found zeros file: {filename}")
    
    # Check file size (should be reasonable for zeros data)
    file_size = os.path.getsize(filename)
    print(f"📏 File size: {file_size:,} bytes")
    
    if file_size < 1000:  # Too small
        print("❌ File too small to contain meaningful zero data")
        return False
    
    if file_size > 10_000_000:  # > 10MB seems excessive for CI
        print("⚠️  Large file detected - may impact CI performance")
    
    # Validate file content
    try:
        with open(filename, 'r') as f:
            lines = 0
            valid_zeros = 0
            
            for i, line in enumerate(f):
                lines += 1
                if lines > 100000:  # Don't read entire huge files in CI
                    break
                    
                line = line.strip()
                if not line:
                    continue
                    
                try:
                    zero_val = float(line)
                    
                    # Basic sanity check: zeros should be positive and in reasonable range
                    if 10.0 <= zero_val <= 1e12:  # Reasonable range for Riemann zeros
                        valid_zeros += 1
                    else:
                        print(f"⚠️  Line {i+1}: unusual zero value {zero_val}")
                        
                except ValueError:
                    print(f"❌ Line {i+1}: invalid numeric value '{line}'")
                    return False
            
            print(f"✅ Validated {valid_zeros} zeros from {lines} lines")
            
            if valid_zeros < 10:
                print("❌ Too few valid zeros found")
                return False
                
            return True
            
    except Exception as e:
        print(f"❌ Error reading file: {e}")
        return False


def compute_file_hash(filename="zeros/zeros_t1e8.txt", algorithm="md5"):
    """Compute file hash for integrity checking."""
    if not os.path.exists(filename):
        return None
        
    hash_obj = hashlib.new(algorithm)
    
    try:
        with open(filename, 'rb') as f:
            # Read in chunks to handle large files
            for chunk in iter(lambda: f.read(4096), b""):
                hash_obj.update(chunk)
        
        file_hash = hash_obj.hexdigest()
        print(f"🔐 File {algorithm.upper()}: {file_hash}")
        return file_hash
        
    except Exception as e:
        print(f"❌ Error computing hash: {e}")
        return None


def main():
    """Main validation function."""
    zeros_file = "zeros/zeros_t1e8.txt"
    
    print("🔍 Validating Riemann zeros data...")
    
    # Basic file validation
    if not validate_zeros_file(zeros_file):
        print("❌ Zeros file validation FAILED")
        sys.exit(1)
    
    # Compute integrity hash
    file_hash = compute_file_hash(zeros_file)
    if file_hash:
        print("🔐 File hash computed successfully")
    
    print("✅ Zeros file validation PASSED")
    return 0


if __name__ == "__main__":
    main()