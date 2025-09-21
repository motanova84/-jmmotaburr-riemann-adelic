"""
Checksum validation utility for Odlyzko zeros data.
Computes and validates MD5 checksums to ensure data integrity.
"""

import hashlib
import os
import sys

def compute_checksum(file_path):
    """Compute MD5 checksum of a file."""
    if not os.path.exists(file_path):
        raise FileNotFoundError(f"File not found: {file_path}")
    
    hash_md5 = hashlib.md5()
    with open(file_path, "rb") as f:
        for chunk in iter(lambda: f.read(4096), b""):
            hash_md5.update(chunk)
    return hash_md5.hexdigest()

def validate_checksum(file_path, expected_checksum):
    """Validate file checksum against expected value."""
    actual_checksum = compute_checksum(file_path)
    return actual_checksum == expected_checksum

# Known checksums for Odlyzko data files
# Updated with computed checksums from verified data
KNOWN_CHECKSUMS = {
    "zeros/zeros_t1e8.txt": "b7b8be60df6d46e78cd60874f9fd76c0",  # MD5 of current verified file
}

def main():
    """Main function to compute or validate checksums."""
    if len(sys.argv) < 2:
        print("Usage: python checksum_zeros.py <file_path> [expected_checksum]")
        print("       python checksum_zeros.py --validate-all")
        sys.exit(1)
    
    if sys.argv[1] == "--validate-all":
        print("🔍 Validating all known checksums...")
        all_valid = True
        
        for file_path, expected_checksum in KNOWN_CHECKSUMS.items():
            if expected_checksum is None:
                if os.path.exists(file_path):
                    checksum = compute_checksum(file_path)
                    print(f"📋 {file_path}: {checksum} (not validated - checksum unknown)")
                else:
                    print(f"⚠️  {file_path}: File not found")
                continue
                
            if os.path.exists(file_path):
                if validate_checksum(file_path, expected_checksum):
                    print(f"✅ {file_path}: Checksum valid")
                else:
                    print(f"❌ {file_path}: Checksum mismatch!")
                    actual = compute_checksum(file_path)
                    print(f"   Expected: {expected_checksum}")
                    print(f"   Actual:   {actual}")
                    all_valid = False
            else:
                print(f"⚠️  {file_path}: File not found")
                all_valid = False
        
        if not all_valid:
            sys.exit(1)
        else:
            print("✅ All checksums valid!")
            
    else:
        file_path = sys.argv[1]
        
        if len(sys.argv) == 3:
            # Validate against expected checksum
            expected_checksum = sys.argv[2]
            if validate_checksum(file_path, expected_checksum):
                print(f"✅ Checksum valid for {file_path}")
            else:
                actual = compute_checksum(file_path)
                print(f"❌ Checksum mismatch for {file_path}")
                print(f"Expected: {expected_checksum}")
                print(f"Actual:   {actual}")
                sys.exit(1)
        else:
            # Just compute and display checksum
            checksum = compute_checksum(file_path)
            print(f"MD5 Checksum for {file_path}: {checksum}")

if __name__ == "__main__":
    main()