import hashlib
import os

def compute_checksum(file_path):
    """Compute MD5 checksum of a file."""
    hash_md5 = hashlib.md5()
    with open(file_path, "rb") as f:
        for chunk in iter(lambda: f.read(4096), b""):
            hash_md5.update(chunk)
    return hash_md5.hexdigest()

def validate_zeros_file(file_path="zeros/zeros_t1e8.txt"):
    """Validate the zeros file exists and compute its checksum."""
    if not os.path.exists(file_path):
        print(f"❌ Zeros file not found: {file_path}")
        return None
    
    checksum = compute_checksum(file_path)
    print(f"✅ Zeros file found: {file_path}")
    print(f"📊 MD5 Checksum: {checksum}")
    
    # Count lines
    with open(file_path, 'r') as f:
        line_count = sum(1 for _ in f)
    print(f"📈 Number of zeros: {line_count}")
    
    return checksum

if __name__ == "__main__":
    import sys
    file_path = sys.argv[1] if len(sys.argv) > 1 else "zeros/zeros_t1e8.txt"
    validate_zeros_file(file_path)