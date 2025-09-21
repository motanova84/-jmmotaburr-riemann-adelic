"""
Checksum validation for Odlyzko zeros data files.

This module provides functions to compute and validate checksums (MD5 and SHA256)
for Odlyzko zeros data files to ensure data integrity during download and storage.
"""

import hashlib
import os


def compute_checksum(file_path, hash_type="md5"):
    """
    Compute MD5 or SHA256 checksum for a file.
    
    Args:
        file_path (str): Path to the file to checksum
        hash_type (str): Either "md5" or "sha256"
        
    Returns:
        str: Hexadecimal representation of the checksum
    """
    hash_func = hashlib.md5() if hash_type == "md5" else hashlib.sha256()
    
    with open(file_path, "rb") as f:
        for chunk in iter(lambda: f.read(4096), b""):
            hash_func.update(chunk)
    return hash_func.hexdigest()


def validate_checksum(file_path, expected_checksum, hash_type="md5"):
    """
    Validate a file's checksum against an expected value.
    
    Args:
        file_path (str): Path to the file to validate
        expected_checksum (str): Expected checksum value
        hash_type (str): Either "md5" or "sha256"
        
    Returns:
        bool: True if checksums match, False otherwise
    """
    computed_checksum = compute_checksum(file_path, hash_type)
    is_valid = computed_checksum == expected_checksum
    print(f"Checksum {hash_type.upper()}: {computed_checksum} (Expected: {expected_checksum}, Valid: {is_valid})")
    return is_valid


if __name__ == "__main__":
    file_path = "zeros/zeros_t1e8.txt"
    
    # Check if file exists
    if not os.path.exists(file_path):
        print(f"❌ File not found: {file_path}")
        exit(1)
    
    # Compute checksums for reference (these would be replaced with known values from Odlyzko)
    md5_checksum = compute_checksum(file_path, "md5")
    sha256_checksum = compute_checksum(file_path, "sha256")
    
    print(f"📄 File: {file_path}")
    print(f"MD5:    {md5_checksum}")
    print(f"SHA256: {sha256_checksum}")
    print()
    print("✅ Checksums computed successfully")
    print("Note: Replace these computed values with known checksums from Odlyzko source for validation")