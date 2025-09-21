"""
Monotonicity validation for Riemann zeta zeros.

This module validates that the imaginary parts of Riemann zeta zeros are 
strictly increasing, which is a fundamental property. It also checks for duplicates.
"""

import os


def check_monotonicity(file_path):
    """
    Check if zeros in file are strictly monotonic (increasing) and have no duplicates.
    
    Args:
        file_path (str): Path to file containing zeros (one per line)
        
    Returns:
        bool: True if data is valid (monotonic and no duplicates), False otherwise
    """
    if not os.path.exists(file_path):
        print(f"❌ File not found: {file_path}")
        return False
        
    zeros = []
    line_count = 0
    
    try:
        with open(file_path, "r") as f:
            for line in f:
                line_count += 1
                try:
                    zero = float(line.strip())
                    zeros.append(zero)
                except ValueError:
                    print(f"❌ Invalid number format at line {line_count}: {line.strip()}")
                    return False
    except IOError as e:
        print(f"❌ Error reading file: {e}")
        return False
    
    if len(zeros) == 0:
        print("❌ No zeros found in file")
        return False
    
    print(f"📊 Loaded {len(zeros)} zeros from {file_path}")
    
    # Check monotonicity
    is_monotonic = all(zeros[i] < zeros[i + 1] for i in range(len(zeros) - 1))
    
    # Check for duplicates
    duplicates = []
    seen = set()
    for z in zeros:
        if z in seen:
            duplicates.append(z)
        seen.add(z)
    
    print(f"Monotonic: {is_monotonic}")
    if duplicates:
        print(f"Duplicates found: {duplicates[:10]}{'...' if len(duplicates) > 10 else ''}")
    else:
        print("Duplicates: None")
    
    # Additional statistics
    if len(zeros) > 1:
        min_gap = min(zeros[i + 1] - zeros[i] for i in range(len(zeros) - 1))
        max_gap = max(zeros[i + 1] - zeros[i] for i in range(len(zeros) - 1))
        avg_gap = (zeros[-1] - zeros[0]) / (len(zeros) - 1) if len(zeros) > 1 else 0
        print(f"Gap statistics - Min: {min_gap:.6f}, Max: {max_gap:.6f}, Avg: {avg_gap:.6f}")
    
    is_valid = is_monotonic and not duplicates
    print(f"Overall validation: {'✅ PASS' if is_valid else '❌ FAIL'}")
    
    return is_valid


if __name__ == "__main__":
    file_path = "zeros/zeros_t1e8.txt"
    is_valid = check_monotonicity(file_path)
    print(f"\nMonotonicity validation: {'✅ PASS' if is_valid else '❌ FAIL'}")