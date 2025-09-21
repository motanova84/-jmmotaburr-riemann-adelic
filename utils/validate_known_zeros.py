"""
Known zeros validation for Riemann zeta function.

This module validates the first few zeros against well-known high-precision values
to ensure the data file contains correct zeros.
"""

import os


def validate_known_zeros(file_path, tolerance=1e-9):
    """
    Validate the first few zeros against known high-precision values.
    
    Args:
        file_path (str): Path to file containing zeros
        tolerance (float): Maximum allowed difference for validation
        
    Returns:
        bool: True if all known zeros match within tolerance, False otherwise
    """
    # First few non-trivial zeros of the Riemann zeta function (high precision)
    # Source: A.M. Odlyzko and other high-precision computations
    known_zeros = [
        14.134725141734693790457251983562470270784257115699243,  # ρ₁
        21.022039638771554992628479593896902777334321596861149,  # ρ₂
        25.010857580145688763213790992562821818659549672557996,  # ρ₃
        30.424876126678895463316942653315505456064715571547205,  # ρ₄
        32.935061587739189690662368964074903488812715603517039,  # ρ₅
        37.586178158825671257217763480705332821405597350830793,  # ρ₆
        40.918719012147495187398126914633254395726165962778430,  # ρ₇
        43.327073280914999519496122165482069025637177504196206,  # ρ₈
        48.005150881167159727942472749427516074646191310977772,  # ρ₉
        49.773832477672302181916784678563724057723178299677727   # ρ₁₀
    ]
    
    if not os.path.exists(file_path):
        print(f"❌ File not found: {file_path}")
        return False
    
    file_zeros = []
    try:
        with open(file_path, "r") as f:
            for i, line in enumerate(f):
                if i >= len(known_zeros):
                    break
                try:
                    zero = float(line.strip())
                    file_zeros.append(zero)
                except ValueError:
                    print(f"❌ Invalid number format at line {i+1}: {line.strip()}")
                    return False
    except IOError as e:
        print(f"❌ Error reading file: {e}")
        return False
    
    if len(file_zeros) < len(known_zeros):
        print(f"⚠️  File contains only {len(file_zeros)} zeros, but {len(known_zeros)} known zeros available for validation")
        known_zeros = known_zeros[:len(file_zeros)]
    
    print(f"📊 Validating first {len(known_zeros)} zeros against known values")
    print(f"Tolerance: {tolerance}")
    
    differences = []
    all_valid = True
    
    for i, (file_zero, known_zero) in enumerate(zip(file_zeros, known_zeros)):
        diff = abs(file_zero - known_zero)
        differences.append(diff)
        is_valid = diff < tolerance
        
        if not is_valid:
            all_valid = False
        
        status = "✅" if is_valid else "❌"
        print(f"{status} ρ_{i+1:2d}: {file_zero:18.12f} (known: {known_zero:18.12f}, diff: {diff:.2e})")
    
    if differences:
        max_diff = max(differences)
        avg_diff = sum(differences) / len(differences)
        print(f"\nStatistics:")
        print(f"  Max difference: {max_diff:.2e}")
        print(f"  Avg difference: {avg_diff:.2e}")
        print(f"  All within tolerance: {'✅ YES' if all_valid else '❌ NO'}")
    
    return all_valid


if __name__ == "__main__":
    file_path = "zeros/zeros_t1e8.txt"
    is_valid = validate_known_zeros(file_path)
    print(f"\nKnown zeros validation: {'✅ PASS' if is_valid else '❌ FAIL'}")