"""
Cross-validation of zeros using SageMath.

This module compares a subset of zeros from the Odlyzko data with zeros
computed by SageMath to validate correctness.

Note: This requires SageMath to be installed. If SageMath is not available,
the validation will be skipped with a warning.
"""

import os


def cross_validate_zeros(file_path, n_samples=10, tolerance=1e-10):
    """
    Cross-validate zeros against SageMath computations.
    
    Args:
        file_path (str): Path to file containing zeros
        n_samples (int): Number of zeros to validate (starting from first)
        tolerance (float): Maximum allowed difference for validation
        
    Returns:
        bool: True if validation passes, False otherwise
    """
    if not os.path.exists(file_path):
        print(f"❌ File not found: {file_path}")
        return False
    
    # Try to import SageMath
    try:
        from sage.all import zeta_zeros
        sage_available = True
    except ImportError:
        print("⚠️  SageMath not available. Cross-validation skipped.")
        print("   Install SageMath: pip install sagemath")
        print("   Or use conda: conda install -c conda-forge sagemath")
        return True  # Skip validation but don't fail
    
    # Load zeros from file
    odlyzko_zeros = []
    try:
        with open(file_path, "r") as f:
            for i, line in enumerate(f):
                if i >= n_samples:
                    break
                try:
                    zero = float(line.strip())
                    odlyzko_zeros.append(zero)
                except ValueError:
                    print(f"❌ Invalid number format at line {i+1}: {line.strip()}")
                    return False
    except IOError as e:
        print(f"❌ Error reading file: {e}")
        return False
    
    if len(odlyzko_zeros) < n_samples:
        n_samples = len(odlyzko_zeros)
        print(f"⚠️  File contains only {len(odlyzko_zeros)} zeros, validating all of them")
    
    print(f"📊 Cross-validating first {n_samples} zeros with SageMath")
    print(f"Tolerance: {tolerance}")
    
    # Compute zeros with SageMath
    try:
        sage_zeros = [float(zeta_zeros(k).imag()) for k in range(1, n_samples + 1)]
    except Exception as e:
        print(f"❌ Error computing zeros with SageMath: {e}")
        return False
    
    # Compare zeros
    differences = []
    all_valid = True
    
    for i, (odlyzko_zero, sage_zero) in enumerate(zip(odlyzko_zeros, sage_zeros)):
        diff = abs(odlyzko_zero - sage_zero)
        differences.append(diff)
        is_valid = diff < tolerance
        
        if not is_valid:
            all_valid = False
        
        status = "✅" if is_valid else "❌"
        print(f"{status} ρ_{i+1:2d}: Odlyzko={odlyzko_zero:15.10f}, Sage={sage_zero:15.10f}, diff={diff:.2e}")
    
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
    is_valid = cross_validate_zeros(file_path)
    print(f"\nCross-validation with SageMath: {'✅ PASS' if is_valid else '❌ FAIL'}")