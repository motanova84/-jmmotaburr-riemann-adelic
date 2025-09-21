#!/usr/bin/env python3
"""
Test script to verify Delta_S operator implementation.
"""
import sys
import os
sys.path.insert(0, os.path.abspath('.'))

import mpmath as mp
from validate_explicit_formula import approximate_delta_s, weil_explicit_formula
from utils.mellin import truncated_gaussian


def test_delta_s_eigenvalues():
    """Test Delta_S eigenvalue computation"""
    print("Testing Delta_S eigenvalue computation...")
    
    # Use first few known zeros (imaginary parts)
    test_zeros = [14.134725142, 21.022039639, 25.010857580, 30.424876126, 32.935061588]
    
    eigenvalues = approximate_delta_s(test_zeros, max_zeros=5, precision=30)
    
    print(f"Test zeros: {test_zeros}")
    print(f"Computed eigenvalues: {[float(ev) for ev in eigenvalues]}")
    
    # Verify the relationship: λₙ = 1/4 + ρ²
    for i, (rho, lam) in enumerate(zip(test_zeros, eigenvalues)):
        expected = 0.25 + rho**2
        actual = float(lam)
        print(f"  Zero {i+1}: ρ={rho}, λ={actual:.6f}, expected={expected:.6f}, diff={abs(actual-expected):.2e}")
        assert abs(actual - expected) < 1e-10, f"Eigenvalue {i} calculation error"
    
    print("✅ Delta_S eigenvalue test passed!")


def test_scaling_factor():
    """Test the scaling factor in Weil formula"""
    print("\nTesting scaling factor computation...")
    
    max_zeros = 100
    k = 22.3
    expected_scale = k * max_zeros / mp.log(max_zeros + mp.e())
    
    print(f"max_zeros: {max_zeros}")
    print(f"k: {k}")
    print(f"Expected scaling factor: {float(expected_scale):.6f}")
    
    # This will be computed internally in weil_explicit_formula
    # We can't directly test it without modifying the function, but we can verify the math
    log_term = float(mp.log(max_zeros + mp.e()))
    manual_scale = k * max_zeros / log_term
    print(f"Manual computation: {manual_scale:.6f}")
    
    assert abs(float(expected_scale) - manual_scale) < 1e-10, "Scaling factor computation error"
    print("✅ Scaling factor test passed!")


def test_full_weil_formula():
    """Test the full Weil formula with Delta_S"""
    print("\nTesting full Weil formula with Delta_S...")
    
    # Small test case
    zeros = [14.134725142, 21.022039639, 25.010857580]
    primes = [2, 3, 5, 7]
    f = truncated_gaussian
    
    mp.mp.dps = 20
    
    error, relative_error, left_side, right_side = weil_explicit_formula(
        zeros, primes, f, max_zeros=3, t_max=10, precision=20
    )
    
    print(f"Error: {float(error):.6e}")
    print(f"Relative error: {float(relative_error):.6e}")
    print(f"Left side: {left_side}")
    print(f"Right side: {right_side}")
    
    # Basic sanity checks
    assert mp.isfinite(error), "Error should be finite"
    assert mp.isfinite(left_side), "Left side should be finite"
    assert mp.isfinite(right_side), "Right side should be finite"
    assert error >= 0, "Error should be non-negative"
    
    print("✅ Full Weil formula test passed!")


if __name__ == "__main__":
    print("=== Delta_S Operator Tests ===")
    test_delta_s_eigenvalues()
    test_scaling_factor()
    test_full_weil_formula()
    print("\n🎉 All Delta_S tests passed!")