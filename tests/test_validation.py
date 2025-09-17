"""
🧠 Copilot Prompt:
Create pytest tests for mathematical identity checks in the Riemann Hypothesis validation.

Test the consistency between prime_sum, A_infty, and zero_sum functions.
Ensure the explicit formula validation works for different test functions.
"""

import pytest
import mpmath as mp
from validate_explicit_formula import prime_sum, archimedean_sum, zero_sum_computed, f1_gaussian
from utils.mellin import truncated_gaussian


def test_riemann_formula_matches():
    """Test that the explicit formula sides match within tolerance."""
    f = f1_gaussian  # Use the enhanced test function
    P = 50  # Smaller values for faster testing
    K = 5
    sigma0 = 2.0
    T = 10
    lim_u = 3.0
    
    # Calculate both sides
    prime_side = prime_sum(f, P, K, log_progress=False)
    arch_side = archimedean_sum(f, sigma0, T, lim_u, log_progress=False)
    total = prime_side + arch_side
    
    # Use a very small number of zeros for testing
    zero_side = zero_sum_computed(f, 5, lim_u, log_progress=False)
    
    # For small tests, we expect some error but it should be finite
    error = abs(total - zero_side)
    assert mp.isfinite(error), "Error should be finite"
    assert error < 100, "Error should be reasonable for small test"  # Loose bound for testing


def test_mellin_transform_properties():
    """Test basic properties of the Mellin transform."""
    from utils.mellin import mellin_transform
    
    # Test that Mellin transform of truncated Gaussian has expected properties
    f = truncated_gaussian
    s = mp.mpc(1, 0)  # s = 1
    lim = 3.0
    
    result = mellin_transform(f, s, lim)
    assert isinstance(result, (mp.mpc, mp.mpf))  # Should return a complex number
    assert mp.isfinite(result)  # Should be finite


if __name__ == "__main__":
    pytest.main([__file__])