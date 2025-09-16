"""
🧠 Copilot Prompt:
Create pytest tests for mathematical identity checks in the Riemann Hypothesis validation.

Test the consistency between prime_sum, A_infty, and zero_sum functions.
Ensure the explicit formula validation works for different test functions.
"""

import pytest
import mpmath as mp
import os
from validate_explicit_formula import prime_sum, archimedean_sum, zero_sum_limited
from utils.mellin import truncated_gaussian, mellin_transform

# Set precision for consistent testing
mp.mp.dps = 15

class TestMathematicalIdentities:
    """Test suite for mathematical identity validation."""
    
    def test_prime_sum_properties(self):
        """Test properties of the prime sum function."""
        f = truncated_gaussian
        P = 50  # Small for fast testing
        K = 3
        
        # Prime sum should be finite and real
        result = prime_sum(f, P, K)
        assert mp.isfinite(result)
        assert isinstance(result, (mp.mpf, float))
        
        # Monotonicity test: more primes should generally increase the sum (for positive f)
        result_smaller = prime_sum(f, P//2, K)
        # This isn't always true due to the nature of the function, but let's check they're different
        assert result != result_smaller
    
    def test_archimedean_sum_properties(self):
        """Test properties of the archimedean sum."""
        f = truncated_gaussian
        sigma0 = 2.0
        T = 5  # Small for fast testing
        lim_u = 3.0
        
        result = archimedean_sum(f, sigma0, T, lim_u)
        assert mp.isfinite(result)
        assert isinstance(result, (mp.mpf, float, complex))
        
        # Result should be real for real sigma0
        if isinstance(result, complex):
            assert abs(result.imag) < 1e-10, f"Imaginary part too large: {result.imag}"

    def test_zero_sum_with_mock_data(self):
        """Test zero sum function with mock zeros data."""
        f = truncated_gaussian
        lim_u = 3.0
        
        # Create mock zeros file for testing
        mock_zeros_file = '/tmp/test_zeros.txt'
        with open(mock_zeros_file, 'w') as file:
            # Write some mock zeros (first few non-trivial zeros approximately)
            zeros = [14.134725, 21.022040, 25.010858, 30.424876, 32.935062]
            for zero in zeros:
                file.write(f"{zero}\n")
        
        try:
            result = zero_sum_limited(f, mock_zeros_file, 5, lim_u)
            assert mp.isfinite(result)
            assert isinstance(result, (mp.mpf, float))
        finally:
            # Clean up
            if os.path.exists(mock_zeros_file):
                os.remove(mock_zeros_file)

    @pytest.mark.skipif(not os.path.exists('zeros/zeros_t1e8.txt'), 
                        reason="Zeros data file not available")
    def test_riemann_formula_with_real_data(self):
        """Test the explicit formula with real zeros data (if available)."""
        f = truncated_gaussian
        P = 100  # Small for fast testing
        K = 5
        sigma0 = 2.0
        T = 10
        lim_u = 3.0
        max_zeros = 50  # Use only first 50 zeros for speed
        
        # Calculate arithmetic side
        prime_side = prime_sum(f, P, K)
        arch_side = archimedean_sum(f, sigma0, T, lim_u)
        arithmetic_total = prime_side + arch_side
        
        # Calculate zero side
        zeros_file = 'zeros/zeros_t1e8.txt'
        zero_side = zero_sum_limited(f, zeros_file, max_zeros, lim_u)
        
        # The error should be finite (not requiring exact match due to truncations)
        error = abs(arithmetic_total - zero_side)
        assert mp.isfinite(error)
        
        # For small parameters, we expect reasonable agreement
        # This is more of a smoke test than an exact validation
        assert error < 100, f"Error too large: {error}"

    def test_mellin_transform_properties(self):
        """Test basic properties of the Mellin transform."""
        f = truncated_gaussian
        
        # Test at different values of s
        test_points = [mp.mpc(1, 0), mp.mpc(0.5, 5), mp.mpc(2, -3)]
        lim = 3.0
        
        for s in test_points:
            result = mellin_transform(f, s, lim)
            assert isinstance(result, (mp.mpc, mp.mpf))
            assert mp.isfinite(result), f"Non-finite result at s={s}: {result}"
    
    def test_mellin_transform_symmetry(self):
        """Test symmetry properties of Mellin transform."""
        f = truncated_gaussian
        lim = 3.0
        
        # Test that conjugate symmetry holds for real functions
        s = mp.mpc(1, 2)
        s_conj = mp.mpc(1, -2)
        
        result1 = mellin_transform(f, s, lim)
        result2 = mellin_transform(f, s_conj, lim)
        
        # For real functions, M[f](s*) = M[f](s)*
        assert abs(result1 - mp.conj(result2)) < 1e-10
    
    def test_reproducibility(self):
        """Test that calculations are reproducible with same parameters."""
        # This tests the specified parameters: δ = 0.01, P = 1000, K = 50, etc.
        f = truncated_gaussian
        P = 50  # Reduced for speed in testing
        K = 10  # Reduced for speed
        
        # Run the same calculation twice
        result1 = prime_sum(f, P, K)
        result2 = prime_sum(f, P, K)
        
        # Results should be identical (reproducible)
        assert result1 == result2
        
        # Test archimedean sum reproducibility
        sigma0 = 2.0
        T = 10
        lim_u = 3.0
        
        arch1 = archimedean_sum(f, sigma0, T, lim_u)
        arch2 = archimedean_sum(f, sigma0, T, lim_u)
        
        # Allow small numerical differences due to quadrature
        assert abs(arch1 - arch2) < 1e-12

    def test_parameter_validation(self):
        """Test that functions handle parameter edge cases properly."""
        f = truncated_gaussian
        
        # Test with minimum parameters
        result = prime_sum(f, 10, 1)  # Only primes up to 10, K=1
        assert mp.isfinite(result)
        
        # Test archimedean sum with small T
        result = archimedean_sum(f, 2.0, 1, 3.0)
        assert mp.isfinite(result)


if __name__ == "__main__":
    pytest.main([__file__, "-v"])