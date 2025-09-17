# 🚀 Copilot Objective:
# Create comprehensive pytest tests for mathematical identity checks in the Riemann Hypothesis validation.
#
# Test the consistency between prime_sum, A_infty, and zero_sum functions.
# Ensure the explicit formula validation works for different test functions.
# Validate enhanced features: error tolerance, JMMB signature coherence, verbose logging.
#
# ✧ Goal: Verify that all mathematical functions work correctly and produce consistent results
# ✧ Test both the individual components and the integrated validation system
# ✧ Ensure JMMB Ψ✧ signature enhancements don't break mathematical correctness

"""
Enhanced Test Suite for Riemann Hypothesis Validation
=====================================================

Tests mathematical functions, validation logic, and Copilot-aware features
including JMMB Ψ✧ signature coherence and enhanced error analysis.
"""

import pytest
import mpmath as mp
import os
import tempfile
from validate_explicit_formula import (
    prime_sum, archimedean_sum, zero_sum_limited, 
    validate_formula_convergence, JMMB_FREQUENCY, DEFAULT_TOLERANCE
)
from utils.mellin import truncated_gaussian


class TestMathematicalFunctions:
    """Test core mathematical functions for correctness."""
    
    def test_prime_sum_basic(self):
        """Test that prime_sum produces finite, reasonable results."""
        f = truncated_gaussian
        P = 50  # Small for fast testing
        K = 3
        
        result = prime_sum(f, P, K, verbose=False)
        
        assert isinstance(result, (mp.mpf, mp.mpc))
        assert mp.isfinite(result)
        assert result > 0  # Should be positive for truncated Gaussian
        
    def test_archimedean_sum_basic(self):
        """Test that archimedean_sum produces finite results."""
        f = truncated_gaussian
        sigma0 = 2.0
        T = 5  # Small for fast testing
        lim_u = 2.0
        
        result = archimedean_sum(f, sigma0, T, lim_u, verbose=False)
        
        assert isinstance(result, (mp.mpf, mp.mpc))
        assert mp.isfinite(result)
        
    def test_zero_sum_with_mock_file(self):
        """Test zero_sum_limited with a mock zeros file."""
        f = truncated_gaussian
        
        # Create temporary zeros file
        with tempfile.NamedTemporaryFile(mode='w', delete=False, suffix='.txt') as tmp:
            # Write some mock zeros (imaginary parts)
            test_zeros = ['14.134725', '21.022040', '25.010858', '30.424876']
            for zero in test_zeros:
                tmp.write(f"{zero}\n")
            tmp_name = tmp.name
        
        try:
            result = zero_sum_limited(f, tmp_name, max_zeros=3, lim_u=2.0, verbose=False)
            
            assert isinstance(result, (mp.mpf, mp.mpc))
            assert mp.isfinite(result)
            
        finally:
            os.unlink(tmp_name)
    
    def test_jmmb_frequency_constant(self):
        """Test that JMMB frequency constant is properly defined."""
        assert isinstance(JMMB_FREQUENCY, (int, float))
        assert JMMB_FREQUENCY == 141.7001
        assert JMMB_FREQUENCY > 0


class TestValidationLogic:
    """Test the validation and error analysis logic."""
    
    def test_validate_formula_convergence_pass(self):
        """Test validation when formula converges."""
        A = mp.mpf('1.0')
        Z = mp.mpf('1.0000001')  # Very close
        tolerance = mp.mpf('1e-6')
        
        is_valid, error, rel_error, analysis = validate_formula_convergence(
            A, Z, tolerance, verbose=False
        )
        
        assert is_valid == True
        assert error < tolerance
        assert isinstance(analysis, dict)
        assert 'coherence_factor' in analysis
        assert 'jmmb_signature' in analysis
        
    def test_validate_formula_convergence_fail(self):
        """Test validation when formula doesn't converge."""
        A = mp.mpf('1.0')
        Z = mp.mpf('2.0')  # Far apart
        tolerance = mp.mpf('1e-6')
        
        is_valid, error, rel_error, analysis = validate_formula_convergence(
            A, Z, tolerance, verbose=False
        )
        
        assert is_valid == False
        assert error > tolerance
        assert rel_error > 0
        
    def test_validate_formula_edge_cases(self):
        """Test validation with edge cases."""
        # Test with zero values
        A = mp.mpf('0.0')
        Z = mp.mpf('1e-10')
        tolerance = mp.mpf('1e-6')
        
        is_valid, error, rel_error, analysis = validate_formula_convergence(
            A, Z, tolerance, verbose=False
        )
        
        assert isinstance(is_valid, bool)
        assert error >= 0
        assert rel_error >= 0 or rel_error == mp.inf


class TestIntegratedValidation:
    """Test the complete validation system."""
    
    def test_small_scale_validation(self):
        """Test complete validation with very small parameters."""
        # This test uses the actual validation logic but with minimal parameters
        f = truncated_gaussian
        P = 20  # Very small for speed
        K = 2
        sigma0 = 2.0
        T = 1
        lim_u = 1.5
        
        # Compute arithmetic side
        prime_part = prime_sum(f, P, K, verbose=False)
        arch_part = archimedean_sum(f, sigma0, T, lim_u, verbose=False)
        A = prime_part + arch_part
        
        # Mock zero side (since we need actual zeros file for real test)
        Z = A * mp.mpf('0.9')  # Simulate 10% difference
        
        # Test validation
        is_valid, error, rel_error, analysis = validate_formula_convergence(
            A, Z, DEFAULT_TOLERANCE, verbose=False
        )
        
        # Should fail with this large difference
        assert is_valid == False
        assert error > 0
        assert isinstance(analysis['coherence_factor'], (mp.mpf, mp.mpc))
        
    def test_mellin_transform_properties(self):
        """Test basic properties of the Mellin transform."""
        from utils.mellin import mellin_transform
        
        f = truncated_gaussian
        s = mp.mpc(1, 0)  # s = 1
        lim = 2.0
        
        result = mellin_transform(f, s, lim)
        assert isinstance(result, (mp.mpc, mp.mpf))
        assert mp.isfinite(result)
        
        # Test with different s values
        s2 = mp.mpc(2, 1)  # s = 2 + i
        result2 = mellin_transform(f, s2, lim)
        assert isinstance(result2, (mp.mpc, mp.mpf))
        assert mp.isfinite(result2)


class TestCopilotAwareness:
    """Test Copilot-specific enhancements and features."""
    
    def test_enhanced_precision_handling(self):
        """Test that enhanced precision settings work correctly."""
        original_dps = mp.mp.dps
        
        try:
            # Test with different precision levels
            mp.mp.dps = 15
            f = truncated_gaussian
            result1 = prime_sum(f, 10, 2, verbose=False)
            
            mp.mp.dps = 25
            result2 = prime_sum(f, 10, 2, verbose=False)
            
            # Results should be similar but not identical due to precision
            assert isinstance(result1, (mp.mpf, mp.mpc))
            assert isinstance(result2, (mp.mpf, mp.mpc))
            assert mp.isfinite(result1)
            assert mp.isfinite(result2)
            
        finally:
            mp.mp.dps = original_dps
    
    def test_error_tolerance_levels(self):
        """Test different error tolerance levels."""
        A = mp.mpf('1.0')
        Z = mp.mpf('1.00001')  # Small difference
        
        # Test strict tolerance
        strict_tolerance = mp.mpf('1e-8')
        is_valid_strict, _, _, _ = validate_formula_convergence(
            A, Z, strict_tolerance, verbose=False
        )
        
        # Test relaxed tolerance  
        relaxed_tolerance = mp.mpf('1e-4')
        is_valid_relaxed, _, _, _ = validate_formula_convergence(
            A, Z, relaxed_tolerance, verbose=False
        )
        
        # Relaxed should pass where strict fails
        assert is_valid_relaxed == True
        assert is_valid_strict == False


if __name__ == "__main__":
    pytest.main([__file__, '-v'])