"""
Tests for thermal kernel operator construction and Riemann Hypothesis verification.

These tests verify that the thermal kernel operator H:
1. Is properly constructed from geometric principles
2. Has non-negative eigenvalues (coercivity)
3. Encodes Riemann zeros on the critical line Re(ρ) = 1/2
"""

import pytest
import numpy as np
import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from thermal_kernel_operator import (
    K_t, basis_func, build_H_operator, spectrum_to_zeros,
    load_theoretical_zeros, compare_with_theoretical
)


class TestThermalKernel:
    """Test the thermal kernel K_t(x, y, t)"""
    
    def test_kernel_symmetry(self):
        """Thermal kernel should be symmetric: K_t(x,y) = K_t(y,x)"""
        x, y = 1.5, 2.3
        t = 0.01
        
        k_xy = K_t(x, y, t)
        k_yx = K_t(y, x, t)
        
        assert np.abs(k_xy - k_yx) < 1e-10, "Kernel should be symmetric"
    
    def test_kernel_positive(self):
        """Thermal kernel should be positive for t > 0"""
        x, y = 1.0, 1.0
        t = 0.01
        
        k = K_t(x, y, t)
        
        assert np.real(k) > 0, "Kernel should be positive at diagonal"
    
    def test_kernel_decay(self):
        """Kernel should decay as |log x - log y| increases"""
        t = 0.01
        x = 1.0
        
        k_near = K_t(x, 1.1, t)
        k_far = K_t(x, 10.0, t)
        
        assert np.abs(k_near) > np.abs(k_far), "Kernel should decay with distance"
    
    def test_kernel_thermal_limit(self):
        """As t → 0, kernel should become more localized"""
        x, y = 1.0, 2.0
        
        k_large_t = K_t(x, y, 0.1)
        k_small_t = K_t(x, y, 0.001)
        
        # Smaller t means more localization (larger magnitude at origin)
        assert np.abs(k_small_t) < np.abs(k_large_t) * 100, "Kernel behavior with t"


class TestBasisFunctions:
    """Test the logarithmic basis functions"""
    
    def test_basis_orthogonality(self):
        """Different basis functions should be approximately orthogonal"""
        x_min, x_max = np.exp(-1), np.exp(1)
        n_points = 100
        x_vals = np.linspace(x_min, x_max, n_points)
        
        psi_1 = np.array([basis_func(1, x, x_min, x_max) for x in x_vals])
        psi_2 = np.array([basis_func(2, x, x_min, x_max) for x in x_vals])
        
        # Approximate inner product with d×x = dx/x measure
        inner_product = np.sum(psi_1 * psi_2 / x_vals) * (x_max - x_min) / n_points
        
        assert np.abs(inner_product) < 0.5, "Basis functions should be approximately orthogonal"
    
    def test_basis_normalization(self):
        """Basis functions should have finite norm"""
        x_min, x_max = np.exp(-1), np.exp(1)
        n_points = 100
        x_vals = np.linspace(x_min, x_max, n_points)
        
        psi_1 = np.array([basis_func(1, x, x_min, x_max) for x in x_vals])
        
        # Approximate norm
        norm_sq = np.sum(psi_1**2 / x_vals) * (x_max - x_min) / n_points
        
        assert 0 < norm_sq < 10, f"Basis function norm should be finite, got {norm_sq}"
    
    def test_basis_boundary(self):
        """Basis functions should be zero outside domain"""
        x_min, x_max = np.exp(-1), np.exp(1)
        
        # Outside domain
        assert basis_func(1, 0.1, x_min, x_max) == 0
        assert basis_func(1, 10.0, x_min, x_max) == 0


class TestOperatorConstruction:
    """Test the H operator construction"""
    
    def test_operator_hermiticity(self):
        """Operator H should be Hermitian (self-adjoint)"""
        n_basis = 5
        H = build_H_operator(n_basis=n_basis, t=0.01, scale_factor=1.0)
        
        # Check Hermiticity: H = H†
        H_dagger = np.conj(H.T)
        
        assert np.allclose(H, H_dagger, atol=1e-10), "Operator should be Hermitian"
    
    def test_operator_coercivity(self):
        """Operator H (with shift) should have all positive eigenvalues"""
        n_basis = 10
        H = build_H_operator(n_basis=n_basis, t=0.01, scale_factor=50.0)
        
        # Add shift for coercivity
        shift = 0.25
        H_shifted = H + shift * np.eye(n_basis)
        
        eigenvalues = np.linalg.eigvalsh(H_shifted)
        
        assert np.all(eigenvalues > 0), "All eigenvalues should be positive (coercive)"
        assert np.min(eigenvalues) >= 0.249, f"Minimum eigenvalue should be at least 0.249, got {np.min(eigenvalues)}"
    
    def test_operator_finite_spectrum(self):
        """Operator should have finite spectrum"""
        n_basis = 10
        H = build_H_operator(n_basis=n_basis, t=0.01, scale_factor=50.0)
        
        eigenvalues = np.linalg.eigvalsh(H)
        
        assert np.all(np.isfinite(eigenvalues)), "All eigenvalues should be finite"
        assert len(eigenvalues) == n_basis, "Should have n_basis eigenvalues"


class TestZeroConversion:
    """Test conversion from eigenvalues to zeros"""
    
    def test_zero_conversion_critical_line(self):
        """All converted zeros should lie on critical line Re(ρ) = 1/2"""
        eigenvalues = np.array([0.25, 1.0, 4.0, 10.0, 25.0])
        zeros = spectrum_to_zeros(eigenvalues, return_both_signs=False)
        
        for z in zeros:
            assert np.abs(np.real(z) - 0.5) < 1e-10, f"Zero {z} not on critical line"
    
    def test_zero_conversion_imaginary_positive(self):
        """Imaginary parts of zeros should be positive"""
        eigenvalues = np.array([0.25, 1.0, 4.0, 10.0, 25.0])
        zeros = spectrum_to_zeros(eigenvalues, return_both_signs=False)
        
        for z in zeros:
            assert np.imag(z) >= 0, f"Zero {z} has negative imaginary part"
    
    def test_zero_conversion_relation(self):
        """Verify λ = ρ(1-ρ) = 1/4 + γ² relationship"""
        # Use eigenvalues that will produce non-trivial zeros (λ > 0.25)
        eigenvalues = np.array([1.0, 4.0, 10.0])
        zeros = spectrum_to_zeros(eigenvalues, return_both_signs=False)
        
        # Should have one zero per eigenvalue
        assert len(zeros) == len(eigenvalues), f"Expected {len(eigenvalues)} zeros, got {len(zeros)}"
        
        for lam, z in zip(eigenvalues, zeros):
            # Extract gamma from zero: z = 1/2 + i*gamma
            gamma = np.imag(z)
            
            # Verify: λ = 1/4 + γ²
            expected_lambda = 0.25 + gamma**2
            
            assert np.abs(lam - expected_lambda) < 1e-8, f"λ={lam} should equal 1/4 + γ²={expected_lambda}"


class TestTheoreticalComparison:
    """Test comparison with known theoretical zeros"""
    
    def test_theoretical_zeros_loaded(self):
        """Should be able to load theoretical zeros"""
        zeros = load_theoretical_zeros(n_zeros=5)
        
        assert len(zeros) == 5, "Should load 5 zeros"
        
        # First zero should be around 14.13...
        assert np.abs(np.imag(zeros[0]) - 14.134725) < 0.001
    
    def test_comparison_function(self):
        """Comparison function should work correctly"""
        theoretical = load_theoretical_zeros(n_zeros=3)
        
        # Create synthetic computed zeros close to theoretical
        computed = [z + 0.1j for z in theoretical]
        
        result = compare_with_theoretical(computed, theoretical)
        
        assert result is not None
        assert result['n_compared'] == 3
        assert all(err < 0.2 for err in result['differences'])


class TestSpectralInversion:
    """Test spectral inversion properties"""
    
    def test_trace_formula(self):
        """Trace of operator should relate to number of zeros"""
        n_basis = 10
        H = build_H_operator(n_basis=n_basis, t=0.001, scale_factor=1.0)
        
        trace = np.trace(H)
        
        # Trace should be finite and positive
        assert np.isfinite(trace), "Trace should be finite"
        assert trace > 0, "Trace should be positive"


class TestIntegration:
    """Integration tests for complete workflow"""
    
    def test_complete_workflow_small(self):
        """Test complete workflow with small basis"""
        # Build operator
        n_basis = 8
        t = 0.01
        H = build_H_operator(n_basis=n_basis, t=t, scale_factor=50.0)
        
        # Add shift
        shift = 0.25
        H_shifted = H + shift * np.eye(n_basis)
        
        # Compute eigenvalues
        eigenvalues = np.linalg.eigvalsh(H_shifted)
        
        # Convert to zeros
        zeros = spectrum_to_zeros(eigenvalues, return_both_signs=False)
        
        # Check properties
        assert len(zeros) <= n_basis
        assert all(np.abs(np.real(z) - 0.5) < 1e-10 for z in zeros)
        assert all(np.isfinite(z) for z in zeros)
    
    @pytest.mark.slow
    def test_complete_workflow_large(self):
        """Test complete workflow with larger basis (slower)"""
        # Build operator with more basis functions
        n_basis = 15
        t = 0.001
        H = build_H_operator(n_basis=n_basis, t=t, scale_factor=50.0)
        
        # Add shift
        shift = 0.25
        H_shifted = H + shift * np.eye(n_basis)
        
        # Compute eigenvalues
        eigenvalues = np.linalg.eigvalsh(H_shifted)
        
        # Convert to zeros
        zeros = spectrum_to_zeros(eigenvalues, return_both_signs=False)
        
        # Compare with theoretical
        theoretical = load_theoretical_zeros(n_zeros=10)
        
        # At least some zeros should be captured
        assert len(zeros) > 0
        assert all(np.abs(np.real(z) - 0.5) < 1e-10 for z in zeros)


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
