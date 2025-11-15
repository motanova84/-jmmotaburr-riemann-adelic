#!/usr/bin/env python3
"""
Adelic D(s) Function Implementation

This module implements the canonical determinant D(s) as defined in the V5 Coronación proof:
    D(s) = det_{S¹}(I + B_δ(s))
where:
    B_δ(s) = R_δ(s; A_δ) - R_δ(s; A_0)

The function D(s) is constructed from S-finite adelic flows without using ζ(s) or its Euler product.
This is the explicit mathematical formalization of the D(s) mentioned in the problem statement.

References:
- Tate (1967): Fourier Analysis in Number Fields and Hecke's Zeta-Functions
- Weil (1964): Sur certains groupes d'opérateurs unitaires
- Birman–Solomyak (2003): Double Operator Integrals in a Hilbert Space
- de Branges (1986): Hilbert Spaces of Entire Functions
"""

import numpy as np
import mpmath as mp
from scipy.linalg import det, inv
from validate_explicit_formula import simulate_delta_s, zeta_p_interpolation


class AdelicDFunction:
    """
    Implementation of the canonical determinant D(s) from S-finite adelic spectral systems.
    
    The function is defined as:
    D(s) = det_{S¹}(I + B_δ(s))
    
    where B_δ(s) is the smoothed resolvent difference operator.
    """
    
    def __init__(self, precision=30, max_zeros=100, places=None):
        """
        Initialize the Adelic D(s) function.
        
        Args:
            precision: mpmath precision in decimal places
            max_zeros: maximum number of zeros for matrix dimension
            places: list of finite places (primes) for S-finite corrections
        """
        mp.mp.dps = precision
        self.precision = precision
        self.max_zeros = max_zeros
        self.places = places if places is not None else [2, 3, 5, 7]
        
        # Precompute base matrices
        self._initialize_base_operators()
        
    def _initialize_base_operators(self):
        """Initialize base operators A_0, A_δ from Delta_S simulation."""
        # Get the Delta_S matrix which serves as our base operator
        eigenvalues, imag_parts, eigenvectors = simulate_delta_s(
            self.max_zeros, self.precision, self.places
        )
        
        # Store base operator data
        self.base_eigenvalues = eigenvalues
        self.base_eigenvectors = eigenvectors
        
        # A_0 is the unperturbed operator (identity-like)
        self.A_0 = np.eye(self.max_zeros, dtype=np.complex128)
        
        # A_δ is the Delta_S matrix
        self.A_delta = np.diag(eigenvalues.astype(np.complex128))
        
    def resolvent(self, s, operator_matrix, delta=1e-3):
        """
        Compute regularized resolvent R_δ(s; A) = (s*I - A + iδ)^{-1}.
        
        Args:
            s: complex parameter
            operator_matrix: operator matrix A
            delta: regularization parameter
            
        Returns:
            Regularized resolvent matrix
        """
        s_complex = complex(s)
        N = operator_matrix.shape[0]
        
        # Compute (s*I - A + iδ)
        resolvent_matrix = s_complex * np.eye(N, dtype=np.complex128) - operator_matrix
        resolvent_matrix += 1j * delta * np.eye(N, dtype=np.complex128)
        
        # Add small regularization to avoid singularities
        regularization = 1e-10 * np.eye(N, dtype=np.complex128)
        resolvent_matrix += regularization
        
        try:
            # Compute inverse
            return inv(resolvent_matrix)
        except np.linalg.LinAlgError:
            # Fallback: use pseudo-inverse
            return np.linalg.pinv(resolvent_matrix)
    
    def B_delta_operator(self, s, delta=1e-3):
        """
        Compute the smoothed difference operator B_δ(s) = R_δ(s; A_δ) - R_δ(s; A_0).
        
        Args:
            s: complex parameter
            delta: regularization parameter
            
        Returns:
            B_δ(s) operator matrix
        """
        R_delta = self.resolvent(s, self.A_delta, delta)
        R_0 = self.resolvent(s, self.A_0, delta) 
        
        return R_delta - R_0
    
    def D(self, s, delta=1e-3, method='trace_class'):
        """
        Compute the canonical determinant D(s) = det_{S¹}(I + B_δ(s)).
        
        Args:
            s: complex parameter
            delta: regularization parameter  
            method: computation method ('trace_class' or 'direct')
            
        Returns:
            Complex value of D(s)
        """
        # Get the B_δ(s) operator
        B_delta = self.B_delta_operator(s, delta)
        
        # Compute I + B_δ(s)
        N = B_delta.shape[0]
        operator_matrix = np.eye(N, dtype=np.complex128) + B_delta
        
        if method == 'trace_class':
            # Use trace-class regularized determinant
            return self._trace_class_determinant(operator_matrix)
        elif method == 'direct':
            # Direct determinant computation
            try:
                det_val = det(operator_matrix)
                return complex(det_val)
            except np.linalg.LinAlgError:
                # Fallback to regularized computation
                return self._trace_class_determinant(operator_matrix)
        else:
            raise ValueError(f"Unknown method: {method}")
    
    def _trace_class_determinant(self, operator_matrix):
        """
        Compute trace-class regularized determinant using Birman-Solomyak theory.
        
        This implements the S¹ (trace-class) determinant needed for D(s).
        
        Args:
            operator_matrix: matrix for which to compute det_{S¹}
            
        Returns:
            Regularized determinant value
        """
        N = operator_matrix.shape[0]
        
        try:
            # Compute eigenvalues for trace-class determinant
            eigenvals = np.linalg.eigvals(operator_matrix)
            
            # Remove eigenvalues too close to zero (regularization)
            eigenvals = eigenvals[np.abs(eigenvals) > 1e-12]
            
            # Trace-class determinant = product of eigenvalues
            if len(eigenvals) == 0:
                return complex(1.0)
                
            # Use log-sum to avoid overflow
            log_det = np.sum(np.log(eigenvals))
            return complex(np.exp(log_det))
            
        except (np.linalg.LinAlgError, OverflowError):
            # Fallback: use regularized direct computation
            regularized_matrix = operator_matrix + 1e-10 * np.eye(N, dtype=np.complex128)
            return complex(det(regularized_matrix))
    
    def verify_functional_equation(self, s_values):
        """
        Verify the functional equation D(1-s) = D(s) for given s values.
        
        Args:
            s_values: list of complex values to test
            
        Returns:
            dict with verification results
        """
        results = {
            'tested_points': [],
            'errors': [],
            'max_error': 0.0,
            'mean_error': 0.0
        }
        
        for s in s_values:
            s_complex = complex(s)
            
            # Compute D(s) and D(1-s)
            D_s = self.D(s_complex)
            D_1_minus_s = self.D(1 - s_complex)
            
            # Compute relative error
            if abs(D_s) > 1e-12:
                error = abs(D_s - D_1_minus_s) / abs(D_s)
            else:
                error = abs(D_s - D_1_minus_s)
            
            results['tested_points'].append(s_complex)
            results['errors'].append(float(error))
        
        if results['errors']:
            results['max_error'] = max(results['errors'])
            results['mean_error'] = sum(results['errors']) / len(results['errors'])
        
        return results
    
    def evaluate_at_zeros(self, zero_imaginary_parts, tolerance=1e-8):
        """
        Evaluate D(1/2 + it) at known Riemann zeros to verify vanishing.
        
        Args:
            zero_imaginary_parts: list of imaginary parts of known zeros
            tolerance: tolerance for considering a value as zero
            
        Returns:
            dict with evaluation results
        """
        results = {
            'zero_values': [],
            'magnitudes': [],
            'zeros_confirmed': 0,
            'total_tested': 0
        }
        
        for t in zero_imaginary_parts[:min(10, len(zero_imaginary_parts))]:  # Test first 10
            s = complex(0.5, float(t))
            D_val = self.D(s)
            magnitude = abs(D_val)
            
            results['zero_values'].append(D_val)
            results['magnitudes'].append(magnitude)
            results['total_tested'] += 1
            
            if magnitude < tolerance:
                results['zeros_confirmed'] += 1
        
        return results


def demo_d_function():
    """Demonstration of the D(s) function capabilities."""
    print("🔬 Adelic D(s) Function Demonstration")
    print("=" * 50)
    
    # Initialize D(s) function
    d_func = AdelicDFunction(precision=20, max_zeros=50, places=[2, 3, 5])
    
    # Test points
    test_points = [0.5, 1.0, 0.5 + 1j, 1.5, 2.0]
    
    print("\n📊 D(s) Evaluations:")
    for s in test_points:
        D_val = d_func.D(s)
        print(f"D({s}) = {D_val:.6f}")
    
    # Verify functional equation
    print("\n⚖️  Functional Equation Verification D(1-s) = D(s):")
    verification = d_func.verify_functional_equation(test_points)
    print(f"Max relative error: {verification['max_error']:.2e}")
    print(f"Mean relative error: {verification['mean_error']:.2e}")
    
    # Test at known zeros (simplified)
    print("\n🎯 Testing at Simulated Critical Line Points:")
    test_zeros = [14.134725142, 21.022039639, 25.010857580]
    zero_results = d_func.evaluate_at_zeros(test_zeros)
    print(f"Zeros confirmed (|D(s)| < 1e-8): {zero_results['zeros_confirmed']}/{zero_results['total_tested']}")
    
    if zero_results['magnitudes']:
        avg_magnitude = sum(zero_results['magnitudes']) / len(zero_results['magnitudes'])
        print(f"Average magnitude at test points: {avg_magnitude:.2e}")
    
    print("\n✅ D(s) function demonstration completed!")


if __name__ == "__main__":
    demo_d_function()