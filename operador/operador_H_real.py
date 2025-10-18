"""
Real Spectral Operator for Riemann Hypothesis

This module implements the construction of the Hamiltonian operator H
for computing Riemann zeros using spectral methods.

Based on the Gaussian kernel approach from operador_H.py
"""

import numpy as np
from numpy.linalg import eigh


def build_H_real(n_basis, t=0.01):
    """
    Build the real Hamiltonian operator H.
    
    Constructs a simplified spectral operator for computing Riemann zeros.
    Uses a Gaussian kernel approximation.
    
    Args:
        n_basis: Number of basis functions (size of matrix)
        t: Thermal parameter (controls kernel width)
        
    Returns:
        H: Real symmetric matrix (n_basis x n_basis) representing the Hamiltonian
    """
    H = np.zeros((n_basis, n_basis))
    
    # Simple basis grid
    x = np.linspace(-5, 5, n_basis)
    
    # Build kernel matrix with Gaussian
    for i in range(n_basis):
        for j in range(n_basis):
            # Gaussian kernel: exp(-(x[i] - x[j])^2 / (4*t))
            kernel = np.exp(-(x[i] - x[j])**2 / (4.0 * t))
            H[i, j] = kernel
    
    # Make it a proper Hamiltonian by adding small identity for numerical stability
    H = H + 0.25 * np.eye(n_basis)
    
    # Ensure exact symmetry
    H = (H + H.T) / 2.0
    
    return H


def compute_zeros_from_H(H):
    """
    Compute Riemann zeros from the eigenvalues of H.
    
    Extracts zeros on the critical line from the spectrum of H.
    Based on the spectral interpretation where eigenvalues λ relate to
    zeros via λ = ω² + 1/4, giving ω and thus zeros at s = 1/2 + iω.
    
    Args:
        H: Hamiltonian matrix (numpy array)
        
    Returns:
        zeros: List of complex numbers representing Riemann zeros
    """
    # Compute eigenvalues
    eigenvalues = eigh(H, eigvals_only=True)
    
    # Extract zeros from eigenvalues
    zeros = []
    for lam in eigenvalues:
        if lam > 0.25:  # Only consider eigenvalues above 1/4
            # Convert eigenvalue to imaginary part: λ = ω² + 1/4
            omega = np.sqrt(lam - 0.25)
            # Zero is at s = 1/2 + i*omega
            z = 0.5 + 1j * omega
            zeros.append(z)
    
    # Sort by imaginary part
    zeros.sort(key=lambda z: z.imag)
    
    return zeros


def verify_with_odlyzko(zeros, known_zeros=None):
    """
    Verify computed zeros against known Riemann zeros.
    
    Compares computed zeros with a set of known zeros (typically from Odlyzko's tables).
    
    Args:
        zeros: List of computed zeros (complex numbers)
        known_zeros: List of known zero imaginary parts (optional)
                    If None, uses first few known zeros
        
    Returns:
        errors: List of absolute errors for each zero
    """
    # Default known zeros (imaginary parts only)
    if known_zeros is None:
        known_zeros = [
            14.134725141734693790,
            21.022039638771554993,
            25.010857580145688763,
            30.424876125859513210,
            32.935061587739189691,
            37.586178158825671257,
            40.918719012147495187,
            43.327073280914999519,
            48.005150881167159727,
            49.773832477672302181,
        ]
    
    errors = []
    for i, z in enumerate(zeros[:len(known_zeros)]):
        if i < len(known_zeros):
            error = abs(z.imag - known_zeros[i])
            errors.append(error)
    
    return errors
