"""
Operador H - Gaussian Kernel Spectral Operator

This module implements the heat operator R_h and Hamiltonian H using
the closed-form Gaussian kernel instead of oscillatory integration.
"""

from .operador_H import (
    K_gauss,
    cos_basis,
    build_R_matrix,
    spectrum_from_R,
    fourier_eigs_H,
    hermite_basis,
    K_gauss_rigorous,
    rigorous_H_construction,
    validate_convergence_bounds
)

__all__ = [
    'K_gauss',
    'cos_basis',
    'build_R_matrix',
    'spectrum_from_R',
    'fourier_eigs_H',
    'hermite_basis',
    'K_gauss_rigorous',
    'rigorous_H_construction',
    'validate_convergence_bounds'
]
