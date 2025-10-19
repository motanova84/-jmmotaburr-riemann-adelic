"""
Operador H - Gaussian Kernel Spectral Operator

This module implements the heat operator R_h and Hamiltonian H using
the closed-form Gaussian kernel instead of oscillatory integration.
"""

from .operador_H import K_gauss, build_R_matrix, cos_basis, fourier_eigs_H, kernel_adelic_ultimus, spectrum_from_R

__all__ = ["K_gauss", "kernel_adelic_ultimus", "cos_basis", "build_R_matrix", "spectrum_from_R", "fourier_eigs_H"]
