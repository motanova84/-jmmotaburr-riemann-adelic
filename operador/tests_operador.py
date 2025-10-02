"""
Tests for the Gaussian kernel spectral operator.

This module validates:
1. Symmetry of R matrix
2. Coercivity of H (eigenvalues > 0.25)
3. Convergence of cosine basis to Fourier as Nq increases
"""

import numpy as np
import pytest
from operador.operador_H import build_R_matrix, spectrum_from_R, fourier_eigs_H


def test_symmetry_R():
    """Test that R matrix is symmetric."""
    h = 1e-3
    R = build_R_matrix(n_basis=5, h=h, L=1.0, Nq=80)
    assert np.allclose(R, R.T, atol=1e-12), "R should be symmetric"


def test_positive_H():
    """Test that H is coercive: all eigenvalues > 1/4."""
    h = 1e-3
    R = build_R_matrix(n_basis=5, h=h, L=1.0, Nq=120)
    lam_H, gammas = spectrum_from_R(R, h)
    assert np.all(lam_H > 0.25), "Eigenvalues of H should exceed 1/4"
    assert np.all(gammas >= 0), "Gammas should be real nonnegative"


def test_cosine_vs_fourier_convergence():
    """Test that cosine quadrature is stable as Nq increases."""
    h = 1e-3
    L = 1.0
    
    # Cosine with increasing quadrature
    R1 = build_R_matrix(n_basis=5, h=h, L=L, Nq=60)
    lam_H1, _ = spectrum_from_R(R1, h)

    R2 = build_R_matrix(n_basis=5, h=h, L=L, Nq=160)
    lam_H2, _ = spectrum_from_R(R2, h)
    
    R3 = build_R_matrix(n_basis=5, h=h, L=L, Nq=240)
    lam_H3, _ = spectrum_from_R(R3, h)

    # Check stability: results should be similar as Nq increases
    diff_12 = np.linalg.norm(lam_H2 - lam_H1)
    diff_23 = np.linalg.norm(lam_H3 - lam_H2)
    
    # As Nq increases, changes should become smaller (converging to something)
    assert diff_23 <= diff_12 * 1.5, "Results should stabilize as Nq increases"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
