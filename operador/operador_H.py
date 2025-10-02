"""
Gaussian Kernel Spectral Operator for Riemann Hypothesis

This module implements the construction with the closed-form Gaussian kernel:
- No oscillatory integration (quad/nquad)
- Direct analytical formula for K_h(t,s)
- Symmetric and positive definite R_h operator
- Coercive Hamiltonian H

Mathematical Foundation:
    K_h(t,s) = exp(-h/4) * sqrt(π/h) * exp(-(t-s)²/(4h))

Where t = log(x), s = log(y) are log-variables.

The heat operator R_h is constructed via double Gauss-Legendre quadrature,
then H = -(1/h) log(R_h / 2π) gives the Hamiltonian with spectrum ω² + 1/4.
"""

import numpy as np
from numpy.polynomial.legendre import leggauss
from numpy.linalg import eigh
import mpmath as mp
from sympy import prime


def K_gauss(t, s, h):
    """
    Analytical Gaussian kernel in log-variables.
    
    Formula:
        K_h(t,s) = exp(-h/4) * sqrt(π/h) * exp(-(t-s)²/(4h))
    
    This is the closed form of the integral:
        ∫ exp(-h(u² + 1/4)) exp(iu(t-s)) du
    
    Args:
        t: log-variable (can be array)
        s: log-variable (can be array)
        h: thermal parameter
    
    Returns:
        Kernel value K_h(t,s)
    """
    return np.exp(-h/4.0) * np.sqrt(np.pi / h) * np.exp(- (t - s)**2 / (4.0*h))


def kernel_adelic_ultimus(t, s, h=1e-3, N=10):
    """
    Adelic thermal kernel with prime corrections.
    
    This function implements the full adelic kernel including:
    - Base Gaussian kernel from heat operator
    - Prime-power corrections from non-archimedean places
    - Infinite tail approximation with validation
    
    Formula:
        K(t,s) = K_gauss(t,s) + Σ_p Σ_k [correction terms]
        
    Where the correction terms include:
    - log(p) * exp(-h*(k*log(p))²/4) / p^(k/2)
    - cos(k*log(p)*(t-s)) modulation
    
    Args:
        t: log-variable (mpmath number)
        s: log-variable (mpmath number)
        h: thermal parameter (default 1e-3)
        N: controls prime cutoff via P = exp(sqrt(N))
            NOTE: For the tail assertion to pass, N must be large enough
            that max_k provides sufficient decay. For small primes like p=2,
            this may require N > 1000. However, very large N can cause
            overflow in primepi(). Typical working range: 50 < N < 500.
    
    Returns:
        Kernel value K(t,s) with adelic corrections (mpmath number)
        
    Raises:
        AssertionError: If the infinite tail estimate exceeds 1e-10,
                       indicating insufficient convergence for the given parameters.
    """
    # Convert inputs to mpmath
    t = mp.mpf(t)
    s = mp.mpf(s)
    h = mp.mpf(h)
    N = mp.mpf(N)
    
    # Base Gaussian kernel
    kernel = mp.exp(-h/4)/mp.sqrt(4*mp.pi*h) * mp.exp(-(t-s)**2/(4*h))
    
    # Prime cutoff
    P = mp.exp(mp.sqrt(N))
    num_primes = int(mp.primepi(P)) + 1
    primes = [prime(i) for i in range(1, num_primes)]
    log_primes = [mp.log(p) for p in primes]
    
    # Add prime corrections
    for p, log_p in zip(primes, log_primes):
        sum_k = mp.mpf(0)
        max_k = int(mp.log(P)/log_p) + 1
        
        # Finite sum over k
        for k in range(1, max_k):
            term = log_p * mp.exp(-h*(k*log_p)**2/4) / (p**(k/2))
            kernel += term * mp.cos(k*log_p*(t-s))
        
        # Infinite tail approximation
        tail = log_p * mp.quad(lambda k: mp.exp(-h*(k*log_p)**2/4) / (p**(k/2)), [max_k, mp.inf])
        kernel += tail * mp.cos(max_k*log_p*(t-s))  # Approx
        
        # Validate tail is sufficiently small
        assert tail < 1e-10, f"Tail too large: {tail} for prime {p}"
    
    return kernel


def cos_basis(t, L, k):
    """
    Orthonormal cosine basis on [-L, L] for L²(dt).
    
    φ_0(t) = 1/√(2L)
    φ_k(t) = cos(kπt/L) / √L  for k ≥ 1
    
    Args:
        t: evaluation points (array)
        L: half-width of interval
        k: mode number (k=0 for constant, k≥1 for cosines)
    
    Returns:
        Basis function values at t
    """
    if k == 0:
        return np.ones_like(t) / np.sqrt(2.0*L)
    return np.cos(k * np.pi * t / L) / np.sqrt(L)


def build_R_matrix(n_basis=5, h=1e-3, L=1.0, Nq=160):
    """
    Build the heat operator R_h matrix in the cosine basis.
    
    Uses double Gauss-Legendre quadrature to compute:
        R_ij = ∫∫ φ_i(t) K_h(t,s) φ_j(s) dt ds
    
    The result is a symmetric positive definite matrix.
    
    Args:
        n_basis: number of basis functions (matrix dimension)
        h: thermal parameter (typically 1e-3)
        L: half-width of interval [-L, L] in log-space
        Nq: number of quadrature points (higher = more accurate)
    
    Returns:
        R: n_basis × n_basis symmetric positive definite matrix
    """
    # Get Gauss-Legendre nodes and weights on [-1, 1]
    x, w = leggauss(Nq)
    
    # Scale to [-L, L]
    t = L * x
    w = L * w
    
    # Build kernel matrix K[a, b] = K_h(t_a, t_b)
    K = np.empty((Nq, Nq))
    for a in range(Nq):
        K[a, :] = K_gauss(t[a], t, h)
    
    # Build basis projection matrix Phi[k, a] = φ_k(t_a)
    Phi = np.vstack([cos_basis(t, L, k) for k in range(n_basis)])
    
    # Compute R_ij = Phi @ (W @ K @ W) @ Phi.T
    # where W = diag(w) is the diagonal weight matrix
    W = np.diag(w)
    M = W @ K @ W
    R = Phi @ M @ Phi.T
    
    # Symmetrize to correct for numerical roundoff
    R = 0.5 * (R + R.T)
    
    return R


def spectrum_from_R(R, h):
    """
    Extract spectrum of H from heat operator R.
    
    Uses the mapping:
        H = -(1/h) log(R / 2π)
    
    Diagonalizes R and applies the logarithmic map to eigenvalues.
    
    Args:
        R: heat operator matrix (symmetric, positive definite)
        h: thermal parameter
    
    Returns:
        lam_H: eigenvalues of H (sorted ascending)
        gammas: estimated γ values from eigenvalues via γ = √(λ - 1/4)
    """
    # Diagonalize R (symmetric real matrix)
    vals, _ = eigh(R)
    
    # Clip to avoid log(0)
    vals = np.clip(vals, 1e-300, None)
    
    # Map to H spectrum: λ_H = -(1/h) log(λ_R / 2π)
    lam_H = -(1.0/h) * np.log(vals / (2.0*np.pi))
    
    # Sort ascending
    lam_H = np.sort(lam_H)
    
    # Extract gammas: γ = √(λ - 1/4), clipped to non-negative
    gammas = np.sqrt(np.clip(lam_H - 0.25, 0.0, None))
    
    return lam_H, gammas


def fourier_eigs_H(n_modes=5, h=1e-3, L=1.0):
    """
    Exact eigenvalues of H in Fourier basis (diagonal).
    
    In the periodic Fourier basis φ_k(t) = exp(iω_k t) / √(2L),
    with ω_k = πk/L, the heat operator is diagonal:
    
        λ_R(ω_k) = 2π exp(-h(ω_k² + 1/4))
    
    Then:
        λ_H(ω_k) = ω_k² + 1/4
    
    This provides the exact spectrum for validation.
    
    Args:
        n_modes: number of Fourier modes (k = 0, 1, 2, ...)
        h: thermal parameter
        L: half-width of interval
    
    Returns:
        eig_H: exact eigenvalues of H
        gammas: exact γ values
    """
    k = np.arange(n_modes, dtype=float)
    omega = (np.pi / L) * k
    
    # Exact formula for R eigenvalues
    eig_R = 2.0*np.pi * np.exp(-h*(omega**2 + 0.25))
    
    # Map to H: λ_H = ω² + 1/4 (exact)
    eig_H = -(1.0/h) * np.log(eig_R / (2.0*np.pi))
    
    # Extract gammas
    gammas = np.sqrt(np.maximum(eig_H - 0.25, 0.0))
    
    return eig_H, gammas


if __name__ == "__main__":
    # Demonstration run
    h = 1e-3
    L = 1.0
    
    print("=" * 70)
    print("GAUSSIAN KERNEL OPERATOR DEMONSTRATION")
    print("=" * 70)
    print(f"Parameters: h={h}, L={L}")
    print()
    
    # Build R matrix via cosine basis quadrature
    print("Building R_h matrix via cosine basis...")
    R = build_R_matrix(n_basis=5, h=h, L=L, Nq=160)
    print(f"  R shape: {R.shape}")
    print(f"  R symmetric: {np.allclose(R, R.T)}")
    print(f"  R eigenvalues: {np.linalg.eigvalsh(R)}")
    print()
    
    # Extract H spectrum
    print("Extracting H spectrum from R...")
    lam_H, gammas = spectrum_from_R(R, h)
    print(f"  Eigenvalues of H: {lam_H}")
    print(f"  Estimated gammas: {gammas}")
    print()
    
    # Compare with exact Fourier
    print("Computing exact Fourier spectrum...")
    lam_H_F, gammas_F = fourier_eigs_H(n_modes=5, h=h, L=L)
    print(f"  Eigenvalues of H (Fourier): {lam_H_F}")
    print(f"  Exact gammas (Fourier): {gammas_F}")
    print()
    
    # Compute difference
    diff = lam_H - lam_H_F
    print("Difference (cosine - Fourier):")
    print(f"  {diff}")
    print(f"  Norm: {np.linalg.norm(diff):.3e}")
    print()
    print("=" * 70)
    print("✓ Demonstration complete!")
