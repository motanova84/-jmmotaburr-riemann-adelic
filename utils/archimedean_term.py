"""
Archimedean term computation for Riemann Hypothesis validation.
Implements A_inf using the Mellin transform approach (legacy method).
"""

import mpmath as mp
from utils.mellin import mellin_transform


def archimedean_term_notebook(phi, sigma0=2.0, T=20, lim_u=3.0):
    """
    Compute Archimedean term using the notebook's working method.
    
    A_infty = (1/(2π)) * ∫ (ψ(s/2) - log(π)) * f̂(s) dt - f̂(1)
    
    Args:
        phi: Test function
        sigma0: Real part of integration contour  
        T: Integration limit
        lim_u: Integration limit for f̂
    
    Returns:
        Archimedean term value
    """
    print(f"  Computing Archimedean integral (notebook method) with T={T}, lim_u={lim_u}")
    
    def fhat(s, lim):
        """Compute f̂(s) = ∫ f(u) * exp(s * u) du"""
        return mp.quad(lambda u: phi(u) * mp.exp(s * u), [-lim, lim], maxdegree=10)
    
    def integrand(t):
        s = mp.mpc(sigma0, t)  # Use complex number as in notebook
        return (mp.digamma(s/2) - mp.log(mp.pi)) * fhat(s, lim_u)
    
    # Use reduced precision for faster computation of the integral
    old_dps = mp.mp.dps
    mp.mp.dps = 15
    try:
        integ = mp.quad(integrand, [-T, T], maxdegree=10) / (2 * mp.pi)
        res1 = fhat(mp.mpf(1), lim_u) / mp.mpf(1)  # The correction term
        result = integ - res1
    finally:
        mp.mp.dps = old_dps
    
    print(f"  Integral part: {integ}")
    print(f"  Correction term: {res1}")
    print(f"  Archimedean term: {result}")
    return result


def archimedean_term_mellin(phi, sigma0=2.0, T=20, lim_u=3.0):
    """
    Compute Archimedean term using the correct notebook method.
    This replaces the old mellin transform approach.
    """
    return archimedean_term_notebook(phi, sigma0, T, lim_u)


def archimedean_sum_legacy(f, sigma0, T, lim_u):
    """
    Legacy archimedean sum function using the old method.
    This uses the Mellin transform approach from the original code.
    """
    return archimedean_term_mellin(f, sigma0, T, lim_u)