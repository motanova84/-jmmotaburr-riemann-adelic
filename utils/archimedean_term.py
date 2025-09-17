"""
Archimedean term computation for Riemann Hypothesis validation.
Implements A_inf using the Mellin transform approach (legacy method).
"""

import mpmath as mp
from utils.mellin import mellin_transform


def archimedean_term_mellin(phi, sigma0=2.0, T=20, lim_u=3.0):
    """
    Compute Archimedean term using Mellin transform approach.
    This is the method currently used in the codebase.
    
    Args:
        phi: Test function
        sigma0: Real part of integration contour
        T: Integration limit (reduced for faster computation)
        lim_u: Mellin transform integration limit (reduced for faster computation)
    
    Returns:
        Archimedean term value
    """
    print(f"  Computing Archimedean integral with T={T}, lim_u={lim_u}")
    
    def integrand(t):
        s = sigma0 + 1j * t
        kernel = mp.digamma(s / 2) - mp.log(mp.pi)
        return kernel * mellin_transform(phi, s, lim_u)
    
    # Use reduced precision for faster computation of the integral
    old_dps = mp.mp.dps
    mp.mp.dps = 15
    try:
        integral, err = mp.quad(integrand, [-T, T], error=True, maxdegree=6)
        result = (integral / (2j * mp.pi)).real
    finally:
        mp.mp.dps = old_dps
    
    print(f"  Archimedean term: {result}")
    return result


def archimedean_sum_legacy(f, sigma0, T, lim_u):
    """
    Legacy archimedean sum function using the old method.
    This uses the Mellin transform approach from the original code.
    """
    return archimedean_term_mellin(f, sigma0, T, lim_u)