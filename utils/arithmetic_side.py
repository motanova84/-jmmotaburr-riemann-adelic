"""
Arithmetic side computation for Riemann Hypothesis validation.
Implements the von Mangoldt function sum over all integers n ≥ 2.
"""

import mpmath as mp
import sympy as sp


def von_mangoldt(n):
    """
    von Mangoldt function Λ(n).
    Returns log(p) if n = p^k for prime p, 0 otherwise.
    """
    if n < 2:
        return mp.mpf('0')
    
    # Factor n to find if it's a prime power
    factors = sp.factorint(n)
    
    # If n has exactly one prime factor, it's a prime power
    if len(factors) == 1:
        p, k = list(factors.items())[0]
        return mp.log(p)
    else:
        return mp.mpf('0')


def arithmetic_side(phi, X=10.0):
    """
    Compute the arithmetic side of the explicit formula.
    
    Sum: -∑_{n=2}^{n_max} Λ(n)/√n * (φ(log(n)) + φ(-log(n)))
    where n_max = exp(X)
    
    Args:
        phi: Test function φ(u)
        X: Upper limit parameter, n_max = exp(X)
    
    Returns:
        Arithmetic side sum
    """
    n_max = int(mp.exp(X))
    total = mp.mpf('0')
    
    print(f"Computing arithmetic side with n_max = {n_max}")
    
    for n in range(2, n_max + 1):
        if n % 1000 == 0:
            print(f"  Progress: n = {n}/{n_max}")
            
        lambda_n = von_mangoldt(n)
        if lambda_n > 0:  # Only compute if von Mangoldt is non-zero
            sqrt_n = mp.sqrt(n)
            log_n = mp.log(n)
            
            phi_pos = phi(log_n)
            phi_neg = phi(-log_n)
            
            term = lambda_n / sqrt_n * (phi_pos + phi_neg)
            total += term
    
    return total  # Try without negative sign first


def prime_sum_legacy(f, P, K):
    """
    Legacy prime sum function for backward compatibility.
    This is the old incorrect implementation - kept for comparison.
    """
    total = mp.mpf('0')
    # Generate all primes up to P
    primes = list(sp.primerange(2, P + 1))
    for p in primes:
        lp = mp.log(p)
        for k in range(1, K + 1):
            total += lp * f(k * lp)
    return total