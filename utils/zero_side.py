"""
Zero side computation for Riemann Hypothesis validation.
Handles the sum over non-trivial zeros of the Riemann zeta function.
"""

import mpmath as mp
from utils.mellin import mellin_transform


def zero_side_notebook(phi, N=1000, lim_u=3.0):
    """
    Compute the zero side using the notebook's working method.
    Uses mpmath.zetazero to get zeros directly.
    
    Args:
        phi: Test function φ(u)
        N: Number of zeros to use
        lim_u: Integration limit for f̂
    
    Returns:
        Zero side sum
    """
    print(f"Computing zero side with {N} zeros using mpmath.zetazero")
    
    def fhat(s, lim):
        """Compute f̂(s) = ∫ f(u) * exp(s * u) du"""
        return mp.quad(lambda u: phi(u) * mp.exp(s * u), [-lim, lim], maxdegree=10)
    
    total = mp.mpf('0')
    
    for n in range(1, N + 1):
        if n % 100 == 0:
            print(f"  Progress: zero {n}/{N}")
            
        rho = mp.zetazero(n)  # Get the n-th zero
        gamma = mp.im(rho)    # Get the imaginary part
        
        fhat_val = fhat(1j * gamma, lim_u)
        total += fhat_val.real
    
    print(f"Used {N} zeros for computation")
    return total


def zero_sum_from_file(phi, filename, max_zeros=None, lim_u=5.0):
    """
    Compute zero sum reading zeros from file.
    
    Args:
        phi: Test function
        filename: File containing zeros (one per line)
        max_zeros: Maximum number of zeros to use (None for all)
        lim_u: Integration limit for Mellin transform
    
    Returns:
        Zero side sum
    """
    total = mp.mpf('0')
    count = 0
    
    with open(filename) as file:
        for line in file:
            if max_zeros is not None and count >= max_zeros:
                break
                
            gamma = mp.mpf(line.strip())
            phi_hat = mellin_transform(phi, 1j * gamma, lim_u)
            total += phi_hat.real
            count += 1
    
    print(f"Used {count} zeros for computation")
    return total


def zero_sum_limited(f, filename, max_zeros, lim_u=5):
    """
    Legacy function for backward compatibility.
    Compute zero sum using only first max_zeros from file.
    """
    return zero_sum_from_file(f, filename, max_zeros, lim_u)