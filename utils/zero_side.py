"""
Zero side computation for Riemann Hypothesis validation.
Handles the sum over non-trivial zeros of the Riemann zeta function.
"""

import mpmath as mp
from utils.mellin import mellin_transform


def zero_side(phi, zeros, multiply_by_two=False):
    """
    Compute the zero side of the explicit formula.
    
    Sum over zeros: ∑_γ φ̂(γ) where φ̂ is the Fourier/Mellin transform of φ
    
    Args:
        phi: Test function φ(u)
        zeros: List of zero imaginary parts γ
        multiply_by_two: If True, multiply result by 2 (for positive zeros only)
    
    Returns:
        Zero side sum
    """
    total = mp.mpf('0')
    
    for gamma in zeros:
        # Compute φ̂(γ) using Mellin transform
        phi_hat = mellin_transform(phi, 1j * gamma, lim=5.0)
        total += phi_hat.real
    
    if multiply_by_two:
        total *= 2
        
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