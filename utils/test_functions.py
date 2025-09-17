"""
Test functions for Riemann Hypothesis validation.
Implements well-defined Gaussian functions and their Fourier transforms.
"""

import mpmath as mp
import math


def phi_gaussian(u, alpha=1.0):
    """
    Gaussian test function φ(u) = exp(-(u/α)²).
    
    Args:
        u: Function argument
        alpha: Scale parameter
    
    Returns:
        φ(u) value
    """
    return mp.exp(-(u / alpha) ** 2)


def phi_hat_gaussian(t, alpha=1.0):
    """
    Fourier transform of Gaussian test function.
    φ̂(t) = α√π * exp(-(παt)²)
    
    Args:
        t: Frequency argument
        alpha: Scale parameter
    
    Returns:
        φ̂(t) value
    """
    return alpha * mp.sqrt(mp.pi) * mp.exp(-(mp.pi * alpha * t) ** 2)


def truncated_gaussian_improved(u, a=5.0, sigma=1.0):
    """
    Improved truncated Gaussian with better properties.
    
    Args:
        u: Function argument
        a: Truncation parameter
        sigma: Standard deviation
    
    Returns:
        Truncated Gaussian value
    """
    if abs(u) > a:
        return mp.mpf('0')
    return mp.exp(-u**2 / (2 * sigma**2))


# For backward compatibility
truncated_gaussian = truncated_gaussian_improved


def test_function_properties():
    """
    Test properties of the test functions.
    Returns diagnostic information.
    """
    alpha = 1.0
    
    # Test normalization and basic properties
    phi_0 = phi_gaussian(0, alpha)
    phi_hat_0 = phi_hat_gaussian(0, alpha)
    
    # Test symmetry
    u_test = 1.0
    phi_pos = phi_gaussian(u_test, alpha)
    phi_neg = phi_gaussian(-u_test, alpha)
    
    return {
        'phi(0)': phi_0,
        'phi_hat(0)': phi_hat_0,
        'phi(1)': phi_pos,
        'phi(-1)': phi_neg,
        'symmetric': abs(phi_pos - phi_neg) < 1e-15
    }


if __name__ == "__main__":
    # Test the functions
    props = test_function_properties()
    print("Test function properties:")
    for key, value in props.items():
        print(f"  {key}: {value}")