"""
Test functions for Riemann Hypothesis validation.
Implements the working test functions from the validation notebook.
"""

import mpmath as mp
import math


def f1_notebook(u):
    """
    Test function f1 from notebook: exp(-u²/2) if |u| ≤ 3, 0 otherwise.
    """
    if abs(u) <= 3:
        return mp.exp(-u**2/2)
    else:
        return mp.mpf(0)


def f2_notebook(u): 
    """
    Test function f2 from notebook: exp(-u²) if |u| ≤ 2, 0 otherwise.
    """
    if abs(u) <= 2:
        return mp.exp(-u**2)
    else:
        return mp.mpf(0)


def f3_notebook(u):
    """
    Test function f3 from notebook: (1 - u²/4)² if |u| ≤ 2, 0 otherwise.
    """
    if abs(u) <= 2:
        return (1 - u**2/4)**2
    else:
        return mp.mpf(0)


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


def get_test_function(name):
    """Get test function by name with appropriate limits."""
    if name == 'f1':
        return f1_notebook, 3
    elif name == 'f2':
        return f2_notebook, 2  
    elif name == 'f3':
        return f3_notebook, 2
    elif name == 'gaussian':
        return phi_gaussian, 5
    elif name == 'truncated':
        return truncated_gaussian, 5
    else:
        raise ValueError(f"Unknown test function: {name}")


def test_function_properties():
    """
    Test properties of the test functions.
    Returns diagnostic information.
    """
    results = {}
    
    for name in ['f1', 'f2', 'f3']:
        func, lim = get_test_function(name)
        
        # Test symmetry and basic values
        results[name] = {
            'f(0)': func(0),
            'f(1)': func(1),
            'f(-1)': func(-1),
            'f(lim)': func(lim),
            'f(lim+0.1)': func(lim + 0.1),
            'symmetric': abs(func(1) - func(-1)) < 1e-15,
            'limit': lim
        }
    
    return results


if __name__ == "__main__":
    # Test the functions
    props = test_function_properties()
    print("Test function properties:")
    for name, data in props.items():
        print(f"\n{name} (limit={data['limit']}):")
        for key, value in data.items():
            if key != 'limit':
                print(f"  {key}: {value}")