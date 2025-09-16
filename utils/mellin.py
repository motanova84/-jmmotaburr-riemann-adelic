import mpmath as mp

def truncated_gaussian(u, a=5.0, sigma=1.0):
    """
    Smooth compactly supported Gaussian function.
    
    Args:
        u: Input value
        a: Truncation parameter (default: 5.0)
        sigma: Standard deviation (default: 1.0)
    
    Returns:
        exp(-u^2 / (2*sigma^2)) if |u| <= a, else 0
    """
    if abs(u) > a:
        return mp.mpf('0')
    return mp.exp(-u**2 / (2 * sigma**2))

def mellin_transform(f, s, lim=5.0):
    """
    Numerical Mellin transform: ∫ f(u) e^{su} du.
    
    Args:
        f: Function to transform
        s: Complex parameter
        lim: Integration limit (default: 5.0)
    
    Returns:
        Complex number representing the Mellin transform
    """
    try:
        return mp.quad(lambda u: f(u) * mp.exp(s * u), [-lim, lim], maxdegree=10)
    except Exception as e:
        print(f"Warning: Mellin transform integration error: {e}")
        return mp.mpc('0', '0')

