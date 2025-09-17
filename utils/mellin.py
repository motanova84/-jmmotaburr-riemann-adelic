import mpmath as mp

def truncated_gaussian(u, a=5.0, sigma=1.0):
    """Smooth compactly supported Gaussian function."""
    if abs(u) > a:
        return mp.mpf('0')
    return mp.exp(-u**2 / (2 * sigma**2))

def mellin_transform(f, s, lim=5.0):
    """Numerical Mellin transform: ∫ f(u) e^{su} du with adaptive precision."""
    # Adaptive maxdegree based on the imaginary part of s
    if hasattr(s, 'imag'):
        base_degree = 8 if abs(s.imag) > 100 else 10
    else:
        base_degree = 10
    
    # Further reduce degree for very large limits  
    maxdegree = max(5, min(base_degree, int(15 - lim/2)))
    
    return mp.quad(lambda u: f(u) * mp.exp(s * u), [-lim, lim], maxdegree=maxdegree)

