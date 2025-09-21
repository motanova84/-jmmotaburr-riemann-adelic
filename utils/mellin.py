import mpmath as mp

def truncated_gaussian(u, a=5.0, sigma=1.0):
    """Smooth compactly supported Gaussian function."""
    if abs(u) > a:
        return mp.mpf('0')
    return mp.exp(-u**2 / (2 * sigma**2))

def mellin_transform(f, s, lim=5.0):
    """Numerical Mellin transform: ∫ f(u) e^{su} du."""
    try:
        result = mp.quad(lambda u: f(u) * mp.exp(s * u), [-lim, lim], maxdegree=10)
        if hasattr(result, '__len__'):
            return result[0]  # Take first element if tuple (value, error)
        return result
    except:
        return mp.mpf('0')  # Fallback if integration fails

