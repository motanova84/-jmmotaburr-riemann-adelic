import mpmath as mp

def truncated_gaussian(u, a=50.0, sigma=10.0):
    """Smooth compactly supported Gaussian function with larger support."""
    if abs(u) > a:
        return mp.mpf('0')
    return mp.exp(-u**2 / (2 * sigma**2))

def mellin_transform(f, s, lim=5.0):
    """Numerical Mellin transform: ∫ f(u) e^{su} du."""
    return mp.quad(lambda u: f(u) * mp.exp(s * u), [-lim, lim], maxdegree=10)  # Reduced from 20

