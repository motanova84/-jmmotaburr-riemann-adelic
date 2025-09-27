try:
    import mpmath as mp
except ImportError:
    import sys
    sys.path.append('..')
    import mpmath_mock as mp

def truncated_gaussian(u, a=5.0, sigma=1.0):
    """Smooth compactly supported Gaussian function."""
    if abs(u) > a:
        return mp.mpf('0')
    return mp.exp(-u**2 / (2 * sigma**2))

def f1(u, a=3.0):
    """First compactly supported test function - smooth bump function."""
    if abs(u) > a:
        return mp.mpf('0')
    # Smooth bump function: exp(-1/(1-u^2/a^2))
    x = u / a
    if abs(x) >= 1:
        return mp.mpf('0')
    try:
        return mp.exp(-mp.mpf(1) / (mp.mpf(1) - x**2))
    except:
        return mp.mpf('0')

def f2(u, a=4.0):
    """Second compactly supported test function - cosine-based."""
    if abs(u) > a:
        return mp.mpf('0')
    # Cosine-based compactly supported function
    return (mp.cos(mp.pi * u / (2 * a)))**2

def f3(u, a=2.5):
    """Third compactly supported test function - polynomial cutoff."""
    if abs(u) > a:
        return mp.mpf('0')
    # Polynomial with smooth cutoff
    x = u / a
    return (mp.mpf(1) - x**2)**3 * mp.exp(-x**2)

def A_infty(f, sigma0=2.0, T=100, lim_u=5.0):
    """
    Archimedean contribution A_∞(f) to the explicit formula.
    
    This computes the archimedean integral:
    A_∞(f) = (1/2πi) ∫_{σ₀-iT}^{σ₀+iT} [ψ(s/2) - log(π)] F̃(s) ds
    
    where ψ(s) is the digamma function and F̃(s) is the Mellin transform of f.
    """
    def integrand(t):
        s = sigma0 + 1j * t
        try:
            # Digamma function ψ(s/2) - log(π)
            kernel = mp.digamma(s / 2) - mp.log(mp.pi)
            # Mellin transform F̃(s) 
            mellin_f = mellin_transform(f, s, lim_u)
            return kernel * mellin_f
        except:
            return mp.mpf('0')
    
    try:
        result = mp.quad(integrand, [-T, T], error=True)
        if hasattr(result, '__len__') and len(result) >= 2:
            integral, err = result
        else:
            integral = result
            err = 0
    except:
        integral = 0
        err = 0
        
    return (integral / (2j * mp.pi)).real

def mellin_transform(f, s, lim=5.0):
    """Numerical Mellin transform: ∫ f(u) e^{su} du."""
    try:
        result = mp.quad(lambda u: f(u) * mp.exp(s * u), [-lim, lim], maxdegree=10)
        if hasattr(result, '__len__'):
            return result[0]  # Take first element if tuple (value, error)
        return result
    except:
        return mp.mpf('0')  # Fallback if integration fails

