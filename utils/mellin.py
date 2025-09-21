import mpmath as mp

def truncated_gaussian(u, a=5.0, sigma=1.0):
    """Smooth compactly supported Gaussian function."""
    if abs(u) > a:
        return mp.mpf('0')
    return mp.exp(-u**2 / (2 * sigma**2))

def mellin_transform(f, s, lim=5.0):
    """Numerical Mellin transform: ∫ f(u) e^{su} du."""
    return mp.quad(lambda u: f(u) * mp.exp(s * u), [-lim, lim], maxdegree=10)  # Reduced from 20

# Compactly supported test functions f1, f2, f3
def f1(u, a=3.0):
    """Test function f1: Smooth bump function with compact support."""
    if abs(u) >= a:
        return mp.mpf('0')
    return mp.exp(-1 / (1 - (u / a)**2))

def f2(u, a=4.0, sigma=1.5):
    """Test function f2: Modified Gaussian with wider support."""
    if abs(u) > a:
        return mp.mpf('0')
    return mp.exp(-u**2 / (2 * sigma**2)) * mp.cos(u)

def f3(u, a=2.5):
    """Test function f3: Polynomial cutoff function."""
    if abs(u) > a:
        return mp.mpf('0')
    t = u / a
    return (1 - t**2)**3

# Function selector for test functions
def get_test_function(name):
    """Return the test function by name."""
    functions = {
        'f1': f1,
        'f2': f2, 
        'f3': f3,
        'gaussian': truncated_gaussian,
        'truncated_gaussian': truncated_gaussian
    }
    return functions.get(name, truncated_gaussian)

