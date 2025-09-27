"""
Minimal mpmath mock for testing when mpmath is not available.
This provides basic functionality to allow the validation scripts to run.
"""
import math
import cmath

class MockMP:
    def __init__(self):
        self.dps = 15  # Default decimal precision
        self.mp = self  # Self-reference for mp.mp.dps
    
    def mpf(self, x):
        """Mock mpf function"""
        return float(x)
    
    def mpc(self, real, imag=0):
        """Mock mpc function"""
        return complex(real, imag)
    
    def log(self, x):
        """Mock log function"""
        if isinstance(x, complex):
            return cmath.log(x)
        return math.log(x)
    
    def sqrt(self, x):
        """Mock sqrt function"""
        if isinstance(x, complex):
            return cmath.sqrt(x)
        return math.sqrt(abs(x)) if x < 0 else math.sqrt(x)
    
    def exp(self, x):
        """Mock exp function"""
        if isinstance(x, complex):
            return cmath.exp(x)
        return math.exp(x)
    
    def sin(self, x):
        """Mock sin function"""
        if isinstance(x, complex):
            return cmath.sin(x)
        return math.sin(x)
    
    def cos(self, x):
        """Mock cos function"""
        if isinstance(x, complex):
            return cmath.cos(x)
        return math.cos(x)
    
    def pi(self):
        """Mock pi"""
        return math.pi
    
    def e(self):
        """Mock e"""
        return math.e
    
    def j(self):
        """Mock imaginary unit"""
        return 1j
    
    def power(self, base, exp):
        """Mock power function"""
        return base ** exp
    
    def digamma(self, x):
        """Mock digamma function - simplified approximation"""
        # Very rough approximation for testing
        if x > 5:
            return math.log(x) - 1/(2*x)
        else:
            return -0.5772 + (x-1) * 1.0  # Rough approximation
    
    def nstr(self, x, precision):
        """Mock nstr function"""
        return str(float(x))
    
    def quad(self, func, interval, maxdegree=None):
        """Mock quad function - very simple integration"""
        # Simple rectangular rule for testing
        a, b = interval
        n = 100
        h = (b - a) / n
        result = 0
        for i in range(n):
            x = a + i * h
            try:
                result += func(x) * h
            except:
                pass
        return result
    
    def polyval(self, coeffs, x):
        """Mock polyval function"""
        result = 0
        for i, c in enumerate(coeffs):
            result += c * (x ** (len(coeffs) - 1 - i))
        return result

# Create the mock instance
mp = MockMP()
pi = math.pi
e = math.e
j = 1j

def mpf(x):
    return float(x)

def mpc(real, imag=0):
    return complex(real, imag)

def log(x):
    if isinstance(x, complex):
        return cmath.log(x)
    return math.log(x)

def sqrt(x):
    if isinstance(x, complex):
        return cmath.sqrt(x)
    return math.sqrt(abs(x)) if x < 0 else math.sqrt(x)

def exp(x):
    if isinstance(x, complex):
        return cmath.exp(x)
    return math.exp(x)

def sin(x):
    if isinstance(x, complex):
        return cmath.sin(x)
    return math.sin(x)

def cos(x):
    if isinstance(x, complex):
        return cmath.cos(x)
    return math.cos(x)

def power(base, exp):
    return base ** exp

def digamma(x):
    # Very rough approximation for testing
    if x > 5:
        return math.log(x) - 1/(2*x)
    else:
        return -0.5772 + (x-1) * 1.0  # Rough approximation

def nstr(x, precision):
    return str(float(x))

def quad(func, interval, maxdegree=None):
    # Simple rectangular rule for testing
    a, b = interval
    n = 100
    h = (b - a) / n
    result = 0
    for i in range(n):
        x = a + i * h
        try:
            result += func(x) * h
        except:
            pass
    return result

def polyval(coeffs, x):
    result = 0
    for i, c in enumerate(coeffs):
        result += c * (x ** (len(coeffs) - 1 - i))
    return result