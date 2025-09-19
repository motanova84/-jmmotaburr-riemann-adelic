import mpmath as mp
import sympy as sp
from utils.mellin import truncated_gaussian, mellin_transform
from utils.riemann_tools import t_to_n, load_zeros_near_t

mp.mp.dps = 50

def prime_sum(f, P, K):
    """Compute prime sum with proper mpmath type handling."""
    total = mp.mpf('0')
    # Generate all primes up to P
    primes = list(sp.primerange(2, P + 1))
    for p in primes:
        # Ensure proper mpmath conversion
        lp = mp.log(mp.mpf(p))
        for k in range(1, K + 1):
            # Use mpmath multiplication
            klp = mp.mpf(k) * lp
            total += lp * f(klp)
    return total

def archimedean_sum(f, sigma0=2.0, T=100, lim_u=5.0):
    """Compute archimedean sum with proper mpmath type handling."""
    def integrand(t):
        # Ensure proper mpmath types
        s = mp.mpf(sigma0) + 1j * mp.mpf(t)
        kernel = mp.digamma(s/mp.mpf(2)) - mp.log(mp.pi)
        return kernel * mellin_transform(f, s, lim_u)
    
    # Use mpmath bounds
    integral = mp.quad(integrand, [-mp.mpf(T), mp.mpf(T)])
    return (integral / (2j * mp.pi)).real

def zero_sum(f, zeros, lim_u=5.0):
    """Compute zero sum with proper mpmath handling and manual loop.
    
    Uses manual loop instead of potential mp.nsum for better performance
    and stability. Ensures all gamma values are properly handled as mpmath.
    """
    total = mp.mpf('0')
    for gamma in zeros:
        # Ensure gamma is mpmath format
        if not isinstance(gamma, mp.mpf):
            gamma = mp.mpf(gamma)
        fhat_val = mellin_transform(f, 1j * gamma, lim_u)
        total += fhat_val.real
    return total

if __name__ == "__main__":
    import sys
    if len(sys.argv) != 2:
        print("Uso: python validate_by_height.py <t_target>")
        sys.exit(1)

    t_target = mp.mpf(sys.argv[1])
    f = truncated_gaussian

    # Lado cero
    delta = 50
    zeros = load_zeros_near_t("zeros/zeros_t1e8.txt", t_target - delta, t_target + delta)
    Z = zero_sum(f, zeros)

    # Lado aritmético - reduced parameters for better performance
    P = 10000  # reduced from 100000 for better performance
    K = 5
    A = prime_sum(f, P, K) + archimedean_sum(f)

    print(f"Altura objetivo t = {t_target}")
    print(f"Número de ceros usados: {len(zeros)}")
    print(f"Parámetros: P={P}, K={K}")
    print(f"Lado Aritmético: {A}")
    print(f"Lado de Ceros:   {Z}")
    print(f"Error absoluto:  {abs(A - Z)}")
    print(f"Error relativo:  {abs(A - Z) / abs(A)}")

