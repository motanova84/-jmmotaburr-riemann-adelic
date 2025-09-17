"""
Simple test with different functions to understand convergence
"""

import mpmath as mp
import sympy as sp

mp.mp.dps = 15  # Start with lower precision for speed

def simple_test_function(u):
    """Simple smooth test function"""
    if abs(u) <= 1:
        return mp.exp(-1 / (1 - u**2))  # Smooth compactly supported
    else:
        return mp.mpf(0)

def fhat(f, s, lim):
    """Mellin transform"""
    return mp.quad(lambda u: f(u) * mp.exp(s * u), [-lim, lim], maxdegree=8)

def simple_validation(P=200, N_zeros=50, T=10):
    """Simple validation with minimal parameters"""
    
    f = simple_test_function
    lim = 2.0
    
    print(f"Simple validation: P={P}, N_zeros={N_zeros}, T={T}")
    
    # Prime sum
    print("Computing prime sum...")
    prime_sum = mp.mpf(0)
    primes = list(sp.primerange(2, P))
    for p in primes:
        lp = mp.log(p)
        prime_sum += lp * f(lp)  # Only k=1 term for simplicity
    
    print(f"Prime sum: {prime_sum}")
    
    # Archimedean part
    print("Computing archimedean part...")
    def integrand(t):
        s = mp.mpc(2.0, t)
        return (mp.digamma(s/2) - mp.log(mp.pi)) * fhat(f, s, lim)
    
    arch_integral = mp.quad(integrand, [-T, T], maxdegree=8) / (2 * mp.pi)
    residue = fhat(f, mp.mpf(1), lim)
    arch_sum = arch_integral - residue
    
    print(f"Arch integral: {arch_integral}")
    print(f"Residue: {residue}")
    print(f"Arch sum: {arch_sum}")
    
    # Zero sum using zetazero
    print("Computing zero sum...")
    zero_sum = mp.mpf(0)
    for n in range(1, N_zeros + 1):
        rho = mp.zetazero(n)
        gamma = mp.im(rho)
        zero_contribution = fhat(f, 1j * gamma, lim).real
        zero_sum += zero_contribution
        
        if n <= 5:  # Debug first few terms
            print(f"  Zero {n}: gamma={gamma}, contribution={zero_contribution}")
    
    print(f"Zero sum: {zero_sum}")
    
    # Results
    arithmetic_side = prime_sum + arch_sum.real
    error = abs(arithmetic_side - zero_sum)
    
    print(f"\nResults:")
    print(f"Arithmetic side: {arithmetic_side}")
    print(f"Zero side:       {zero_sum}")
    print(f"Error:           {error}")
    
    return error

if __name__ == "__main__":
    simple_validation()