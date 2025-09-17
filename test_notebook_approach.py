"""
Test using the exact notebook approach with mp.zetazero
"""

import mpmath as mp
import sympy as sp
from utils.mellin import truncated_gaussian

mp.mp.dps = 20

def fhat(f, s, lim):
    """Mellin transform as in notebook"""
    return mp.quad(lambda u: f(u) * mp.exp(s * u), [-lim, lim], maxdegree=10)

def prime_sum_notebook(f, P=500, K=5):
    """Prime sum exactly as in notebook"""
    s = mp.mpf(0)
    primes = list(sp.primerange(2, P + 1))
    for p in primes:
        lp = mp.log(p)
        for k in range(1, K+1):
            s += lp * f(k * lp)
    return s

def A_infty_notebook(f, sigma0=2.0, lim=3, T=20):
    """A_infty exactly as in notebook"""
    def integrand(t):
        s = mp.mpc(sigma0, t)
        return (mp.digamma(s/2) - mp.log(mp.pi)) * fhat(f, s, lim)
    integ = mp.quad(integrand, [-T, T], maxdegree=10) / (2 * mp.pi)
    res1 = fhat(f, mp.mpf(1), lim) / mp.mpf(1)
    return integ - res1

def zero_sum_notebook(f, N=100, lim=3):
    """Zero sum exactly as in notebook using zetazero"""
    s = mp.mpf(0)
    for n in range(1, N+1):
        rho = mp.zetazero(n)
        # The notebook uses fhat(f, mp.im(rho), lim) 
        # but fhat is the Mellin transform, so we need the proper complex argument
        s += fhat(f, 1j * mp.im(rho), lim).real
    return s

def test_notebook_approach():
    """Test the exact notebook approach"""
    f = truncated_gaussian
    lim = 3
    
    print("Testing notebook approach...")
    print(f"Using truncated_gaussian with lim={lim}")
    
    # Test with small parameters first
    print("\n--- Computing prime sum ---")
    ps = prime_sum_notebook(f, P=500, K=5)
    print(f"Prime sum: {ps}")
    
    print("\n--- Computing A_infty ---")
    ain = A_infty_notebook(f, sigma0=2.0, lim=lim, T=20)
    print(f"A_infty: {ain}")
    
    print("\n--- Computing zero sum ---")
    zs = zero_sum_notebook(f, N=100, lim=lim)
    print(f"Zero sum: {zs}")
    
    # Total comparison
    tot = ps + ain
    err = abs(tot - zs)
    
    print(f"\n--- Results ---")
    print(f"Prime + A_infty: {tot}")
    print(f"Zero sum:        {zs}")
    print(f"Error:           {err}")
    print(f"Relative error:  {err / abs(tot) if abs(tot) > 0 else 'inf'}")
    
    if err <= 1e-6:
        print("🎯 SUCCESS: Target error achieved!")
    else:
        print(f"⚠️  Need improvement: {err:.2e} > 1e-6")
    
    return err

if __name__ == "__main__":
    test_notebook_approach()