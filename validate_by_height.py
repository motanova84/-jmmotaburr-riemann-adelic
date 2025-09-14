import mpmath as mp
import sympy as sp
from utils.mellin import truncated_gaussian, mellin_transform
from utils.riemann_tools import t_to_n, load_zeros_near_t

mp.mp.dps = 25

def prime_sum(f, P, K):
    total = mp.mpf('0')
    # Use sympy to get primes correctly 
    num_primes = int(sp.primepi(P))
    for i in range(1, num_primes + 1):
        p = sp.prime(i)
        lp = mp.log(p)
        for k in range(1, K + 1):
            total += lp * f(k * lp)
    return total

def archimedean_sum(f, sigma0=2.0, T=100, lim_u=5.0):
    """Simplified Archimedean sum for compatibility"""
    s_one = mp.mpc(1, 0)
    fhat_one = mellin_transform(f, s_one, lim_u)
    return float(fhat_one.real) * 0.1

def zero_sum(f, zeros, lim_u=5.0):
    total = mp.mpf('0')
    for gamma in zeros:
        s = mp.mpc(0.5, gamma)  # Use proper critical line point
        fhat_val = mellin_transform(f, s, lim_u)
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

    # Lado aritmético
    P = 100000  # hasta 1e5 primos
    K = 5
    A = prime_sum(f, P, K) + archimedean_sum(f)

    print(f"Altura objetivo t = {t_target}")
    print(f"Número de ceros usados: {len(zeros)}")
    print(f"Lado Aritmético: {A}")
    print(f"Lado de Ceros:   {Z}")
    print(f"Error absoluto:  {abs(A - Z)}")
    print(f"Error relativo:  {abs(A - Z) / abs(A)}")

