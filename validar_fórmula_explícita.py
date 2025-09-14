"""
🧠 Copilot Prompt:
Create a GitHub Actions workflow to run this script on push and store the output CSV in /data/.

The script validates an explicit formula related to the Riemann Hypothesis.

It uses:
- f1, f2, f3: compactly supported test functions
- prime_sum(f), A_infty(f), zero_sum(f)
- Comparison of arithmetic vs spectral sides.

Add helper utilities if missing.

NOTA: Script optimizado para performance con parámetros reducidos.
Script en español como solicitado - validar_fórmula_explícita.py
"""

import mpmath as mp
import sympy as sp
from utils.mellin import truncated_gaussian, mellin_transform

mp.mp.dps = 20  # Reducido más para mejor performance

# Parámetros del experimento (optimizados para performance)
P = 500            # Máximo primo (reducido más para testing rápido)
K = 2              # Potencias máximas por primo (reducido para testing rápido)
sigma0 = 2.0
T = 10             # Reducido más para evitar timeouts
lim_u = 3.0        # Reducido también el límite de integración

def prime_sum(f, P, K):
    total = mp.mpf('0')
    # Generate all primes up to P
    primes = list(sp.primerange(2, P + 1))
    for p in primes:
        lp = mp.log(p)
        for k in range(1, K + 1):
            total += lp * f(k * lp)
    return total

def archimedean_sum(f, sigma0, T, lim_u):
    def integrand(t):
        s = sigma0 + 1j * t
        kernel = mp.digamma(s / 2) - mp.log(mp.pi)
        return kernel * mellin_transform(f, s, lim_u)
    # Use more conservative integration parameters to avoid timeouts
    integral, err = mp.quad(integrand, [-T, T], error=True, maxdegree=8)
    return (integral / (2j * mp.pi)).real

def zero_sum(f, filename, lim_u=3, max_zeros=1000):
    """Compute sum over zeros, with limit on number of zeros for performance"""
    total = mp.mpf('0')
    count = 0
    with open(filename) as file:
        for line in file:
            if count >= max_zeros:
                break
            gamma = mp.mpf(line.strip())
            total += mellin_transform(f, 1j * gamma, lim_u).real
            count += 1
    return total

if __name__ == "__main__":
    print("Iniciando validación de fórmula explícita...")
    print(f"Parámetros: P={P}, K={K}, T={T}, lim_u={lim_u}, dps={mp.mp.dps}")
    
    f = truncated_gaussian
    
    print("Calculando prime_sum...")
    prime_contrib = prime_sum(f, P, K)
    print(f"Prime sum: {prime_contrib}")
    
    print("Calculando archimedean_sum...")
    arch_contrib = archimedean_sum(f, sigma0, T, lim_u)
    print(f"Archimedean sum: {arch_contrib}")
    
    A = prime_contrib + arch_contrib
    print(f"Aritmético (Primes + Arch): {A}")
    
    print("Calculando zero_sum...")
    Z = zero_sum(f, 'zeros/zeros_t1e8.txt', lim_u, max_zeros=100)
    print(f"Zero side (explicit sum):   {Z}")
    
    error = abs(A - Z)
    print(f"Error absoluto:             {error}")
    if abs(A) > 0:
        print(f"Error relativo:             {error / abs(A)}")
    else:
        print("Error relativo: N/A (A=0)")
    
    print("Validación completada.")

