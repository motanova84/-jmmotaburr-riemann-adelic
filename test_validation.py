import mpmath as mp
import sympy as sp
from utils.mellin import truncated_gaussian, mellin_transform

mp.mp.dps = 30  # Reduced precision for testing

# Parámetros de prueba reducidos
P_test = 100          # Reduced from 1000
K_test = 10           # Reduced from 50
N_Xi_test = 500       # Reduced from 2000
sigma0 = 2.0
T_test = 20           # Reduced from 50
lim_u = 3.0           # Reduced from 5.0

def prime_sum(f, P, K):
    total = mp.mpf('0')
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
    integral, err = mp.quad(integrand, [-T, T], error=True)
    return (integral / (2j * mp.pi)).real

def zero_sum(f, filename, lim_u=3, N_Xi=500):
    total = mp.mpf('0')
    count = 0
    with open(filename) as file:
        for line in file:
            if count >= N_Xi:
                break
            gamma = mp.mpf(line.strip())
            total += mellin_transform(f, 1j * gamma, lim_u).real
            count += 1
    return total

if __name__ == "__main__":
    # Test function
    def f_test(u): 
        return mp.exp(-u**2/2) if abs(u) <= 3 else mp.mpf(0)
    
    print("🧪 Test rápido del sistema de validación")
    print(f"Parámetros de prueba: P={P_test}, K={K_test}, N_Ξ={N_Xi_test}, T={T_test}")
    print("=" * 60)
    
    try:
        print("Calculando lado aritmético...")
        prime_term = prime_sum(f_test, P_test, K_test)
        print(f"  Prime sum: {prime_term}")
        
        arch_term = archimedean_sum(f_test, sigma0, T_test, lim_u)
        print(f"  Archimedean sum: {arch_term}")
        
        A = prime_term + arch_term
        print(f"  Total aritmético: {A}")
        
        print("Calculando lado de ceros...")
        Z = zero_sum(f_test, 'zeros/zeros_t1e8.txt', lim_u, N_Xi_test)
        print(f"  Zero sum: {Z}")
        
        error = abs(A - Z)
        rel_error = error / abs(A) if abs(A) > 0 else float('inf')
        
        print(f"\n📊 Resultados:")
        print(f"  Error absoluto: {error}")
        print(f"  Error relativo: {rel_error}")
        print(f"  ✅ Éxito: {error < 1e-5}")
        
    except Exception as e:
        print(f"❌ Error: {e}")
        import traceback
        traceback.print_exc()