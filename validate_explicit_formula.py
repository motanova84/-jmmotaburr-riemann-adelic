import mpmath as mp
import sympy as sp
from utils.mellin import truncated_gaussian, mellin_transform

mp.mp.dps = 50

# Parámetros del experimento (según especificación)
delta = 0.01       # δ = 0.01
P = 1000          # P = 1000
K = 50            # K = 50
N_Xi = 2000       # N_Ξ = 2000
sigma0 = 2.0      # σ₀ = 2
T = 50            # T = 50
lim_u = 5.0

def prime_sum(f, P, K):
    total = mp.mpf('0')
    primes = list(sp.primerange(2, P + 1))  # Primos hasta P
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

def zero_sum(f, filename, lim_u=5, N_Xi=2000):
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
    import csv
    import os
    
    # Crear directorio de datos si no existe
    os.makedirs('data', exist_ok=True)
    
    # Funciones de prueba
    def f1(u): return mp.exp(-u**2/2) if abs(u) <= 3 else mp.mpf(0)
    def f2(u): return mp.exp(-u**2) if abs(u) <= 2 else mp.mpf(0)  
    def f3(u): return (1 - u**2/4)**2 if abs(u) <= 2 else mp.mpf(0)
    
    functions = [('f1', f1), ('f2', f2), ('f3', f3)]
    results = []
    
    print("🔬 Validación de Fórmula Explícita para Hipótesis de Riemann")
    print(f"Parámetros: δ={delta}, P={P}, K={K}, N_Ξ={N_Xi}, σ₀={sigma0}, T={T}")
    print("=" * 70)
    
    for fname, f in functions:
        print(f"\n📊 Validando función {fname}...")
        
        # Calcular lado aritmético
        prime_term = prime_sum(f, P, K)
        arch_term = archimedean_sum(f, sigma0, T, lim_u)
        A = prime_term + arch_term
        
        # Calcular lado de ceros
        Z = zero_sum(f, 'zeros/zeros_t1e8.txt', lim_u, N_Xi)
        
        # Calcular error
        error = abs(A - Z)
        rel_error = error / abs(A) if abs(A) > 0 else float('inf')
        
        print(f"  PrimeSum({fname}) = {prime_term}")
        print(f"  A_∞({fname}) = {arch_term}")
        print(f"  Aritmético Total: {A}")
        print(f"  Zero Sum: {Z}")
        print(f"  Error absoluto: {error}")
        print(f"  Error relativo: {rel_error}")
        
        # Validar criterio de éxito
        success = error < 1e-5
        print(f"  ✅ ÉXITO" if success else f"  ❌ FALLO (error > 1e-5)")
        
        results.append({
            'function': fname,
            'prime_sum': float(prime_term),
            'archimedean_sum': float(arch_term), 
            'arithmetic_total': float(A),
            'zero_sum': float(Z),
            'absolute_error': float(error),
            'relative_error': float(rel_error),
            'success': success
        })
    
    # Exportar resultados a CSV
    with open('data/validation_output.csv', 'w', newline='') as csvfile:
        fieldnames = ['function', 'prime_sum', 'archimedean_sum', 'arithmetic_total', 
                     'zero_sum', 'absolute_error', 'relative_error', 'success']
        writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
        writer.writeheader()
        for result in results:
            writer.writerow(result)
    
    print(f"\n📄 Resultados exportados a: data/validation_output.csv")
    
    # Resumen final
    all_success = all(r['success'] for r in results)
    print(f"\n🎯 VALIDACIÓN FINAL: {'✅ TODAS LAS FUNCIONES EXITOSAS' if all_success else '❌ ALGUNAS FUNCIONES FALLARON'}")

