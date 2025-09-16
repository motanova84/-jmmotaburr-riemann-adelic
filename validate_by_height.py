import mpmath as mp
import sympy as sp
import os
from utils.mellin import truncated_gaussian, mellin_transform
from utils.riemann_tools import t_to_n, load_zeros_near_t

mp.mp.dps = 25  # Reduced precision for better performance

def prime_sum(f, P, K):
    total = mp.mpf('0')
    # Generate all primes up to P
    primes = list(sp.primerange(2, P + 1))
    for p in primes:
        lp = mp.log(p)
        for k in range(1, K + 1):
            total += lp * f(k * lp)
    return total

def archimedean_sum(f, sigma0=2.0, T=50, lim_u=3.0):  # Reduced T and lim_u for better performance
    """Compute archimedean sum with reduced parameters for performance."""
    def integrand(t):
        s = sigma0 + 1j * t
        kernel = mp.digamma(s/2) - mp.log(mp.pi)
        return kernel * mellin_transform(f, s, lim_u)
    
    try:
        result = mp.quad(integrand, [-T, T], maxdegree=5)  # Reduced maxdegree
        return (result / (2j * mp.pi)).real
    except Exception as e:
        print(f"Warning: Archimedean sum computation error: {e}")
        return mp.mpf('0')

def zero_sum(f, zeros, lim_u=5.0):
    total = mp.mpf('0')
    for gamma in zeros:
        fhat_val = mellin_transform(f, 1j * gamma, lim_u)
        total += fhat_val.real
    return total

if __name__ == "__main__":
    import sys
    if len(sys.argv) != 2:
        print("Uso: python validate_by_height.py <t_target>")
        print("Ejemplo: python validate_by_height.py 100")
        sys.exit(1)

    try:
        t_target = mp.mpf(sys.argv[1])
        if t_target <= 0:
            print("Error: t_target debe ser un número positivo")
            sys.exit(1)
    except ValueError:
        print("Error: t_target debe ser un número válido")
        sys.exit(1)

    print(f"🔬 Iniciando validación por altura para t = {t_target}")
    
    f = truncated_gaussian

    # Check if zeros file exists
    zeros_file = "zeros/zeros_t1e8.txt"
    if not os.path.exists(zeros_file):
        print(f"❌ Archivo de ceros no encontrado: {zeros_file}")
        sys.exit(1)

    try:
        # Lado cero
        delta = 50
        print(f"Cargando ceros en el rango [{t_target - delta}, {t_target + delta}]...")
        zeros = load_zeros_near_t(zeros_file, t_target - delta, t_target + delta)
        if not zeros:
            print(f"⚠️  No se encontraron ceros en el rango especificado")
            sys.exit(1)
        
        print("Calculando suma de ceros...")
        Z = zero_sum(f, zeros)

        # Lado aritmético - reduced parameters for better performance
        P = 1000  # hasta 1k primos (further reduced from 10k)
        K = 3     # reduced K for faster computation
        print("Calculando lado aritmético...")
        A = prime_sum(f, P, K) + archimedean_sum(f)

        print(f"\n✅ Resultados:")
        print(f"Altura objetivo t = {t_target}")
        print(f"Número de ceros usados: {len(zeros)}")
        print(f"Lado Aritmético: {A}")
        print(f"Lado de Ceros:   {Z}")
        print(f"Error absoluto:  {abs(A - Z)}")
        if abs(A) > 0:
            print(f"Error relativo:  {abs(A - Z) / abs(A)}")
        else:
            print("Error relativo:  undefined (arithmetic side is zero)")
            
    except Exception as e:
        print(f"❌ Error durante el cálculo: {e}")
        sys.exit(1)

