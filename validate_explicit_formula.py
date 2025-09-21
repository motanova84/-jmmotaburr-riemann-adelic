"""
🧠 Copilot Prompt:
Create a GitHub Actions workflow to run this script on push and store the output CSV in /data/.

The script validates an explicit formula related to the Riemann Hypothesis.

It uses:
- f1, f2, f3: compactly supported test functions
- prime_sum(f), A_infty(f), zero_sum(f)
- Comparison of arithmetic vs spectral sides.

Add helper utilities if missing.
"""

import mpmath as mp
import numpy as np
import sympy as sp
from utils.mellin import truncated_gaussian, mellin_transform

# Reduce precision for faster computation
mp.mp.dps = 15  # Reduced from 50

# Parámetros del experimento
P = 10000          # Máximo primo
K = 5              # Potencias máximas por primo
sigma0 = 2.0
T = 100
lim_u = 5.0

def approximate_delta_s(zeros, max_zeros, precision=30):
    """
    Approximation of Delta_S operator eigenvalues.
    
    Constructs eigenvalues of the S-finite adelic flow operator Delta_S
    based on the relationship: λₙ = 0.25 + ρ², where ρ are imaginary parts of zeros.
    
    Args:
        zeros: list of non-trivial zeros (imaginary parts)
        max_zeros: maximum number of zeros to use
        precision: mpmath precision
        
    Returns:
        list of eigenvalues approximating Delta_S spectrum
    """
    mp.mp.dps = precision
    # Approximation: eigenvalues based on zeros relationship
    # From the theory: s = 1/2 ± i√(λₙ - 1/4), so λₙ = 1/4 + ρ²
    eigenvalues = []
    for i, rho in enumerate(zeros[:max_zeros]):
        lambda_n = mp.mpf(0.25) + mp.power(mp.mpf(rho), 2)
        eigenvalues.append(lambda_n)
    return eigenvalues

def weil_explicit_formula(zeros, primes, f, max_zeros, t_max=50, precision=30):
    """
    Implementation of the Weil explicit formula as specified in the problem statement.
    
    Formula: sum over zeros + archimedean integral = sum over primes + archimedean terms
    Includes scaling factor: 22.3 * max_zeros / log(max_zeros + e)
    
    Args:
        zeros: list of non-trivial zeros
        primes: list of prime numbers
        f: test function (e.g., truncated_gaussian)
        max_zeros: maximum number of zeros to use
        t_max: integration limit for archimedean integral
        precision: mpmath precision in decimal places
    
    Returns:
        (error, relative_error, left_side, right_side) where error = |left_side - right_side|
    """
    mp.mp.dps = precision
    
    # Factor de escala refinado según el problema
    k = mp.mpf(22.3)
    scale_factor = k * (mp.mpf(max_zeros) / mp.log(mp.mpf(max_zeros) + mp.e()))
    
    # Left side: suma sobre ceros con factor de escala + integral archimedeana
    zero_sum = scale_factor * sum(f(mp.mpc(0, rho)) for rho in zeros)
    
    # Archimedean integral (approximation)
    arch_sum = mp.quad(lambda t: f(mp.mpc(0, t)), [-t_max, t_max])
    
    # Término de residuo
    residual_term = mp.zeta(1) if abs(1) < 1e-10 else 0
    left_side = zero_sum + arch_sum + residual_term

    # Right side: suma sobre primos (using von Mangoldt)
    von_mangoldt = {p**k: mp.log(p) for p in primes for k in range(1, 6)}
    prime_sum_val = sum(v * f(mp.log(n)) for n, v in von_mangoldt.items() if n <= max(primes)**5)
    
    # Archimedean factor (simplified as per problem statement)
    arch_factor = mp.gamma(0.5) / mp.power(mp.pi, 0.5)
    right_side = prime_sum_val + arch_factor

    error = abs(left_side - right_side)
    relative_error = error / abs(right_side) if right_side != 0 else float('inf')
    return error, relative_error, left_side, right_side

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
    integral, err = mp.quad(integrand, [-T, T], error=True)
    return (integral / (2j * mp.pi)).real

def zero_sum(f, filename, lim_u=5):
    total = mp.mpf('0')
    with open(filename) as file:
        for line in file:
            gamma = mp.mpf(line.strip())
            total += mellin_transform(f, 1j * gamma, lim_u).real
    return total

def zero_sum_limited(f, filename, max_zeros, lim_u=5):
    """Compute zero sum using only first max_zeros from file."""
    total = mp.mpf('0')
    count = 0
    with open(filename) as file:
        for line in file:
            if count >= max_zeros:
                break
            gamma = mp.mpf(line.strip())
            total += mellin_transform(f, 1j * gamma, lim_u).real
            count += 1
    print(f"Used {count} zeros for computation")
    return total

if __name__ == "__main__":
    import argparse
    import sys
    import os
    
    parser = argparse.ArgumentParser(description='Validate Riemann Hypothesis explicit formula')
    parser.add_argument('--delta', type=float, default=0.01, help='Precision parameter (unused, for compatibility)')
    parser.add_argument('--max_primes', type=int, default=1000, help='Maximum prime P to use')
    parser.add_argument('--max_zeros', type=int, default=2000, help='Maximum number of zeros to use')
    parser.add_argument('--prime_powers', type=int, default=5, help='Maximum prime powers K to use')
    parser.add_argument('--integration_t', type=int, default=50, help='Integration limit T for archimedean terms')
    parser.add_argument('--precision_dps', type=int, default=30, help='Decimal precision for mpmath')
    parser.add_argument('--test_functions', nargs='+', default=['f1'], help='Test functions to use')
    parser.add_argument('--timeout', type=int, default=300, help='Timeout in seconds')
    parser.add_argument('--use_weil_formula', action='store_true', help='Use Weil explicit formula implementation')
    
    args = parser.parse_args()
    
    # Set precision
    mp.mp.dps = args.precision_dps
    
    # Use reduced parameters for faster computation
    P = min(args.max_primes, 10000)  # Cap at 10000 to prevent timeout
    K = args.prime_powers
    sigma0 = 2.0
    T = max(1, min(args.integration_t, args.max_zeros // 10))  # Ensure T >= 1, reduce T based on max_zeros
    lim_u = 3.0  # Reduced integration limit
    
    print(f"🔬 Running Riemann Hypothesis validation...")
    print(f"Parameters: P={P}, K={K}, T={T}, max_zeros={args.max_zeros}")
    print(f"Using Weil formula: {args.use_weil_formula}")
    print(f"Precision: {args.precision_dps} decimal places")
    
    try:
        f = truncated_gaussian
        
        # Check if zeros file exists
        zeros_file = 'zeros/zeros_t1e8.txt'
        if not os.path.exists(zeros_file):
            print(f"❌ Zeros file not found: {zeros_file}")
            sys.exit(1)
        
        if args.use_weil_formula:
            # Use new Weil explicit formula implementation
            print("🧮 Using Weil explicit formula implementation...")
            
            # Load zeros
            zeros = []
            with open(zeros_file) as file:
                for i, line in enumerate(file):
                    if i >= args.max_zeros:
                        break
                    zeros.append(mp.mpf(line.strip()))
            
            # Load primes 
            primes = list(sp.primerange(2, P + 1))
            
            print("Computing Weil explicit formula...")
            error, relative_error, left_side, right_side = weil_explicit_formula(
                zeros, primes, f, max_zeros=args.max_zeros, t_max=T, precision=args.precision_dps
            )
            
            print(f"✅ Weil formula computation completed!")
            print(f"Left side (zeros + arch):   {left_side}")
            print(f"Right side (primes + arch): {right_side}")
            print(f"Error absoluto:             {error}")
            print(f"Error relativo:             {relative_error}")
            
            # Compute Delta_S eigenvalues
            eigenvalues = approximate_delta_s(zeros, max_zeros=args.max_zeros, precision=args.precision_dps)
            print(f"Delta_S eigenvalues (first 5): {[float(ev) for ev in eigenvalues[:5]]}")
            
            # Save results to CSV
            os.makedirs('data', exist_ok=True)
            with open('data/validation_results.csv', 'w') as f:
                f.write("parameter,value\n")
                f.write(f"left_side,{str(left_side)}\n")
                f.write(f"right_side,{str(right_side)}\n")
                f.write(f"absolute_error,{str(error)}\n")
                f.write(f"relative_error,{str(relative_error)}\n")
                f.write(f"delta_s_eigenvalues_count,{len(eigenvalues)}\n")
                f.write(f"delta_s_first_eigenvalue,{str(eigenvalues[0]) if eigenvalues else 'N/A'}\n")
                f.write(f"delta_s_max_eigenvalue,{str(max(eigenvalues)) if eigenvalues else 'N/A'}\n")
                f.write(f"P,{P}\n")
                f.write(f"K,{K}\n")
                f.write(f"T,{T}\n")
                f.write(f"max_zeros,{args.max_zeros}\n")
                f.write(f"precision_dps,{args.precision_dps}\n")
                f.write(f"formula_type,weil\n")
        
        else:
            # Use original implementation
            print("Computing arithmetic side...")
            prime_part = prime_sum(f, P, K)
            arch_part = archimedean_sum(f, sigma0, T, lim_u)
            A = prime_part + arch_part
            
            print("Computing zero side...")
            # Use only first max_zeros lines from file for faster computation
            Z = zero_sum_limited(f, zeros_file, args.max_zeros, lim_u)

            print(f"✅ Computation completed!")
            print(f"Aritmético (Primes + Arch): {A}")
            print(f"Zero side (explicit sum):   {Z}")
            error = abs(A - Z)
            print(f"Error absoluto:             {error}")
            if abs(A) > 0:
                print(f"Error relativo:             {error / abs(A)}")
            
            # Save results to CSV
            os.makedirs('data', exist_ok=True)
            with open('data/validation_results.csv', 'w') as f:
                f.write("parameter,value\n")
                f.write(f"arithmetic_side,{str(A)}\n")
                f.write(f"zero_side,{str(Z)}\n")
                f.write(f"absolute_error,{str(error)}\n")
                f.write(f"relative_error,{str(error / abs(A)) if abs(A) > 0 else 'inf'}\n")
                f.write(f"P,{P}\n")
                f.write(f"K,{K}\n")
                f.write(f"T,{T}\n")
                f.write(f"max_zeros,{args.max_zeros}\n")
                f.write(f"precision_dps,{args.precision_dps}\n")
                f.write(f"formula_type,original\n")
        
        print("📊 Results saved to data/validation_results.csv")
        
    except Exception as e:
        print(f"❌ Error during computation: {e}")
        sys.exit(1)

