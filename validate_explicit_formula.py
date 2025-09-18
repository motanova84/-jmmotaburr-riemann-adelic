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
    parser.add_argument('--test_functions', nargs='+', default=['f1'], help='Test functions to use')
    parser.add_argument('--timeout', type=int, default=300, help='Timeout in seconds')
    
    args = parser.parse_args()
    
    # Use reduced parameters for faster computation
    P = min(args.max_primes, 10000)  # Cap at 10000 to prevent timeout
    K = 5
    sigma0 = 2.0
    T = max(1, min(100, args.max_zeros // 10))  # Ensure T >= 1, reduce T based on max_zeros
    lim_u = 3.0  # Reduced integration limit
    
    print(f"🔬 Running Riemann Hypothesis validation...")
    print(f"Parameters: P={P}, K={K}, T={T}, max_zeros={args.max_zeros}")
    
    try:
        f = truncated_gaussian
        
        # Check if zeros file exists
        zeros_file = 'zeros/zeros_t1e8.txt'
        if not os.path.exists(zeros_file):
            print(f"❌ Zeros file not found: {zeros_file}")
            # Create error CSV for auto-evolution continuity
            os.makedirs('data', exist_ok=True)
            with open('data/validation_results.csv', 'w') as f:
                f.write("parameter,value\n")
                f.write(f"arithmetic_side,ERROR\n")
                f.write(f"zero_side,ERROR\n")
                f.write(f"absolute_error,inf\n")
                f.write(f"relative_error,inf\n")
                f.write(f"verified,ERROR\n")
                f.write(f"tolerance_absolute,0.01\n")
                f.write(f"tolerance_relative,0.05\n")
                f.write(f"P,{P}\n")
                f.write(f"K,{K}\n")
                f.write(f"T,{T}\n")
                f.write(f"max_zeros,{args.max_zeros}\n")
                f.write(f"frequency_hz,141.7001\n")
                f.write(f"signature,JMMB Ψ✧\n")
                f.write(f"error_message,Zeros file not found: {zeros_file}\n")
            print("📊 Error information saved to data/validation_results.csv for auto-evolution continuity")
            sys.exit(1)
        
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
        relative_error = error / abs(A) if abs(A) > 0 else float('inf')
        
        # Determine verification verdict based on error thresholds
        # Note: These are research-appropriate tolerances for the Riemann Hypothesis validation
        tolerance_absolute = 0.01  # Strict absolute tolerance for mathematical precision
        tolerance_relative = 0.05  # 5% relative error tolerance
        verified = error < tolerance_absolute and relative_error < tolerance_relative
        verdict = "YES" if verified else "NO"
        
        print(f"Error absoluto:             {error}")
        if abs(A) > 0:
            print(f"Error relativo:             {relative_error}")
        print(f"🎯 Verification verdict:     {verdict}")
        
        # Save results to CSV
        os.makedirs('data', exist_ok=True)
        with open('data/validation_results.csv', 'w') as f:
            f.write("parameter,value\n")
            f.write(f"arithmetic_side,{A}\n")
            f.write(f"zero_side,{Z}\n")
            f.write(f"absolute_error,{error}\n")
            f.write(f"relative_error,{relative_error if relative_error != float('inf') else 'inf'}\n")
            f.write(f"verified,{verdict}\n")
            f.write(f"tolerance_absolute,{tolerance_absolute}\n")
            f.write(f"tolerance_relative,{tolerance_relative}\n")
            f.write(f"P,{P}\n")
            f.write(f"K,{K}\n")
            f.write(f"T,{T}\n")
            f.write(f"max_zeros,{args.max_zeros}\n")
            f.write(f"frequency_hz,141.7001\n")
            f.write(f"signature,JMMB Ψ✧\n")
        
        print("📊 Results saved to data/validation_results.csv")
        
    except Exception as e:
        print(f"❌ Error during computation: {e}")
        
        # Create fallback CSV with error information for auto-evolution continuity
        os.makedirs('data', exist_ok=True)
        with open('data/validation_results.csv', 'w') as f:
            f.write("parameter,value\n")
            f.write(f"arithmetic_side,ERROR\n")
            f.write(f"zero_side,ERROR\n")
            f.write(f"absolute_error,inf\n")
            f.write(f"relative_error,inf\n")
            f.write(f"verified,ERROR\n")
            f.write(f"tolerance_absolute,0.01\n")
            f.write(f"tolerance_relative,0.05\n")
            f.write(f"P,{P}\n")
            f.write(f"K,{K}\n")
            f.write(f"T,{T}\n")
            f.write(f"max_zeros,{args.max_zeros}\n")
            f.write(f"frequency_hz,141.7001\n")
            f.write(f"signature,JMMB Ψ✧\n")
            f.write(f"error_message,{str(e)}\n")
        
        print("📊 Error information saved to data/validation_results.csv for auto-evolution continuity")
        sys.exit(1)

