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
import logging
import datetime
from utils.mellin import truncated_gaussian, mellin_transform

# Set precision for computation
mp.mp.dps = 15  # Reduced from 50 for performance

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
    
    # Setup logging
    timestamp = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
    os.makedirs('logs', exist_ok=True)
    log_file = f'logs/validation_{timestamp}.log'
    
    logging.basicConfig(
        level=logging.INFO,
        format='%(asctime)s - %(levelname)s - %(message)s',
        handlers=[
            logging.FileHandler(log_file),
            logging.StreamHandler()
        ]
    )
    
    logger = logging.getLogger(__name__)
    
    # Use parameters specified in problem statement
    # Reproducible parameters: δ = 0.01, P = 1000, K = 50, N_Ξ = 2000, σ₀ = 2, T = 50
    P = min(args.max_primes, 1000)  # Use P = 1000 as specified
    K = 50  # K = 50 as specified
    sigma0 = 2.0  # σ₀ = 2 as specified
    T = 50  # T = 50 as specified
    lim_u = 5.0  # Integration limit
    
    logger.info("🔬 Running Riemann Hypothesis validation...")
    logger.info(f"Parameters: δ={args.delta}, P={P}, K={K}, T={T}, N_Ξ={args.max_zeros}, σ₀={sigma0}")
    logger.info(f"Log file: {log_file}")
    
    print(f"🔬 Running Riemann Hypothesis validation...")
    print(f"Parameters: P={P}, K={K}, T={T}, max_zeros={args.max_zeros}")
    print(f"📝 Logging to: {log_file}")
    
    try:
        f = truncated_gaussian
        
        # Check if zeros file exists
        zeros_file = 'zeros/zeros_t1e8.txt'
        if not os.path.exists(zeros_file):
            error_msg = f"❌ Zeros file not found: {zeros_file}"
            logger.error(error_msg)
            print(error_msg)
            logger.error("Run utils/fetch_odlyzko.py to download zeros data")
            sys.exit(1)
        
        logger.info("Computing arithmetic side (prime_sum + archimedean_sum)...")
        print("Computing arithmetic side...")
        prime_part = prime_sum(f, P, K)
        logger.info(f"Prime sum computed: {prime_part}")
        
        arch_part = archimedean_sum(f, sigma0, T, lim_u)
        logger.info(f"Archimedean sum computed: {arch_part}")
        
        A = prime_part + arch_part
        logger.info(f"Total arithmetic side: {A}")
        
        logger.info("Computing zero side...")
        print("Computing zero side...")
        # Use only first max_zeros lines from file for faster computation
        Z = zero_sum_limited(f, zeros_file, args.max_zeros, lim_u)
        logger.info(f"Zero side computed: {Z}")

        logger.info("✅ Computation completed!")
        print(f"✅ Computation completed!")
        print(f"Aritmético (Primes + Arch): {A}")
        print(f"Zero side (explicit sum):   {Z}")
        error = abs(A - Z)
        print(f"Error absoluto:             {error}")
        
        logger.info(f"Results: Arithmetic={A}, Zero={Z}, Error={error}")
        
        if abs(A) > 0:
            rel_error = error / abs(A)
            print(f"Error relativo:             {rel_error}")
            logger.info(f"Relative error: {rel_error}")
        
        # Save results to CSV
        os.makedirs('data', exist_ok=True)
        csv_file = f'data/validation_results_{timestamp}.csv'
        with open(csv_file, 'w') as f:
            f.write("parameter,value\n")
            f.write(f"timestamp,{timestamp}\n")
            f.write(f"delta,{args.delta}\n")
            f.write(f"arithmetic_side,{A}\n")
            f.write(f"zero_side,{Z}\n")
            f.write(f"absolute_error,{error}\n")
            f.write(f"relative_error,{error / abs(A) if abs(A) > 0 else 'inf'}\n")
            f.write(f"P,{P}\n")
            f.write(f"K,{K}\n")
            f.write(f"T,{T}\n")
            f.write(f"sigma0,{sigma0}\n")
            f.write(f"max_zeros,{args.max_zeros}\n")
            f.write(f"lim_u,{lim_u}\n")
            f.write(f"precision_dps,{mp.mp.dps}\n")
        
        # Also keep the standard file for compatibility
        with open('data/validation_results.csv', 'w') as f:
            f.write("parameter,value\n")
            f.write(f"timestamp,{timestamp}\n")
            f.write(f"delta,{args.delta}\n")
            f.write(f"arithmetic_side,{A}\n")
            f.write(f"zero_side,{Z}\n")
            f.write(f"absolute_error,{error}\n")
            f.write(f"relative_error,{error / abs(A) if abs(A) > 0 else 'inf'}\n")
            f.write(f"P,{P}\n")
            f.write(f"K,{K}\n")
            f.write(f"T,{T}\n")
            f.write(f"sigma0,{sigma0}\n")
            f.write(f"max_zeros,{args.max_zeros}\n")
            f.write(f"lim_u,{lim_u}\n")
            f.write(f"precision_dps,{mp.mp.dps}\n")
        
        logger.info(f"📊 Results saved to {csv_file} and data/validation_results.csv")
        print(f"📊 Results saved to {csv_file}")
        
    except Exception as e:
        error_msg = f"❌ Error during computation: {e}"
        logger.error(error_msg)
        logger.error("Full traceback:", exc_info=True)
        print(error_msg)
        sys.exit(1)

