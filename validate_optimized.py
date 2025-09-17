"""
Enhanced numerical validation for Riemann Hypothesis explicit formula
with optimized precision-performance balance for error ≤10^{-6}
"""

import mpmath as mp
import sympy as sp
from utils.mellin import truncated_gaussian, mellin_transform
import time
import os

# Progressive precision strategy
def set_precision_for_target(target_zeros):
    """Set appropriate precision based on number of zeros."""
    if target_zeros <= 1000:
        return 20  # Fast computation for small tests
    elif target_zeros <= 10000:
        return 25  # Balanced for medium tests
    elif target_zeros <= 100000:
        return 30  # Higher precision for large tests
    else:
        return 35  # Maximum precision for very large tests

def prime_sum_optimized(f, P, K):
    """Optimized prime sum computation."""
    total = mp.mpf('0')
    print(f"  Computing prime sum with P={P}, K={K}...")
    
    # Generate primes in chunks for better memory efficiency
    chunk_size = min(1000, P // 10)
    primes_processed = 0
    
    for start in range(2, P + 1, chunk_size):
        end = min(start + chunk_size, P + 1)
        primes = list(sp.primerange(start, end))
        
        for p in primes:
            lp = mp.log(p)
            for k in range(1, K + 1):
                total += lp * f(k * lp)
        
        primes_processed += len(primes)
        if primes_processed % 100 == 0:
            print(f"    Processed {primes_processed} primes...")
    
    return total

def archimedean_sum_optimized(f, sigma0, T, lim_u):
    """Optimized archimedean contribution computation."""
    print(f"  Computing archimedean sum with T={T}...")
    
    def integrand(t):
        s = sigma0 + 1j * t
        kernel = mp.digamma(s / 2) - mp.log(mp.pi)
        return kernel * mellin_transform(f, s, lim_u)
    
    # Use adaptive quadrature with error control
    start_time = time.time()
    integral, err = mp.quad(integrand, [-T, T], error=True, maxdegree=12)
    computation_time = time.time() - start_time
    
    result = (integral / (2j * mp.pi)).real
    
    print(f"    Archimedean computation: {float(computation_time):.2f}s, error estimate: {float(abs(err)):.2e}")
    
    # Check convergence
    if abs(err) > 1e-8:
        print(f"    Warning: Archimedean sum may not have converged, error estimate: {err}")
    
    return result

def zero_sum_optimized(f, filename, max_zeros, lim_u=4.0):
    """Optimized zero sum computation with progress tracking."""
    total = mp.mpf('0')
    count = 0
    
    print(f"  Computing zero sum with {max_zeros} zeros...")
    start_time = time.time()
    
    with open(filename) as file:
        for line in file:
            if count >= max_zeros:
                break
            
            gamma = mp.mpf(line.strip())
            total += mellin_transform(f, 1j * gamma, lim_u).real
            count += 1
            
            # Progress reporting
            if count % 100 == 0:
                elapsed = time.time() - start_time
                rate = count / elapsed if elapsed > 0 else 0
                eta = (max_zeros - count) / rate if rate > 0 else 0
                print(f"    Processed {count}/{max_zeros} zeros ({rate:.1f} zeros/s, ETA: {eta:.1f}s)")
    
    elapsed = time.time() - start_time
    print(f"  Zero sum completed: {count} zeros in {elapsed:.2f}s")
    return total

def validate_formula_optimized(max_zeros=2000, max_primes=1000, target_error=1e-6):
    """Main validation function with optimized computation."""
    
    # Set precision based on problem size
    precision = set_precision_for_target(max_zeros)
    mp.mp.dps = precision
    print(f"🔬 Running optimized Riemann Hypothesis validation...")
    print(f"   Precision: {precision} digits")
    
    # Optimized parameters
    P = min(max_primes, 10000)
    K = 5  # Standard value
    sigma0 = 2.0
    T = max(20, min(100, max_zeros // 50))  # Adaptive T
    lim_u = 4.0
    
    print(f"   Parameters: P={P}, K={K}, T={T}, max_zeros={max_zeros}")
    
    try:
        f = truncated_gaussian
        
        # Check zeros file
        zeros_file = 'zeros/zeros_t1e8.txt'
        if not os.path.exists(zeros_file):
            print(f"❌ Zeros file not found: {zeros_file}")
            return False
        
        total_start = time.time()
        
        # Compute arithmetic side
        print("Computing arithmetic side...")
        prime_part = prime_sum_optimized(f, P, K)
        arch_part = archimedean_sum_optimized(f, sigma0, T, lim_u)
        A = prime_part + arch_part
        
        # Compute zero side
        print("Computing zero side...")
        Z = zero_sum_optimized(f, zeros_file, max_zeros, lim_u)
        
        total_time = time.time() - total_start
        
        # Validate results
        error = abs(A - Z)
        rel_error = error / abs(A) if abs(A) > 0 else float('inf')
        
        print(f"\n✅ Computation completed in {total_time:.2f}s!")
        print(f"Aritmético (Primes + Arch): {A}")
        print(f"Zero side (explicit sum):   {Z}")
        print(f"Error absoluto:             {error}")
        if abs(A) > 0:
            print(f"Error relativo:             {rel_error}")
        
        # Check precision requirement
        success = error <= target_error
        if success:
            print(f"🎯 SUCCESS: Error {float(error):.2e} ≤ {target_error:.0e} (target achieved)")
        else:
            print(f"⚠️  WARNING: Error {float(error):.2e} > {target_error:.0e} (target not met)")
        
        # Save results
        save_results_enhanced(A, Z, P, K, T, max_zeros, success, target_error, precision, total_time)
        
        return success
        
    except Exception as e:
        print(f"❌ Error during computation: {e}")
        return False

def save_results_enhanced(A, Z, P, K, T, max_zeros, precision_met, target_error, precision_used, computation_time):
    """Save enhanced validation results."""
    error = abs(A - Z)
    rel_error = error / abs(A) if abs(A) > 0 else float('inf')
    
    os.makedirs('data', exist_ok=True)
    with open('data/validation_results.csv', 'w') as f:
        f.write("parameter,value\n")
        f.write(f"arithmetic_side,{A}\n")
        f.write(f"zero_side,{Z}\n")
        f.write(f"absolute_error,{error}\n")
        f.write(f"relative_error,{rel_error}\n")
        f.write(f"target_error,{target_error}\n")
        f.write(f"precision_met,{precision_met}\n")
        f.write(f"precision_used,{precision_used}\n")
        f.write(f"computation_time,{computation_time}\n")
        f.write(f"P,{P}\n")
        f.write(f"K,{K}\n")
        f.write(f"T,{T}\n")
        f.write(f"max_zeros,{max_zeros}\n")
    
    print("📊 Results saved to data/validation_results.csv")

if __name__ == "__main__":
    import argparse
    
    parser = argparse.ArgumentParser(description='Optimized Riemann Hypothesis explicit formula validation')
    parser.add_argument('--max_primes', type=int, default=1000, help='Maximum prime P to use')
    parser.add_argument('--max_zeros', type=int, default=2000, help='Maximum number of zeros to use')
    parser.add_argument('--target_error', type=float, default=1e-6, help='Target error threshold')
    
    args = parser.parse_args()
    
    success = validate_formula_optimized(
        max_zeros=args.max_zeros,
        max_primes=args.max_primes,
        target_error=args.target_error
    )
    
    if not success:
        print("❌ Validation failed to meet precision requirements")
        exit(1)
    else:
        print("✅ Validation completed successfully")