"""
Corrected implementation of Riemann Hypothesis explicit formula validation
Based on the correct formulation from the notebook
"""

import mpmath as mp
import sympy as sp
from utils.mellin import truncated_gaussian, mellin_transform
import time
import os

def correct_archimedean_sum(f, sigma0=2.0, T=50, lim_u=3.0):
    """
    Corrected archimedean sum based on notebook implementation.
    Uses the correct formula with the residue correction.
    """
    print(f"  Computing corrected archimedean sum with T={T}...")
    
    def integrand(t):
        s = mp.mpc(sigma0, t)  # Use mpc instead of sigma0 + 1j * t
        return (mp.digamma(s/2) - mp.log(mp.pi)) * mellin_transform(f, s, lim_u)
    
    # Compute the main integral
    integral = mp.quad(integrand, [-T, T], maxdegree=10) / (2 * mp.pi)  # Note: no 'j'
    
    # Add the residue correction term
    residue_term = mellin_transform(f, mp.mpf(1), lim_u) / mp.mpf(1)
    
    result = integral - residue_term  # Subtract the residue
    
    print(f"    Integral part: {integral}")
    print(f"    Residue term: {residue_term}")
    print(f"    Final result: {result}")
    
    return result.real

def correct_zero_sum_from_file(f, filename, max_zeros, lim_u=3.0):
    """
    Corrected zero sum using file data.
    """
    total = mp.mpf('0')
    count = 0
    
    print(f"  Computing corrected zero sum with {max_zeros} zeros...")
    
    with open(filename) as file:
        for line in file:
            if count >= max_zeros:
                break
            
            gamma = mp.mpf(line.strip())
            # Note: Use 1j * gamma, not just gamma
            zero_contrib = mellin_transform(f, 1j * gamma, lim_u).real
            total += zero_contrib
            count += 1
            
            if count % 100 == 0:
                print(f"    Processed {count}/{max_zeros} zeros...")
    
    print(f"  Zero sum completed: {count} zeros")
    return total

def validate_corrected_formula(max_zeros=1000, max_primes=1000, precision=25):
    """Validate the corrected explicit formula."""
    
    mp.mp.dps = precision
    print(f"🔬 Running CORRECTED Riemann Hypothesis validation...")
    print(f"   Precision: {precision} digits")
    
    # Parameters based on notebook
    P = min(max_primes, 5000)
    K = 5
    sigma0 = 2.0
    T = min(50, max_zeros // 20)  # Conservative T
    lim_u = 3.0  # Match notebook
    
    print(f"   Parameters: P={P}, K={K}, T={T}, max_zeros={max_zeros}")
    
    try:
        f = truncated_gaussian
        zeros_file = 'zeros/zeros_t1e8.txt'
        
        start_time = time.time()
        
        # Compute prime sum (unchanged)
        print("Computing prime sum...")
        prime_total = mp.mpf('0')
        primes = list(sp.primerange(2, P + 1))
        print(f"  Using {len(primes)} primes...")
        
        for p in primes:
            lp = mp.log(p)
            for k in range(1, K + 1):
                prime_total += lp * f(k * lp)
        
        print(f"  Prime sum: {prime_total}")
        
        # Compute corrected archimedean sum
        print("Computing corrected archimedean sum...")
        arch_total = correct_archimedean_sum(f, sigma0, T, lim_u)
        
        A = prime_total + arch_total
        print(f"Total arithmetic side: {A}")
        
        # Compute corrected zero sum
        print("Computing corrected zero sum...")
        Z = correct_zero_sum_from_file(f, zeros_file, max_zeros, lim_u)
        print(f"Total zero side: {Z}")
        
        # Calculate results
        error = abs(A - Z)
        rel_error = error / abs(A) if abs(A) > 0 else float('inf')
        elapsed = time.time() - start_time
        
        print(f"\n✅ Computation completed in {elapsed:.2f}s!")
        print(f"Arithmetic side: {A}")
        print(f"Zero side:       {Z}")
        print(f"Error:           {error}")
        if abs(A) > 0:
            print(f"Relative error:  {rel_error}")
        
        # Check precision requirement
        target_error = 1e-6
        success = error <= target_error
        if success:
            print(f"🎯 SUCCESS: Error {float(error):.2e} ≤ {target_error:.0e} (target achieved)")
        else:
            print(f"⚠️  WARNING: Error {float(error):.2e} > {target_error:.0e} (target not met)")
        
        # Save results
        save_corrected_results(A, Z, P, K, T, max_zeros, success, target_error, precision, elapsed)
        
        return success
        
    except Exception as e:
        print(f"❌ Error during computation: {e}")
        import traceback
        traceback.print_exc()
        return False

def save_corrected_results(A, Z, P, K, T, max_zeros, precision_met, target_error, precision_used, computation_time):
    """Save corrected validation results."""
    error = abs(A - Z)
    rel_error = error / abs(A) if abs(A) > 0 else float('inf')
    
    os.makedirs('data', exist_ok=True)
    with open('data/corrected_validation_results.csv', 'w') as f:
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
    
    print("📊 Results saved to data/corrected_validation_results.csv")

if __name__ == "__main__":
    import argparse
    
    parser = argparse.ArgumentParser(description='Corrected Riemann Hypothesis explicit formula validation')
    parser.add_argument('--max_primes', type=int, default=1000, help='Maximum prime P to use')
    parser.add_argument('--max_zeros', type=int, default=1000, help='Maximum number of zeros to use')
    parser.add_argument('--precision', type=int, default=25, help='Decimal precision to use')
    
    args = parser.parse_args()
    
    success = validate_corrected_formula(
        max_zeros=args.max_zeros,
        max_primes=args.max_primes,
        precision=args.precision
    )
    
    if not success:
        print("❌ Validation failed to meet precision requirements")
        exit(1)
    else:
        print("✅ Validation completed successfully")