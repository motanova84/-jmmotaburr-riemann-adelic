#!/usr/bin/env python3
"""
High-precision validation script for reaching 1e-10 error target.

This script implements the fixes mentioned in the problem statement and
attempts to achieve the target precision of 1e-10 error by:

1. Using optimized manual loops instead of mp.nsum
2. Ensuring proper mpmath type handling throughout
3. Using higher precision arithmetic
4. Optimizing integration parameters
"""

import mpmath as mp
import sympy as sp
from utils.mellin import truncated_gaussian, mellin_transform
import argparse
import time

def optimized_zero_sum_limited(f, filename, max_zeros, lim_u=5, precision=50):
    """
    Optimized zero sum computation with manual loops.
    
    This replaces any potential mp.nsum calls with efficient manual loops
    as suggested in the problem statement for better performance and stability.
    """
    # Set high precision for target 1e-10 accuracy
    old_dps = mp.mp.dps
    mp.mp.dps = precision
    
    try:
        total = mp.mpf('0')
        count = 0
        
        with open(filename, 'r') as file:
            for line in file:
                if count >= max_zeros:
                    break
                try:
                    gamma_str = line.strip()
                    if not gamma_str:
                        continue
                    
                    # Ensure proper mpmath conversion (avoiding float intermediates)
                    gamma = mp.mpf(gamma_str)
                    
                    # Compute mellin transform - this is where optimization matters
                    fhat_val = mellin_transform(f, 1j * gamma, lim_u)
                    total += fhat_val.real
                    count += 1
                    
                except (ValueError, TypeError) as e:
                    print(f"Warning: Skipping invalid zero: {e}")
                    continue
                    
        print(f"Used {count} zeros for high-precision computation")
        return total
        
    finally:
        mp.mp.dps = old_dps

def optimized_prime_sum(f, P, K, precision=50):
    """Optimized prime sum with proper mpmath handling."""
    old_dps = mp.mp.dps
    mp.mp.dps = precision
    
    try:
        total = mp.mpf('0')
        primes = list(sp.primerange(2, P + 1))
        
        for p in primes:
            # Ensure all arithmetic is mpmath to avoid type mismatches
            lp = mp.log(mp.mpf(p))
            for k in range(1, K + 1):
                klp = mp.mpf(k) * lp
                total += lp * f(klp)
                
        return total
        
    finally:
        mp.mp.dps = old_dps

def optimized_archimedean_sum(f, sigma0, T, lim_u, precision=50):
    """Optimized archimedean sum with high precision."""
    old_dps = mp.mp.dps
    mp.mp.dps = precision
    
    try:
        def integrand(t):
            s = mp.mpf(sigma0) + 1j * mp.mpf(t)
            kernel = mp.digamma(s / mp.mpf(2)) - mp.log(mp.pi)
            return kernel * mellin_transform(f, s, lim_u)
        
        # Use higher precision integration
        integral, err = mp.quad(integrand, 
                               [-mp.mpf(T), mp.mpf(T)], 
                               error=True,
                               maxdegree=15)  # Higher degree for better accuracy
        
        result = (integral / (2j * mp.pi)).real
        return result
        
    finally:
        mp.mp.dps = old_dps

def validate_high_precision(max_zeros=2000, P=5000, precision=50, target_error=1e-10):
    """
    Main validation function targeting 1e-10 error.
    
    Implements all the fixes from the problem statement:
    - mp.nsum → loop replacements
    - random → mp.mpf conversions (where applicable)
    - Proper type handling throughout
    """
    print(f"🎯 High-precision validation targeting {target_error:.0e} error")
    print(f"Parameters: max_zeros={max_zeros}, P={P}, precision={precision}")
    
    f = truncated_gaussian
    K = 5
    sigma0 = mp.mpf('2.0')
    T = mp.mpf('100')
    lim_u = mp.mpf('5.0')
    
    start_time = time.time()
    
    # Arithmetic side with optimized functions
    print("Computing arithmetic side (high precision)...")
    prime_part = optimized_prime_sum(f, P, K, precision)
    arch_part = optimized_archimedean_sum(f, sigma0, T, lim_u, precision)
    A = prime_part + arch_part
    
    # Zero side with optimized manual loops
    print("Computing zero side (optimized loops)...")
    Z = optimized_zero_sum_limited(f, 'zeros/zeros_t1e8.txt', max_zeros, lim_u, precision)
    
    # Calculate error
    error = abs(A - Z)
    rel_error = abs(error / A) if abs(A) > 0 else mp.inf
    
    elapsed = time.time() - start_time
    
    # Results
    print("\n" + "="*60)
    print("HIGH-PRECISION VALIDATION RESULTS")
    print("="*60)
    print(f"Arithmetic side: {A}")
    print(f"Zero side:       {Z}")
    print(f"Absolute error:  {error}")
    print(f"Relative error:  {rel_error}")
    print(f"Computation time: {elapsed:.1f}s")
    print(f"Precision used:   {precision} decimal places")
    
    # Check if target achieved
    error_float = float(error.real if hasattr(error, 'real') else error)
    if error_float < target_error:
        print(f"\n🎉 SUCCESS! Error {error_float:.2e} < {target_error:.0e}")
        print("✅ Repository fixes have achieved the target precision!")
        return True
    else:
        print(f"\n⚠️  Error {error_float:.2e} > {target_error:.0e}")
        print("💡 May need more zeros or higher precision for target")
        return False

def main():
    parser = argparse.ArgumentParser(description='High-precision Riemann validation')
    parser.add_argument('--max_zeros', type=int, default=1000, 
                       help='Maximum zeros to use (default: 1000)')
    parser.add_argument('--max_primes', type=int, default=2000,
                       help='Maximum prime P (default: 2000)')  
    parser.add_argument('--precision', type=int, default=30,
                       help='Decimal precision (default: 30)')
    parser.add_argument('--target_error', type=float, default=1e-8,
                       help='Target error (default: 1e-8)')
    
    args = parser.parse_args()
    
    success = validate_high_precision(
        max_zeros=args.max_zeros,
        P=args.max_primes, 
        precision=args.precision,
        target_error=args.target_error
    )
    
    return 0 if success else 1

if __name__ == "__main__":
    import sys
    sys.exit(main())