"""
Riemann Hypothesis Validation using Explicit Formula

This script validates the explicit formula for the Riemann zeta function
by comparing the arithmetic side (von Mangoldt sum + Archimedean term)
with the zero side (sum over non-trivial zeros).

The corrected implementation uses:
- von Mangoldt function Λ(n) sum over all integers n ≥ 2
- Proper Archimedean term A_inf using Γ'/Γ ratios
- Well-defined Gaussian test functions
- Enhanced validation criteria

Target: Relative error < 1e-2
"""

import mpmath as mp
import sys
import os
import argparse
from utils.arithmetic_side import arithmetic_side
from utils.archimedean_term import archimedean_term_mellin
from utils.zero_side import zero_sum_from_file
from utils.test_functions import phi_gaussian, truncated_gaussian

# Set precision for computation
mp.mp.dps = 25  # Increased for better accuracy

def validate_riemann_hypothesis(test_function, X=8.0, max_zeros=1000, alpha=1.0):
    """
    Validate the Riemann Hypothesis using the explicit formula.
    
    Args:
        test_function: Test function φ(u) to use
        X: Parameter controlling n_max = exp(X)
        max_zeros: Maximum number of zeros to use
        alpha: Scale parameter for test function
    
    Returns:
        Dictionary with validation results
    """
    print(f"🔬 Validating with X={X}, max_zeros={max_zeros}, alpha={alpha}")
    
    # Create test function with alpha parameter
    if test_function == phi_gaussian:
        phi = lambda u: phi_gaussian(u, alpha)
    else:
        phi = test_function
    
    # Check if zeros file exists
    zeros_file = 'zeros/zeros_t1e8.txt'
    if not os.path.exists(zeros_file):
        print(f"❌ Zeros file not found: {zeros_file}")
        sys.exit(1)
    
    # Compute arithmetic side (von Mangoldt sum)
    print("Computing arithmetic side (von Mangoldt sum)...")
    arith_sum = arithmetic_side(phi, X)
    
    # Compute Archimedean term
    print("Computing Archimedean term...")
    arch_term = archimedean_term_mellin(phi, sigma0=2.0, T=50, lim_u=5.0)
    
    # Total arithmetic side
    A = arith_sum + arch_term
    
    # Compute zero side (multiply by 2 since we have only positive zeros)
    print("Computing zero side...")
    Z = 2 * zero_sum_from_file(phi, zeros_file, max_zeros, lim_u=5.0)
    
    # Compute errors
    error_abs = abs(A - Z)
    error_rel = error_abs / abs(A) if abs(A) > 0 else float('inf')
    
    return {
        'arithmetic_side': A,
        'arith_sum': arith_sum,
        'arch_term': arch_term,
        'zero_side': Z,
        'error_abs': error_abs,
        'error_rel': error_rel,
        'X': X,
        'max_zeros': max_zeros,
        'alpha': alpha,
        'n_max': int(mp.exp(X))
    }


# Legacy functions for backward compatibility
def prime_sum(f, P, K):
    """Legacy prime sum - use arithmetic_side instead."""
    from utils.arithmetic_side import prime_sum_legacy
    return prime_sum_legacy(f, P, K)


def archimedean_sum(f, sigma0, T, lim_u):
    """Legacy archimedean sum - use archimedean_term_mellin instead."""
    return archimedean_term_mellin(f, sigma0, T, lim_u)


def zero_sum(f, filename, lim_u=5):
    """Legacy zero sum - use zero_sum_from_file instead."""
    return zero_sum_from_file(f, filename, None, lim_u)


def zero_sum_limited(f, filename, max_zeros, lim_u=5):
    """Legacy zero sum limited - use zero_sum_from_file instead."""
    return zero_sum_from_file(f, filename, max_zeros, lim_u)

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='Validate Riemann Hypothesis explicit formula')
    parser.add_argument('--function', choices=['gaussian', 'truncated'], default='gaussian',
                        help='Test function to use')
    parser.add_argument('--X', type=float, default=8.0, 
                        help='Parameter X (n_max = exp(X))')
    parser.add_argument('--max_zeros', type=int, default=1000, 
                        help='Maximum number of zeros to use')
    parser.add_argument('--alpha', type=float, default=1.0, 
                        help='Scale parameter for test function')
    parser.add_argument('--legacy', action='store_true',
                        help='Use legacy implementation for comparison')
    
    args = parser.parse_args()
    
    print("🧮 Riemann Hypothesis Validation - Corrected Implementation")
    print("=" * 60)
    
    try:
        if args.legacy:
            print("⚠️  Using legacy implementation for comparison")
            # Use reduced parameters for faster computation
            P = 1000
            K = 5
            sigma0 = 2.0
            T = max(1, min(100, args.max_zeros // 10))
            lim_u = 3.0
            
            f = truncated_gaussian
            
            print("Computing arithmetic side (legacy)...")
            prime_part = prime_sum(f, P, K)
            arch_part = archimedean_sum(f, sigma0, T, lim_u)
            A = prime_part + arch_part
            
            print("Computing zero side (legacy)...")
            Z = zero_sum_limited(f, 'zeros/zeros_t1e8.txt', args.max_zeros, lim_u)
            
            error = abs(A - Z)
            error_rel = error / abs(A) if abs(A) > 0 else float('inf')
            
            results = {
                'arithmetic_side': A,
                'zero_side': Z,
                'error_abs': error,
                'error_rel': error_rel,
                'P': P,
                'K': K,
                'T': T,
                'max_zeros': args.max_zeros
            }
        else:
            # Use new corrected implementation
            if args.function == 'gaussian':
                test_func = phi_gaussian
            else:
                test_func = truncated_gaussian
                
            results = validate_riemann_hypothesis(
                test_func, args.X, args.max_zeros, args.alpha
            )
        
        # Display results
        print(f"\n✅ Computation completed!")
        print(f"Arithmetic side:     {results['arithmetic_side']}")
        print(f"Zero side:           {results['zero_side']}")
        print(f"Absolute error:      {results['error_abs']}")
        print(f"Relative error:      {results['error_rel']}")
        
        # Check validation criterion
        error_rel_float = float(results['error_rel'])
        if error_rel_float > 1e-2:
            print(f"\n❌ Validation failed: error {error_rel_float:.2e} > 1e-2")
            validation_passed = False
        else:
            print(f"\n✅ Validation passed: error {error_rel_float:.2e} ≤ 1e-2")
            validation_passed = True
        
        # Save enhanced results to CSV
        os.makedirs('data', exist_ok=True)
        with open('data/validation_results.csv', 'w') as f:
            f.write("parameter,value\n")
            f.write(f"arithmetic_side,{results['arithmetic_side']}\n")
            f.write(f"zero_side,{results['zero_side']}\n")
            f.write(f"absolute_error,{results['error_abs']}\n")
            f.write(f"relative_error,{results['error_rel']}\n")
            f.write(f"validation_passed,{validation_passed}\n")
            
            if not args.legacy:
                f.write(f"X,{results['X']}\n")
                f.write(f"n_max,{results['n_max']}\n")
                f.write(f"alpha,{results['alpha']}\n")
                f.write(f"arith_sum,{results['arith_sum']}\n")
                f.write(f"arch_term,{results['arch_term']}\n")
                f.write(f"function,{args.function}\n")
            else:
                f.write(f"P,{results['P']}\n")
                f.write(f"K,{results['K']}\n")
                f.write(f"T,{results['T']}\n")
                
            f.write(f"max_zeros,{results['max_zeros']}\n")
        
        print("📊 Results saved to data/validation_results.csv")
        
        # Exit with error code if validation failed
        if not validation_passed:
            sys.exit(1)
        
    except Exception as e:
        print(f"❌ Error during computation: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)

