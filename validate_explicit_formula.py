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

def validate_riemann_hypothesis_notebook(test_function_name, P=1000, K=50, N=1000):
    """
    Validate the Riemann Hypothesis using the notebook's working method.
    
    Args:
        test_function_name: Name of test function ('f1', 'f2', 'f3')
        P: Number of primes to use
        K: Maximum prime powers
        N: Number of zeros to use
    
    Returns:
        Dictionary with validation results
    """
    from utils.test_functions import get_test_function
    
    print(f"🔬 Validating with notebook method: {test_function_name}")
    print(f"   Parameters: P={P}, K={K}, N={N}")
    
    # Get test function and its limit
    phi, lim = get_test_function(test_function_name)
    
    def fhat(s, limit):
        """Compute f̂(s) = ∫ f(u) * exp(s * u) du"""
        return mp.quad(lambda u: phi(u) * mp.exp(s * u), [-limit, limit], maxdegree=10)
    
    def prime_sum_notebook(f, P=1000, K=50):
        """Prime sum as in notebook."""
        s = mp.mpf(0)
        primes = list(sp.primerange(2, 7919))[:P]  # Use first P primes
        for p in primes:
            lp = mp.log(p)
            for k in range(1, K+1):
                s += lp * f(k * lp)
        return s
    
    def A_infty_notebook(f, sigma0=2.0, lim=3, T=20):  # Reduce T from 50 to 20
        """A_infinity as in notebook."""
        print(f"    Computing A_infty with T={T}, lim={lim}")
        
        def integrand(t):
            s = mp.mpc(sigma0, t)
            return (mp.digamma(s/2) - mp.log(mp.pi)) * fhat(s, lim)
        
        # Use lower precision for speed
        old_dps = mp.mp.dps
        mp.mp.dps = 15
        try:
            integ = mp.quad(integrand, [-T, T], maxdegree=6) / (2 * mp.pi)  # Reduce maxdegree
            res1 = fhat(mp.mpf(1), lim) / mp.mpf(1)
            result = integ - res1
        finally:
            mp.mp.dps = old_dps
        
        print(f"    A_infty: integral={integ}, correction={res1}, result={result}")
        return result
    
    def zero_sum_notebook(f, N=2000, lim=3):
        """Zero sum as in notebook (corrected)."""
        s = mp.mpf(0)
        for n in range(1, N+1):
            if n % 100 == 0:
                print(f"    Processing zero {n}/{N}")
            rho = mp.zetazero(n)
            # Use i*gamma instead of just gamma for the Mellin transform
            s += fhat(1j * mp.im(rho), lim).real
        return s
    
    # Compute all terms
    print("Computing prime sum...")
    ps = prime_sum_notebook(phi, P, K)
    
    print("Computing A_infty...")
    ain = A_infty_notebook(phi, lim=lim, T=50)
    
    print("Computing zero sum...")
    zs = zero_sum_notebook(phi, N=N, lim=lim)
    
    # Total arithmetic side
    tot = ps + ain
    
    # Compute errors
    error_abs = abs(tot - zs)
    error_rel = error_abs / abs(tot) if abs(tot) > 0 else float('inf')
    
    return {
        'arithmetic_side': tot,
        'prime_sum': ps,
        'archimedean_term': ain,
        'zero_side': zs,
        'error_abs': error_abs,
        'error_rel': error_rel,
        'function': test_function_name,
        'P': P,
        'K': K,
        'N': N,
        'lim': lim
    }


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
    import sympy as sp  # Add this import for prime generation
    
    parser = argparse.ArgumentParser(description='Validate Riemann Hypothesis explicit formula')
    parser.add_argument('--function', choices=['f1', 'f2', 'f3', 'gaussian', 'truncated'], default='f1',
                        help='Test function to use')
    parser.add_argument('--method', choices=['notebook', 'vonmangoldt'], default='notebook',
                        help='Method to use: notebook (working) or vonmangoldt (corrected)')
    parser.add_argument('--P', type=int, default=1000, 
                        help='Number of primes to use')
    parser.add_argument('--K', type=int, default=50,
                        help='Maximum prime power')
    parser.add_argument('--N', '--max_zeros', type=int, default=1000, 
                        help='Maximum number of zeros to use')
    parser.add_argument('--X', type=float, default=8.0, 
                        help='Parameter X (n_max = exp(X)) for von Mangoldt method')
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
            T = max(1, min(100, args.N // 10))
            lim_u = 3.0
            
            f = truncated_gaussian
            
            print("Computing arithmetic side (legacy)...")
            prime_part = prime_sum(f, P, K)
            arch_part = archimedean_sum(f, sigma0, T, lim_u)
            A = prime_part + arch_part
            
            print("Computing zero side (legacy)...")
            Z = zero_sum_limited(f, 'zeros/zeros_t1e8.txt', args.N, lim_u)
            
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
                'max_zeros': args.N
            }
            
        elif args.method == 'notebook':
            # Use the working notebook method
            if args.function in ['f1', 'f2', 'f3']:
                results = validate_riemann_hypothesis_notebook(args.function, args.P, args.K, args.N)
            else:
                print(f"❌ Function {args.function} not available for notebook method. Use f1, f2, or f3.")
                sys.exit(1)
                
        else:
            # Use new corrected implementation with von Mangoldt
            if args.function == 'gaussian':
                test_func = phi_gaussian
            elif args.function in ['f1', 'f2', 'f3']:
                from utils.test_functions import get_test_function
                test_func, _ = get_test_function(args.function)
            else:
                test_func = truncated_gaussian
                
            results = validate_riemann_hypothesis(
                test_func, args.X, args.N, args.alpha
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
            f.write(f"method,{args.method if not args.legacy else 'legacy'}\n")
            
            if args.method == 'notebook' and not args.legacy:
                f.write(f"function,{results['function']}\n")
                f.write(f"P,{results['P']}\n")
                f.write(f"K,{results['K']}\n")
                f.write(f"N,{results['N']}\n")
                f.write(f"lim,{results['lim']}\n")
                f.write(f"prime_sum,{results['prime_sum']}\n")
                f.write(f"archimedean_term,{results['archimedean_term']}\n")
            elif not args.legacy:
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
                
            f.write(f"max_zeros,{results.get('max_zeros', args.N)}\n")
        
        print("📊 Results saved to data/validation_results.csv")
        
        # Exit with error code if validation failed
        if not validation_passed:
            sys.exit(1)
        
    except Exception as e:
        print(f"❌ Error during computation: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)

