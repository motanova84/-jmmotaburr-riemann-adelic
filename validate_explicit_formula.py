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

import argparse
import csv
import os
import mpmath as mp
import sympy as sp
from datetime import datetime
from utils.mellin import truncated_gaussian, mellin_transform

mp.mp.dps = 50

# Default parameters (can be overridden by command line)
DEFAULT_P = 1000          # Máximo primo (as specified in problem statement)
DEFAULT_K = 5             # Potencias máximas por primo
DEFAULT_SIGMA0 = 2.0
DEFAULT_T = 50            # As specified in problem statement
DEFAULT_LIM_U = 5.0

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

def f1(u):
    """Test function f1: truncated Gaussian with smaller support"""
    return mp.exp(-u**2/2) if abs(u) <= 3 else mp.mpf(0)

def f2(u): 
    """Test function f2: different Gaussian truncation"""
    return mp.exp(-u**2) if abs(u) <= 2 else mp.mpf(0)

def f3(u):
    """Test function f3: polynomial with compact support"""
    return (1 - u**2/4)**2 if abs(u) <= 2 else mp.mpf(0)

def save_results_to_csv(results, filename="data/validation_results.csv"):
    """Save validation results to CSV file."""
    os.makedirs(os.path.dirname(filename), exist_ok=True)
    
    with open(filename, 'w', newline='') as csvfile:
        writer = csv.writer(csvfile)
        
        # Header
        writer.writerow(['timestamp', 'function', 'P', 'K', 'T', 'sigma0', 'lim_u',
                        'prime_sum', 'archimedean_sum', 'arithmetic_total', 'zero_sum',
                        'absolute_error', 'relative_error', 'passes_tolerance'])
        
        # Data rows
        for result in results:
            writer.writerow([
                result['timestamp'],
                result['function'],
                result['P'],
                result['K'],
                result['T'],
                result['sigma0'],
                result['lim_u'],
                result['prime_sum'],
                result['archimedean_sum'],
                result['arithmetic_total'],
                result['zero_sum'],
                result['absolute_error'],
                result['relative_error'],
                result['passes_tolerance']
            ])
    
    print(f"Results saved to: {filename}")

def run_validation(f, function_name, P, K, sigma0, T, lim_u, tolerance=1e-6):
    """Run validation for a single test function."""
    print(f"\n{'='*60}")
    print(f"VALIDATING: {function_name}")
    print(f"Parameters: P={P}, K={K}, T={T}, σ₀={sigma0}")
    print(f"{'='*60}")
    
    # Calculate components
    p_sum = prime_sum(f, P, K)
    a_sum = archimedean_sum(f, sigma0, T, lim_u)
    arithmetic_total = p_sum + a_sum
    z_sum = zero_sum(f, 'zeros/zeros_t1e8.txt', lim_u)
    
    # Error analysis
    absolute_error = abs(arithmetic_total - z_sum)
    relative_error = absolute_error / abs(arithmetic_total) if arithmetic_total != 0 else float('inf')
    passes_tolerance = absolute_error <= tolerance
    
    # Display results
    print(f"Prime sum:          {p_sum}")
    print(f"Archimedean sum:    {a_sum}")
    print(f"Arithmetic total:   {arithmetic_total}")
    print(f"Zero sum:           {z_sum}")
    print(f"Absolute error:     {absolute_error:.2e}")
    print(f"Relative error:     {relative_error:.2e}")
    print(f"Tolerance (1e-6):   {'✓ PASS' if passes_tolerance else '✗ FAIL'}")
    
    return {
        'timestamp': datetime.now().isoformat(),
        'function': function_name,
        'P': P,
        'K': K,
        'T': T,
        'sigma0': sigma0,
        'lim_u': lim_u,
        'prime_sum': float(p_sum),
        'archimedean_sum': float(a_sum),
        'arithmetic_total': float(arithmetic_total),
        'zero_sum': float(z_sum),
        'absolute_error': float(absolute_error),
        'relative_error': float(relative_error),
        'passes_tolerance': passes_tolerance
    }

def main():
    parser = argparse.ArgumentParser(description='Validate Riemann Hypothesis explicit formula')
    parser.add_argument('--P', type=int, default=DEFAULT_P,
                       help=f'Maximum prime (default: {DEFAULT_P})')
    parser.add_argument('--K', type=int, default=DEFAULT_K,
                       help=f'Maximum prime powers (default: {DEFAULT_K})')
    parser.add_argument('--T', type=float, default=DEFAULT_T,
                       help=f'Integration limit (default: {DEFAULT_T})')
    parser.add_argument('--sigma0', type=float, default=DEFAULT_SIGMA0,
                       help=f'Sigma parameter (default: {DEFAULT_SIGMA0})')
    parser.add_argument('--lim-u', type=float, default=DEFAULT_LIM_U,
                       help=f'U integration limit (default: {DEFAULT_LIM_U})')
    parser.add_argument('--tolerance', type=float, default=1e-6,
                       help='Error tolerance (default: 1e-6)')
    parser.add_argument('--output', default='data/validation_results.csv',
                       help='Output CSV file')
    parser.add_argument('--functions', nargs='+', default=['truncated_gaussian'],
                       choices=['truncated_gaussian', 'f1', 'f2', 'f3'],
                       help='Test functions to validate')
    
    args = parser.parse_args()
    
    print("RIEMANN HYPOTHESIS EXPLICIT FORMULA VALIDATION")
    print("=" * 60)
    print(f"Reproducibility parameters: δ≤{args.tolerance}, P={args.P}, T={args.T}")
    print("=" * 60)
    
    results = []
    
    # Test function mapping
    functions = {
        'truncated_gaussian': (truncated_gaussian, 'Truncated Gaussian'),
        'f1': (f1, 'F1 (Gaussian, support 3)'),
        'f2': (f2, 'F2 (Gaussian^2, support 2)'),  
        'f3': (f3, 'F3 (Polynomial, support 2)')
    }
    
    for func_name in args.functions:
        if func_name in functions:
            f, display_name = functions[func_name]
            try:
                result = run_validation(f, display_name, args.P, args.K, 
                                      args.sigma0, args.T, args.lim_u, args.tolerance)
                results.append(result)
            except Exception as e:
                print(f"ERROR validating {display_name}: {e}")
    
    # Save results
    if results:
        save_results_to_csv(results, args.output)
        
        # Summary
        print(f"\n{'='*60}")
        print("VALIDATION SUMMARY")
        print(f"{'='*60}")
        passed = sum(1 for r in results if r['passes_tolerance'])
        total = len(results)
        print(f"Passed: {passed}/{total}")
        print(f"All tests passed: {'✓ YES' if passed == total else '✗ NO'}")
        
        if passed == total:
            print("\n🎉 All validations PASSED - explicit formula holds within tolerance!")
            print("This supports the theoretical framework.")
        else:
            print("\n⚠️  Some validations FAILED - review parameters or implementation.")
    else:
        print("No results to save.")

if __name__ == "__main__":
    main()

