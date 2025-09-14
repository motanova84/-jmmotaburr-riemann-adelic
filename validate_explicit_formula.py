"""
Riemann Hypothesis Validation Script

This script validates an explicit formula related to the Riemann Hypothesis.

It uses:
- f1, f2, f3: compactly supported test functions
- prime_sum(f), A_infty(f), zero_sum(f)
- Comparison of arithmetic vs spectral sides.
"""

import mpmath as mp
import argparse
import csv
import os
import sys
import logging
import sympy as sp
from datetime import datetime
from utils.mellin import truncated_gaussian, mellin_transform

# Setup logging
def setup_logging(log_dir="logs"):
    """Setup logging to both file and console."""
    os.makedirs(log_dir, exist_ok=True)
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    log_file = os.path.join(log_dir, f"validation_{timestamp}.log")
    
    logging.basicConfig(
        level=logging.INFO,
        format='%(asctime)s - %(levelname)s - %(message)s',
        handlers=[
            logging.FileHandler(log_file),
            logging.StreamHandler(sys.stdout)
        ]
    )
    return log_file

# Default parameters
DEFAULT_PARAMS = {
    'P': 1000,          # Maximum prime
    'K': 50,            # Maximum powers per prime  
    'sigma0': 2.0,      # Real part for integration
    'T': 50,            # Integration limit
    'lim_u': 5.0,       # Support limit for test functions
    'delta': 0.01,      # Tolerance for validation
    'N_zeros': 2000     # Number of zeros to use
}

mp.mp.dps = 50

def prime_sum(f, P, K):
    """Calculate the prime sum contribution to the explicit formula."""
    total = mp.mpf('0')
    primes = list(sp.primerange(2, P + 1))  # Get primes up to P
    logging.info(f"Computing prime sum for {len(primes)} primes up to {P}")
    
    for p in primes:
        lp = mp.log(p)
        for k in range(1, K + 1):
            total += lp * f(k * lp)
    return total

def archimedean_sum(f, sigma0, T, lim_u):
    """Calculate the Archimedean contribution to the explicit formula."""
    logging.info(f"Computing Archimedean sum with σ₀={sigma0}, T={T}")
    
    def integrand(t):
        s = sigma0 + 1j * t
        kernel = mp.digamma(s / 2) - mp.log(mp.pi)
        return kernel * mellin_transform(f, s, lim_u)
    
    try:
        integral, err = mp.quad(integrand, [-T, T], error=True)
        logging.info(f"Integration error estimate: {err}")
        return (integral / (2j * mp.pi)).real
    except Exception as e:
        logging.error(f"Error in Archimedean sum computation: {e}")
        raise

def zero_sum(f, filename, lim_u=5):
    """Calculate the sum over nontrivial zeros."""
    total = mp.mpf('0')
    zero_count = 0
    
    if not os.path.exists(filename):
        logging.error(f"Zeros file not found: {filename}")
        raise FileNotFoundError(f"Zeros file not found: {filename}")
        
    logging.info(f"Computing zero sum using {filename}")
    
    try:
        with open(filename, 'r') as file:
            for line in file:
                line = line.strip()
                if not line or line.startswith('#'):
                    continue
                try:
                    gamma = mp.mpf(line)
                    total += mellin_transform(f, 1j * gamma, lim_u).real
                    zero_count += 1
                except ValueError as e:
                    logging.warning(f"Skipping invalid line '{line}': {e}")
                    continue
                    
        logging.info(f"Processed {zero_count} zeros from {filename}")
        return total
    except Exception as e:
        logging.error(f"Error reading zeros file: {e}")
        raise

def get_test_functions():
    """Return dictionary of available test functions."""
    def f1(u):
        return truncated_gaussian(u, a=3.0, sigma=1.0)
    
    def f2(u):
        return truncated_gaussian(u, a=2.5, sigma=0.8)
        
    def f3(u):
        # Alternative compactly supported function
        if abs(u) > 2.5:
            return mp.mpf('0')
        return (1 - (u/2.5)**2)**2
    
    return {'f1': f1, 'f2': f2, 'f3': f3}

def validate_explicit_formula(test_func, params, zeros_file):
    """Validate the explicit formula for a given test function."""
    logging.info(f"Validating explicit formula with parameters: {params}")
    
    # Calculate both sides of the explicit formula
    prime_contribution = prime_sum(test_func, params['P'], params['K'])
    arch_contribution = archimedean_sum(test_func, params['sigma0'], params['T'], params['lim_u'])
    arithmetic_side = prime_contribution + arch_contribution
    
    spectral_side = zero_sum(test_func, zeros_file, params['lim_u'])
    
    # Calculate error
    absolute_error = abs(arithmetic_side - spectral_side)
    relative_error = absolute_error / abs(arithmetic_side) if arithmetic_side != 0 else float('inf')
    
    result = {
        'prime_sum': float(prime_contribution),
        'archimedean_sum': float(arch_contribution), 
        'arithmetic_total': float(arithmetic_side),
        'spectral_sum': float(spectral_side),
        'absolute_error': float(absolute_error),
        'relative_error': float(relative_error),
        'validation_passed': relative_error < params['delta']
    }
    
    # Log results
    logging.info(f"Prime sum: {prime_contribution}")
    logging.info(f"Archimedean sum: {arch_contribution}")
    logging.info(f"Arithmetic side (total): {arithmetic_side}")
    logging.info(f"Spectral side (zeros): {spectral_side}")
    logging.info(f"Absolute error: {absolute_error}")
    logging.info(f"Relative error: {relative_error}")
    logging.info(f"Validation {'PASSED' if result['validation_passed'] else 'FAILED'}")
    
    return result

def save_results_csv(results, filename, params):
    """Save validation results to CSV file."""
    os.makedirs(os.path.dirname(filename), exist_ok=True)
    
    with open(filename, 'w', newline='') as csvfile:
        fieldnames = ['test_function', 'prime_sum', 'archimedean_sum', 'arithmetic_total', 
                     'spectral_sum', 'absolute_error', 'relative_error', 'validation_passed',
                     'P', 'K', 'sigma0', 'T', 'lim_u', 'delta', 'timestamp']
        writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
        
        writer.writeheader()
        for func_name, result in results.items():
            row = result.copy()
            row['test_function'] = func_name
            row.update(params)
            row['timestamp'] = datetime.now().isoformat()
            writer.writerow(row)
    
    logging.info(f"Results saved to {filename}")

def main():
    parser = argparse.ArgumentParser(description='Validate Riemann Hypothesis Explicit Formula')
    parser.add_argument('--delta', type=float, default=DEFAULT_PARAMS['delta'],
                       help='Validation tolerance (default: %(default)s)')
    parser.add_argument('--max_primes', type=int, default=DEFAULT_PARAMS['P'],
                       help='Maximum prime to use (default: %(default)s)')
    parser.add_argument('--max_powers', type=int, default=DEFAULT_PARAMS['K'],
                       help='Maximum powers per prime (default: %(default)s)')
    parser.add_argument('--sigma0', type=float, default=DEFAULT_PARAMS['sigma0'],
                       help='Real part for integration (default: %(default)s)')
    parser.add_argument('--T', type=float, default=DEFAULT_PARAMS['T'],
                       help='Integration limit (default: %(default)s)')
    parser.add_argument('--lim_u', type=float, default=DEFAULT_PARAMS['lim_u'],
                       help='Support limit for test functions (default: %(default)s)')
    parser.add_argument('--test_functions', nargs='+', default=['f1'],
                       choices=['f1', 'f2', 'f3'], help='Test functions to validate (default: f1)')
    parser.add_argument('--zeros_file', default='zeros/zeros_t1e8.txt',
                       help='Path to zeros file (default: %(default)s)')
    parser.add_argument('--output', default='data/validation_results.csv',
                       help='Output CSV file (default: %(default)s)')
    parser.add_argument('--log_dir', default='logs',
                       help='Directory for log files (default: %(default)s)')
    
    args = parser.parse_args()
    
    # Setup logging
    log_file = setup_logging(args.log_dir)
    logging.info("Starting Riemann Hypothesis validation")
    logging.info(f"Log file: {log_file}")
    
    # Prepare parameters
    params = {
        'P': args.max_primes,
        'K': args.max_powers,
        'sigma0': args.sigma0,
        'T': args.T,
        'lim_u': args.lim_u,
        'delta': args.delta
    }
    
    try:
        # Get test functions
        available_functions = get_test_functions()
        
        # Run validation for each requested test function
        results = {}
        for func_name in args.test_functions:
            if func_name not in available_functions:
                logging.error(f"Unknown test function: {func_name}")
                continue
                
            logging.info(f"Validating with test function: {func_name}")
            test_func = available_functions[func_name]
            result = validate_explicit_formula(test_func, params, args.zeros_file)
            results[func_name] = result
        
        # Save results
        if results:
            save_results_csv(results, args.output, params)
            
            # Print summary
            print("\n" + "="*60)
            print("VALIDATION SUMMARY")
            print("="*60)
            for func_name, result in results.items():
                status = "PASS" if result['validation_passed'] else "FAIL"
                print(f"{func_name}: {status} (relative error: {result['relative_error']:.2e})")
            print("="*60)
            
            # Exit with error code if any validation failed
            if not all(r['validation_passed'] for r in results.values()):
                logging.error("Some validations failed!")
                sys.exit(1)
            else:
                logging.info("All validations passed!")
        else:
            logging.error("No valid results obtained")
            sys.exit(1)
            
    except Exception as e:
        logging.error(f"Validation failed with error: {e}")
        sys.exit(1)


if __name__ == "__main__":
    main()
