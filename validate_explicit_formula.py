"""
🧠 Enhanced Riemann Hypothesis Validation Script

This script validates the explicit formula related to the Riemann Hypothesis with:
- Complete CLI support with configurable parameters
- CSV output with timestamps and comprehensive results
- Structured logging to logs/ directory
- Multiple test functions (f1, f2, f3) support
- Robust error handling and recovery
- Automatic zeros file validation

Usage:
python validate_explicit_formula.py --P 1000 --K 50 --test_functions f1 f2 f3 --output_csv data/results.csv
"""

import mpmath as mp
import sympy as sp
import os
import sys
import logging
import datetime
from utils.mellin import truncated_gaussian, mellin_transform

# Reduce precision for faster computation
mp.mp.dps = 15  # Reduced from 50

# Test functions (compactly supported)
def f1(u): 
    """Truncated Gaussian function"""
    return mp.exp(-u**2/2) if abs(u) <= 3 else mp.mpf(0)

def f2(u): 
    """Alternative Gaussian function"""
    return mp.exp(-u**2) if abs(u) <= 2 else mp.mpf(0)

def f3(u): 
    """Polynomial function"""
    return (1 - u**2/4)**2 if abs(u) <= 2 else mp.mpf(0)

TEST_FUNCTIONS = {
    'f1': f1,
    'f2': f2, 
    'f3': f3,
    'truncated_gaussian': truncated_gaussian
}

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

def setup_logging(log_dir="logs"):
    """Setup comprehensive logging."""
    os.makedirs(log_dir, exist_ok=True)
    timestamp = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
    log_file = os.path.join(log_dir, f"validation_{timestamp}.log")
    
    logging.basicConfig(
        level=logging.INFO,
        format='%(asctime)s - %(levelname)s - %(message)s',
        handlers=[
            logging.FileHandler(log_file),
            logging.StreamHandler(sys.stdout)
        ]
    )
    return logging.getLogger(__name__)

def validate_zeros_file(filename, max_lines=None):
    """Validate zeros file format and accessibility."""
    if not os.path.exists(filename):
        return False, f"Zeros file not found: {filename}"
    
    try:
        with open(filename, 'r') as f:
            count = 0
            for i, line in enumerate(f):
                if max_lines and i >= max_lines:
                    break
                try:
                    float(line.strip())
                    count += 1
                except ValueError:
                    return False, f"Invalid format at line {i+1}: {line.strip()}"
            return True, f"Valid zeros file with {count} entries checked"
    except Exception as e:
        return False, f"Error reading zeros file: {e}"

def save_results_csv(results, output_file, logger):
    """Save validation results to CSV with comprehensive metadata."""
    os.makedirs(os.path.dirname(output_file), exist_ok=True)
    
    try:
        with open(output_file, 'w') as f:
            f.write("# Riemann Hypothesis Validation Results\n")
            f.write(f"# Generated: {datetime.datetime.now().isoformat()}\n")
            f.write("parameter,value\n")
            
            for key, value in results.items():
                f.write(f"{key},{value}\n")
        
        logger.info(f"📊 Results saved to {output_file}")
        return True
    except Exception as e:
        logger.error(f"❌ Error saving results: {e}")
        return False

def zero_sum_limited(f, filename, max_zeros, lim_u=5, logger=None):
    """Compute zero sum using only first max_zeros from file."""
    total = mp.mpf('0')
    count = 0
    try:
        with open(filename) as file:
            for line in file:
                if count >= max_zeros:
                    break
                try:
                    gamma = mp.mpf(line.strip())
                    total += mellin_transform(f, 1j * gamma, lim_u).real
                    count += 1
                except ValueError as e:
                    if logger:
                        logger.warning(f"Skipping invalid zero at line {count+1}: {e}")
                    continue
        if logger:
            logger.info(f"Used {count} zeros for computation")
        else:
            print(f"Used {count} zeros for computation")
        return total
    except Exception as e:
        error_msg = f"Error computing zero sum: {e}"
        if logger:
            logger.error(error_msg)
        else:
            print(error_msg)
        raise
if __name__ == "__main__":
    import argparse
    
    parser = argparse.ArgumentParser(
        description='Enhanced Riemann Hypothesis Validation',
        formatter_class=argparse.ArgumentDefaultsHelpFormatter
    )
    parser.add_argument('--P', '--max_primes', type=int, default=1000, 
                       help='Maximum prime P to use')
    parser.add_argument('--K', type=int, default=5,
                       help='Maximum powers K per prime')
    parser.add_argument('--sigma0', type=float, default=2.0,
                       help='Real part of integration line')
    parser.add_argument('--T', type=int, default=100,
                       help='Integration limit T')
    parser.add_argument('--max_zeros', type=int, default=2000,
                       help='Maximum number of zeros to use')
    parser.add_argument('--test_functions', nargs='+', default=['truncated_gaussian'],
                       choices=['f1', 'f2', 'f3', 'truncated_gaussian'],
                       help='Test functions to use')
    parser.add_argument('--output_csv', default='data/validation_results.csv',
                       help='Output CSV file path')
    parser.add_argument('--timeout', type=int, default=300,
                       help='Timeout in seconds')
    parser.add_argument('--lim_u', type=float, default=3.0,
                       help='Integration limit for Mellin transforms')
    parser.add_argument('--log_dir', default='logs',
                       help='Directory for log files')
    
    args = parser.parse_args()
    
    # Setup logging
    logger = setup_logging(args.log_dir)
    logger.info("🔬 Starting Enhanced Riemann Hypothesis Validation")
    logger.info(f"Parameters: P={args.P}, K={args.K}, T={args.T}, max_zeros={args.max_zeros}")
    logger.info(f"Test functions: {args.test_functions}")
    
    # Validate parameters
    P = min(args.P, 10000)  # Cap at 10000 to prevent timeout
    K = args.K
    sigma0 = args.sigma0
    T = max(1, min(args.T, args.max_zeros // 10))  # Ensure T >= 1
    lim_u = args.lim_u
    
    if P != args.P:
        logger.warning(f"P capped at {P} for performance")
    if T != args.T:
        logger.warning(f"T adjusted to {T} based on max_zeros")
    
    try:
        # Check zeros file
        zeros_file = 'zeros/zeros_t1e8.txt'
        is_valid, msg = validate_zeros_file(zeros_file, max_lines=args.max_zeros)
        if not is_valid:
            logger.error(f"❌ {msg}")
            sys.exit(1)
        logger.info(f"✅ {msg}")
        
        results_summary = {}
        
        # Process each test function
        for func_name in args.test_functions:
            if func_name not in TEST_FUNCTIONS:
                logger.warning(f"Unknown test function: {func_name}, skipping")
                continue
                
            logger.info(f"🧮 Processing test function: {func_name}")
            f = TEST_FUNCTIONS[func_name]
            
            # Compute arithmetic side
            logger.info("Computing arithmetic side...")
            prime_part = prime_sum(f, P, K)
            arch_part = archimedean_sum(f, sigma0, T, lim_u)
            A = prime_part + arch_part
            
            logger.info("Computing zero side...")
            Z = zero_sum_limited(f, zeros_file, args.max_zeros, lim_u, logger)
            
            # Calculate errors
            error = abs(A - Z)
            rel_error = error / abs(A) if abs(A) > 0 else float('inf')
            
            logger.info(f"✅ {func_name} completed!")
            logger.info(f"Arithmetic side: {A}")
            logger.info(f"Zero side: {Z}")
            logger.info(f"Absolute error: {error}")
            logger.info(f"Relative error: {rel_error}")
            
            # Store results
            results_summary.update({
                f"{func_name}_arithmetic_side": A,
                f"{func_name}_zero_side": Z,
                f"{func_name}_absolute_error": error,
                f"{func_name}_relative_error": rel_error,
            })
        
        # Add metadata to results
        results_summary.update({
            "P": P,
            "K": K,
            "sigma0": sigma0,
            "T": T,
            "max_zeros": args.max_zeros,
            "lim_u": lim_u,
            "test_functions": " ".join(args.test_functions),
            "timestamp": datetime.datetime.now().isoformat()
        })
        
        # Save results
        if save_results_csv(results_summary, args.output_csv, logger):
            logger.info("🎯 Validation completed successfully!")
        else:
            logger.error("❌ Failed to save results")
            sys.exit(1)
            
    except Exception as e:
        logger.error(f"❌ Error during computation: {e}")
        logger.exception("Full traceback:")
        sys.exit(1)

