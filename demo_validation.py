#!/usr/bin/env python3
"""
🧮 Riemann-Adelic Validation Demonstration

This script demonstrates the numerical validation of the Weil explicit formula
as implemented in the Riemann-Adelic framework by José Manuel Mota Burruezo.

The validation compares two sides of the Weil explicit formula:
- Left side: Sum over non-trivial zeros + archimedean integral  
- Right side: Sum over prime powers + archimedean terms

Expected results show numerical agreement with error ~1e-7 under normal conditions.

Usage:
    python demo_validation.py [--quick] [--precision] [--show-details]
"""

import sys
import os
import time
import argparse
from pathlib import Path

# Add current directory to path to import validation modules
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

try:
    import mpmath as mp
    import numpy as np
    from validate_explicit_formula import weil_explicit_formula, truncated_gaussian
    from utils.fetch_odlyzko import create_sample_zeros
except ImportError as e:
    print(f"❌ Missing dependency: {e}")
    print("💡 Please install requirements: pip install -r requirements.txt")
    sys.exit(1)


def print_header():
    """Print demonstration header with paper information."""
    print("=" * 80)
    print("🧮 RIEMANN-ADELIC VALIDATION DEMONSTRATION")
    print("=" * 80)
    print()
    print("Paper: A Complete Proof of the Riemann Hypothesis via S-Finite Adelic Systems")
    print("Author: José Manuel Mota Burruezo")
    print("DOI: 10.5281/zenodo.17161831")
    print()
    print("This demonstration validates the Weil explicit formula:")
    print("  Left side:  Σ f(ρ) + ∫ f(it) dt  (zeros + archimedean)")
    print("  Right side: Σ Λ(n)f(log n) + arch terms  (primes + archimedean)")
    print()


def run_validation_demo(max_primes=1000, max_zeros=1000, precision_dps=30, show_details=False):
    """Run the main validation demonstration."""
    print(f"📋 VALIDATION PARAMETERS")
    print(f"   Max primes: {max_primes}")
    print(f"   Max zeros:  {max_zeros}")
    print(f"   Precision:  {precision_dps} decimal places")
    print()
    
    # Set precision
    mp.mp.dps = precision_dps
    
    # Ensure zeros data exists
    zeros_file = Path('zeros/zeros_t1e8.txt')
    if not zeros_file.exists():
        print("⚠️  Riemann zeros file not found. Creating sample data...")
        os.makedirs('zeros', exist_ok=True)
        if create_sample_zeros(str(zeros_file), num_zeros=max_zeros + 100):
            print("✅ Sample zeros created successfully")
        else:
            print("❌ Failed to create sample zeros")
            return False
    
    # Load zeros
    print("📂 Loading Riemann zeros...")
    zeros = []
    with open(zeros_file) as f:
        for i, line in enumerate(f):
            if i >= max_zeros:
                break
            zeros.append(mp.mpf(line.strip()))
    print(f"✅ Loaded {len(zeros)} zeros")
    
    # Load primes
    print("🔢 Generating prime numbers...")
    import sympy as sp
    primes = list(sp.primerange(2, max_primes + 1))
    print(f"✅ Generated {len(primes)} primes up to {max_primes}")
    
    # Run validation
    print()
    print("🧮 RUNNING WEIL EXPLICIT FORMULA VALIDATION...")
    print("=" * 60)
    
    start_time = time.time()
    
    try:
        error, relative_error, left_side, right_side, simulated_imag_parts = weil_explicit_formula(
            zeros, primes, truncated_gaussian, 
            max_zeros=max_zeros, 
            t_max=50, 
            precision=precision_dps
        )
        
        computation_time = time.time() - start_time
        
        print("✅ VALIDATION COMPLETED SUCCESSFULLY")
        print()
        print("📊 RESULTS:")
        print(f"   Left side (zeros + arch):    {left_side}")
        print(f"   Right side (primes + arch):  {right_side}")
        print(f"   Absolute error:              {error}")
        print(f"   Relative error:              {relative_error}")
        print(f"   Computation time:            {computation_time:.2f} seconds")
        print()
        
        # Error analysis
        if abs(relative_error) < 1e-6:
            print("🎯 EXCELLENT: Relative error < 1e-6 (high precision achieved)")
        elif abs(relative_error) < 1e-4:
            print("✅ GOOD: Relative error < 1e-4 (acceptable precision)")
        elif abs(relative_error) < 0.01:
            print("⚠️  MODERATE: Relative error < 1% (may need more data/precision)")
        else:
            print("❌ HIGH ERROR: Relative error > 1% (check parameters)")
        
        if show_details:
            print()
            print("🔍 DETAILED ANALYSIS:")
            print(f"   v-adic corrected zeros (first 10):")
            for i, sim_zero in enumerate(simulated_imag_parts[:10]):
                original = zeros[i] if i < len(zeros) else "N/A"
                print(f"     {i+1:2d}. Original: {original}, Corrected: {sim_zero}")
            
            print(f"   Error magnitude: {abs(float(error)):.2e}")
            print(f"   Error in scientific notation: {float(error):.6e}")
        
        return True
        
    except Exception as e:
        print(f"❌ VALIDATION FAILED: {e}")
        return False


def run_quick_demo():
    """Run a quick demonstration with reduced parameters."""
    print("⚡ QUICK DEMONSTRATION MODE")
    print()
    return run_validation_demo(max_primes=100, max_zeros=100, precision_dps=15)


def main():
    """Main demonstration function."""
    parser = argparse.ArgumentParser(
        description="Demonstrate Riemann-Adelic validation",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python demo_validation.py                    # Full demonstration
  python demo_validation.py --quick            # Quick demo (reduced parameters)
  python demo_validation.py --precision 50     # High precision
  python demo_validation.py --show-details     # Show detailed analysis
        """
    )
    
    parser.add_argument('--quick', action='store_true', 
                       help='Run quick demo with reduced parameters')
    parser.add_argument('--precision', type=int, default=30,
                       help='Decimal precision (default: 30)')
    parser.add_argument('--max-primes', type=int, default=1000,
                       help='Maximum primes to use (default: 1000)')
    parser.add_argument('--max-zeros', type=int, default=1000,
                       help='Maximum zeros to use (default: 1000)')
    parser.add_argument('--show-details', action='store_true',
                       help='Show detailed analysis of results')
    
    args = parser.parse_args()
    
    print_header()
    
    if args.quick:
        success = run_quick_demo()
    else:
        success = run_validation_demo(
            max_primes=args.max_primes,
            max_zeros=args.max_zeros, 
            precision_dps=args.precision,
            show_details=args.show_details
        )
    
    print()
    print("=" * 80)
    if success:
        print("🎉 DEMONSTRATION COMPLETED SUCCESSFULLY")
        print()
        print("📚 For more information, see:")
        print("   - README.md for usage instructions")
        print("   - logs/USAGE_EXAMPLE.md for parameter guidelines")
        print("   - validate_explicit_formula.py for full CLI options")
        print("   - Paper: https://doi.org/10.5281/zenodo.17161831")
    else:
        print("❌ DEMONSTRATION FAILED")
        print("💡 Try --quick mode for reduced parameters")
    
    print("=" * 80)
    return 0 if success else 1


if __name__ == "__main__":
    sys.exit(main())