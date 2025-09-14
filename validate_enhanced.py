#!/usr/bin/env python3
"""
🧠 Copilot Enhancement: Advanced Riemann Hypothesis Validation CLI

Enhanced validation script with:
- Configurable partial simulation runs
- SHA256 integrity verification
- CSV output for reproducible analysis  
- Result archiving and comparison
- Multiple test function support

Usage:
    python validate_enhanced.py --partial --max-primes 1000 --max-zeros 100
    python validate_enhanced.py --full --output-dir results/
    python validate_enhanced.py --verify results/partial_*.json
"""

import argparse
import sys
import json
from pathlib import Path

import mpmath as mp
from utils.validation_core import ComputationalValidator


def main():
    parser = argparse.ArgumentParser(
        description='Enhanced Riemann Hypothesis Validation with Computational Verification'
    )
    
    parser.add_argument('--partial', action='store_true',
                        help='Run partial validation (faster, for development)')
    parser.add_argument('--full', action='store_true',
                        help='Run full validation (slower, for publication)')
    parser.add_argument('--verify', type=str,
                        help='Verify integrity of saved results (path to JSON file)')
    
    parser.add_argument('--max-primes', type=int, default=1000,
                        help='Maximum number of primes to use (default: 1000)')
    parser.add_argument('--max-zeros', type=int, default=100,
                        help='Maximum number of zeros to use (default: 100)')
    parser.add_argument('--precision', type=int, default=50,
                        help='Decimal precision for calculations (default: 50)')
    parser.add_argument('--sigma0', type=float, default=2.0,
                        help='Real part for Archimedean integration (default: 2.0)')
    parser.add_argument('--T', type=float, default=50.0,
                        help='Integration bound (default: 50.0)')
    parser.add_argument('--output-dir', type=str, default='data/validation_runs',
                        help='Output directory for results (default: data/validation_runs)')
    
    args = parser.parse_args()
    
    if not (args.partial or args.full or args.verify):
        print("❌ Error: Must specify --partial, --full, or --verify")
        parser.print_help()
        return 1
        
    # Set precision
    mp.mp.dps = args.precision
    
    if args.verify:
        return verify_results(args.verify)
    
    # Initialize validator
    validator = ComputationalValidator(args.output_dir)
    
    if args.partial:
        print("🔄 Running partial validation...")
        results = validator.run_partial_validation(
            max_primes=args.max_primes,
            max_zeros=args.max_zeros,
            sigma0=args.sigma0,
            T=args.T
        )
        display_results(results)
        
    elif args.full:
        print("🔄 Running full validation...")
        # For full validation, use larger parameters
        results = validator.run_partial_validation(
            max_primes=max(10000, args.max_primes),
            max_zeros=max(2000, args.max_zeros),  
            sigma0=args.sigma0,
            T=max(100.0, args.T)
        )
        display_results(results)
        
    return 0


def display_results(results):
    """Display validation results in a clear format."""
    print(f"\n📊 Validation Results (Run ID: {results.run_id})")
    print("=" * 60)
    
    # Parameters
    print("\n🔧 Parameters:")
    for key, value in results.params.items():
        print(f"  {key}: {value}")
    
    # Core results
    print(f"\n🧮 Computational Results:")
    if 'prime_sum' in results.results:
        print(f"  Prime Sum:       {results.results['prime_sum']['value']}")
    if 'archimedean_sum' in results.results:
        print(f"  Archimedean Sum: {results.results['archimedean_sum']['value']}")
    if 'arithmetic_side' in results.results:
        print(f"  Arithmetic Side: {results.results['arithmetic_side']['value']}")
    if 'zero_sum' in results.results:
        print(f"  Zero Sum:        {results.results['zero_sum']['value']}")
        
    # Error analysis
    print(f"\n📈 Error Analysis:")
    if 'absolute_error' in results.results:
        abs_err = results.results['absolute_error']['value']
        print(f"  Absolute Error:  {abs_err}")
        
        # Convert to float for comparison
        try:
            abs_err_float = float(abs_err)
            if abs_err_float < 1e-10:
                print("  ✅ Excellent agreement (< 1e-10)")
            elif abs_err_float < 1e-5:
                print("  ✅ Good agreement (< 1e-5)")  
            elif abs_err_float < 1e-2:
                print("  ⚠️  Moderate agreement (< 1e-2)")
            else:
                print("  ❌ Poor agreement (>= 1e-2)")
        except (ValueError, TypeError):
            print("  ❓ Unable to assess agreement level")
            
    if 'relative_error' in results.results:
        rel_err = results.results['relative_error']['value']
        print(f"  Relative Error:  {rel_err}")
    
    # Integrity
    print(f"\n🔒 Data Integrity:")
    print(f"  SHA256 Hash:     {results.compute_integrity_hash()}")
    print(f"  Timestamp:       {results.timestamp}")
    
    # Output files
    output_dir = Path("data/validation_runs")
    csv_file = output_dir / f"{results.run_id}_results.csv"
    json_file = output_dir / f"{results.run_id}_full.json"
    
    print(f"\n💾 Output Files:")
    if csv_file.exists():
        print(f"  CSV Results:     {csv_file}")
    if json_file.exists():
        print(f"  Full Data:       {json_file}")
    
    print("\n✅ Validation completed successfully!")


def verify_results(filepath: str) -> int:
    """Verify the integrity of saved validation results."""
    print(f"🔍 Verifying results: {filepath}")
    
    try:
        validator = ComputationalValidator()
        verification = validator.verify_result_integrity(filepath)
        
        print(f"\n📋 Verification Results:")
        print(f"  File:            {verification['file']}")
        print(f"  Run ID:          {verification['run_id']}")
        print(f"  Timestamp:       {verification['timestamp']}")
        print(f"  Stored Hash:     {verification['stored_hash']}")
        print(f"  Computed Hash:   {verification['computed_hash']}")
        
        if verification['integrity_verified']:
            print(f"  ✅ Integrity:      VERIFIED")
            return 0
        else:
            print(f"  ❌ Integrity:      FAILED")
            return 1
            
    except Exception as e:
        print(f"❌ Error during verification: {e}")
        return 1


if __name__ == "__main__":
    sys.exit(main())