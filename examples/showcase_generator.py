#!/usr/bin/env python3
"""
📊 Validation Results Showcase

This script generates a showcase of the Riemann-Adelic validation results.
"""

import sys
import os
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

try:
    import mpmath as mp
    from validate_explicit_formula import weil_explicit_formula, truncated_gaussian
    import sympy as sp
except ImportError as e:
    print(f"❌ Missing dependency: {e}")
    sys.exit(1)


def main():
    """Generate a quick validation showcase."""
    print("🧮 RIEMANN-ADELIC VALIDATION SHOWCASE")
    print("=" * 50)
    
    # Quick test
    mp.mp.dps = 15
    max_zeros = 50
    max_primes = 50
    
    # Load zeros from parent directory
    zeros_file = Path('..') / 'zeros' / 'zeros_t1e8.txt'
    zeros = []
    with open(zeros_file) as f:
        for i, line in enumerate(f):
            if i >= max_zeros:
                break
            zeros.append(mp.mpf(line.strip()))
    
    # Load primes
    primes = list(sp.primerange(2, max_primes + 1))
    
    print(f"Loaded {len(zeros)} zeros and {len(primes)} primes")
    print("Running Weil explicit formula validation...")
    
    try:
        error, relative_error, left_side, right_side, _ = weil_explicit_formula(
            zeros, primes, truncated_gaussian, 
            max_zeros=max_zeros, 
            t_max=25, 
            precision=15
        )
        
        print("\n✅ VALIDATION COMPLETED")
        print(f"Left side (zeros + arch):  {left_side}")
        print(f"Right side (primes + arch): {right_side}")
        print(f"Relative error: {float(relative_error):.6e}")
        
        # Write results to file
        with open('validation_results.md', 'w') as f:
            f.write("# Validation Results\n\n")
            f.write(f"- Configuration: {len(primes)} primes, {len(zeros)} zeros, 15 dps\n")
            f.write(f"- Left side: {left_side}\n")
            f.write(f"- Right side: {right_side}\n")
            f.write(f"- Relative error: {float(relative_error):.6e}\n")
        
        print("✅ Results saved to validation_results.md")
        
    except Exception as e:
        print(f"❌ Validation failed: {e}")
        return 1
    
    return 0


if __name__ == "__main__":
    sys.exit(main())