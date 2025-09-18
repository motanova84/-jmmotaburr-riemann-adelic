#!/usr/bin/env python3
"""
Create sample zeros file for testing if it doesn't exist.
This generates approximate Riemann zeta zeros using Gram points formula.
"""
import math
import os

def create_sample_zeros():
    """Create a sample zeros file with approximate zeros for testing."""
    zeros_file = "zeros/zeros_t1e8.txt"
    
    if os.path.exists(zeros_file):
        print(f"✅ Zeros file already exists: {zeros_file}")
        return
    
    os.makedirs("zeros", exist_ok=True)
    
    with open(zeros_file, 'w') as f:
        for n in range(1, 101):
            # Approximate zeros using Gram points formula
            t_n = 2 * math.pi * n / math.log(n) if n > 1 else 14.134725
            f.write(f'{t_n:.10f}\n')
    
    print(f"✅ Sample zeros file created: {zeros_file}")

if __name__ == "__main__":
    create_sample_zeros()