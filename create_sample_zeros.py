#!/usr/bin/env python3
"""
Create a sample zeros file for testing purposes.
Generates approximate zeros using the Gram points formula.
"""
import math
import os

def create_sample_zeros(filename="zeros/zeros_t1e8.txt", count=100):
    """Create a sample zeros file with approximate values."""
    os.makedirs("zeros", exist_ok=True)
    
    with open(filename, "w") as f:
        for n in range(1, count + 1):
            # Approximate zeros using Gram points formula
            t_n = 2 * math.pi * n / math.log(n) if n > 1 else 14.134725
            f.write(f"{t_n:.10f}\n")
    
    print(f"✅ Sample zeros file created with {count} entries: {filename}")

if __name__ == "__main__":
    create_sample_zeros()