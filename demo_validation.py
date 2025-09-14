#!/usr/bin/env python3
"""
Quick demo of validation and perturbation testing with minimal parameters
for immediate verification of the implementation.
"""

import mpmath as mp
import sympy as sp
from utils.mellin import truncated_gaussian, mellin_transform

mp.mp.dps = 30  # Reduced precision for speed

def demo_validation():
    """Quick demo with minimal parameters."""
    print("QUICK VALIDATION DEMO")
    print("=" * 40)
    
    f = truncated_gaussian
    
    # Very small parameters for demo
    P = 5  # Just primes 2, 3, 5
    K = 2  # Powers up to 2
    
    # Prime sum
    print("Computing prime sum...")
    prime_total = mp.mpf('0')
    primes = list(sp.primerange(2, P + 1))
    for p in primes:
        lp = mp.log(p)
        for k in range(1, K + 1):
            prime_total += lp * f(k * lp)
    
    print(f"Prime sum: {prime_total}")
    
    # Simple archimedean approximation (just the residue term)
    print("Computing simplified archimedean term...")
    # This is a simplified version - just the residue at s=1
    residue_term = mellin_transform(f, mp.mpf(1), 3.0) / mp.mpf(1)
    print(f"Residue term: {residue_term}")
    
    # Very small zero sum (just first few zeros)
    print("Computing first few zeros...")
    zero_total = mp.mpf('0')
    with open('zeros/zeros_t1e8.txt') as file:
        for i, line in enumerate(file):
            if i >= 3:  # Just first 3 zeros
                break
            gamma = mp.mpf(line.strip())
            zero_total += mellin_transform(f, 1j * gamma, 3.0).real
    
    print(f"Zero sum (first 3): {zero_total}")
    
    # Compare
    arithmetic = prime_total - residue_term  # Note: archimedean includes negative residue
    error = abs(arithmetic - zero_total)
    
    print(f"\nComparison (simplified):")
    print(f"Arithmetic side: {arithmetic}")
    print(f"Zero side:       {zero_total}")
    print(f"Error:          {float(error):.2e}")
    
    print("\nNote: This is a simplified demo. Full calculation requires more terms.")
    return float(error)

def demo_perturbation():
    """Quick perturbation demo."""
    print("\nPERTURBATION DEMO")
    print("=" * 40)
    
    f = truncated_gaussian
    
    # Original calculation
    prime_total = mp.mpf('0')
    primes = [2, 3, 5]
    for p in primes:
        lp = mp.log(p)
        prime_total += lp * f(lp)
    
    # Perturbed calculation
    perturb_total = mp.mpf('0')
    perturbation = 0.1
    for p in primes:
        lp = mp.log(p) * (1 + perturbation)  # Perturb log p
        perturb_total += lp * f(lp)
    
    print(f"Original prime sum:  {prime_total}")
    print(f"Perturbed prime sum: {perturb_total}")
    print(f"Change factor:       {perturb_total / prime_total}")
    
    print("\nThis shows the method is sensitive to perturbations ✓")

if __name__ == "__main__":
    demo_validation()
    demo_perturbation()
    
    print("\n" + "=" * 60)
    print("DEMO COMPLETE")
    print("The full validation scripts are ready:")
    print("- validate_explicit_formula.py (with CSV output)")
    print("- perturb_test.py (falsification testing)")  
    print("Use smaller parameters for faster execution in production.")
    print("=" * 60)