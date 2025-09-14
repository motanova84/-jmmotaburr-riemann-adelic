#!/usr/bin/env python3
"""
🧠 Copilot Prompt:
Implement falsification testing for the Riemann Hypothesis validation.

This script performs perturbation tests to demonstrate scientific rigor:
- Perturb log q_v values (prime logarithms)
- Perturb kernel functions (digamma, log π)
- Perturb symmetry in the explicit formula
- Test with specified parameters: δ=0.01, P=1000, T=50

Expected: perturbations should break the explicit formula balance,
showing the method is sensitive to theoretical correctness.
"""

import argparse
import csv
import os
import mpmath as mp
import sympy as sp
from datetime import datetime
from utils.mellin import truncated_gaussian, mellin_transform
from validate_explicit_formula import prime_sum, archimedean_sum, zero_sum

mp.mp.dps = 50

def perturbed_prime_sum(f, P, K, perturbation=0.01):
    """Prime sum with perturbed log p values."""
    total = mp.mpf('0')
    primes = list(sp.primerange(2, P + 1))
    for p in primes:
        # Perturb log p by adding noise
        lp = mp.log(p) * (1 + perturbation * mp.rand())  # Random perturbation
        for k in range(1, K + 1):
            total += lp * f(k * lp)
    return total

def perturbed_archimedean_sum(f, sigma0, T, lim_u, perturbation=0.01):
    """Archimedean sum with perturbed kernel."""
    def integrand(t):
        s = sigma0 + 1j * t
        # Perturb the digamma kernel
        kernel = mp.digamma(s / 2) - mp.log(mp.pi)
        kernel *= (1 + perturbation)  # Apply perturbation
        return kernel * mellin_transform(f, s, lim_u)
    integral, err = mp.quad(integrand, [-T, T], error=True)
    return (integral / (2j * mp.pi)).real

def perturbed_zero_sum(f, filename, lim_u=5, perturbation=0.01):
    """Zero sum with perturbed symmetry (artificial asymmetry)."""
    total = mp.mpf('0')
    count = 0
    with open(filename) as file:
        for line in file:
            gamma = mp.mpf(line.strip())
            # Introduce asymmetric perturbation
            if count % 2 == 0:
                gamma *= (1 + perturbation)
            else:
                gamma *= (1 - perturbation)
            total += mellin_transform(f, 1j * gamma, lim_u).real
            count += 1
    return total

def run_perturbation_test(test_type, delta=0.01, P=1000, K=5, T=50, output_dir="data"):
    """Run a specific perturbation test."""
    print(f"\n{'='*60}")
    print(f"PERTURBATION TEST: {test_type.upper()}")
    print(f"Parameters: δ={delta}, P={P}, K={K}, T={T}")
    print(f"{'='*60}")
    
    f = truncated_gaussian
    sigma0 = 2.0
    lim_u = 5.0
    
    # Original values (should balance)
    A_orig = prime_sum(f, P, K) + archimedean_sum(f, sigma0, T, lim_u)
    Z_orig = zero_sum(f, 'zeros/zeros_t1e8.txt', lim_u)
    error_orig = abs(A_orig - Z_orig)
    
    print(f"ORIGINAL (unperturbed):")
    print(f"  Arithmetic side: {A_orig}")
    print(f"  Zero side:       {Z_orig}")
    print(f"  Error:          {error_orig:.2e}")
    print(f"  Relative error: {error_orig/abs(A_orig):.2e}")
    
    # Perturbed values
    if test_type == "prime_logs":
        A_pert = perturbed_prime_sum(f, P, K, delta) + archimedean_sum(f, sigma0, T, lim_u)
        Z_pert = Z_orig
    elif test_type == "kernel":
        A_pert = prime_sum(f, P, K) + perturbed_archimedean_sum(f, sigma0, T, lim_u, delta)
        Z_pert = Z_orig
    elif test_type == "symmetry":
        A_pert = A_orig
        Z_pert = perturbed_zero_sum(f, 'zeros/zeros_t1e8.txt', lim_u, delta)
    else:
        raise ValueError(f"Unknown test type: {test_type}")
    
    error_pert = abs(A_pert - Z_pert)
    
    print(f"\nPERTURBED (δ={delta}):")
    print(f"  Arithmetic side: {A_pert}")
    print(f"  Zero side:       {Z_pert}")
    print(f"  Error:          {error_pert:.2e}")
    print(f"  Relative error: {error_pert/abs(A_pert):.2e}")
    
    # Analysis
    error_amplification = error_pert / error_orig if error_orig > 0 else float('inf')
    
    print(f"\nANALYSIS:")
    print(f"  Error amplification: {error_amplification:.2f}x")
    print(f"  Status: {'FAIL (as expected)' if error_pert > 10*error_orig else 'UNEXPECTED - should fail!'}")
    
    # Save results
    os.makedirs(output_dir, exist_ok=True)
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    filename = os.path.join(output_dir, f"perturb_test_{test_type}_{timestamp}.csv")
    
    with open(filename, 'w', newline='') as csvfile:
        writer = csv.writer(csvfile)
        writer.writerow(['Parameter', 'Value'])
        writer.writerow(['test_type', test_type])
        writer.writerow(['delta', delta])
        writer.writerow(['P', P])
        writer.writerow(['K', K])
        writer.writerow(['T', T])
        writer.writerow(['timestamp', timestamp])
        writer.writerow([])
        writer.writerow(['Metric', 'Original', 'Perturbed'])
        writer.writerow(['arithmetic_side', A_orig, A_pert])
        writer.writerow(['zero_side', Z_orig, Z_pert])
        writer.writerow(['absolute_error', error_orig, error_pert])
        writer.writerow(['relative_error', error_orig/abs(A_orig), error_pert/abs(A_pert)])
        writer.writerow(['error_amplification', 1.0, error_amplification])
    
    print(f"\nResults saved to: {filename}")
    return error_amplification

def main():
    parser = argparse.ArgumentParser(description='Run perturbation tests for RH validation')
    parser.add_argument('--test-type', choices=['prime_logs', 'kernel', 'symmetry', 'all'], 
                       default='all', help='Type of perturbation test')
    parser.add_argument('--delta', type=float, default=0.01, 
                       help='Perturbation magnitude (default: 0.01)')
    parser.add_argument('--P', type=int, default=1000, 
                       help='Maximum prime (default: 1000)')
    parser.add_argument('--K', type=int, default=5, 
                       help='Maximum prime powers (default: 5)')
    parser.add_argument('--T', type=float, default=50, 
                       help='Integration limit (default: 50)')
    parser.add_argument('--output-dir', default='data', 
                       help='Output directory for CSV files')
    
    args = parser.parse_args()
    
    print("RIEMANN HYPOTHESIS PERTURBATION TESTS")
    print("="*60)
    print("Testing scientific rigor through falsification")
    print("Expected: perturbations should break formula balance")
    print("="*60)
    
    if args.test_type == 'all':
        test_types = ['prime_logs', 'kernel', 'symmetry']
    else:
        test_types = [args.test_type]
    
    results = {}
    for test_type in test_types:
        try:
            amplification = run_perturbation_test(
                test_type, args.delta, args.P, args.K, args.T, args.output_dir
            )
            results[test_type] = amplification
        except Exception as e:
            print(f"ERROR in {test_type} test: {e}")
            results[test_type] = None
    
    # Summary
    print(f"\n{'='*60}")
    print("SUMMARY OF PERTURBATION TESTS")
    print(f"{'='*60}")
    for test_type, amplification in results.items():
        if amplification is not None:
            status = "PASS (correctly sensitive)" if amplification > 10 else "CONCERN (not sensitive enough)"
            print(f"{test_type:12} | Error amplification: {amplification:8.2f}x | {status}")
        else:
            print(f"{test_type:12} | FAILED TO RUN")
    
    print("\nConclusion: A good RH validation should show high sensitivity to perturbations")
    print("This demonstrates the method is scientifically rigorous, not dogmatic.")

if __name__ == "__main__":
    main()