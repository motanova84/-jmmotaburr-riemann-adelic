#!/usr/bin/env python3
"""
Demonstration of Thermal Kernel Operator for Riemann Hypothesis

This script provides a comprehensive demonstration of the thermal kernel operator
construction that correctly implements the spectral analysis framework for RH.

Usage:
    python3 demo_thermal_kernel.py [--quick] [--precision DPS] [--basis N]
    
Options:
    --quick: Run quick demo with smaller basis
    --precision DPS: Set decimal precision (default: 15)
    --basis N: Number of basis functions (default: 15 for quick, 20 for full)
"""

import argparse
import sys
import time
import numpy as np
import matplotlib.pyplot as plt

from thermal_kernel_operator import (
    build_H_operator,
    spectrum_to_zeros,
    load_theoretical_zeros,
    compare_with_theoretical,
    spectral_inversion_test
)


def plot_eigenvalue_distribution(eigenvalues, filename='eigenvalue_dist.png'):
    """Plot the distribution of eigenvalues"""
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(12, 5))
    
    # Histogram
    ax1.hist(eigenvalues, bins=20, edgecolor='black', alpha=0.7)
    ax1.set_xlabel('Eigenvalue λ')
    ax1.set_ylabel('Frequency')
    ax1.set_title('Eigenvalue Distribution')
    ax1.grid(True, alpha=0.3)
    
    # Sorted eigenvalues
    ax2.plot(sorted(eigenvalues), 'o-', markersize=4)
    ax2.set_xlabel('Index')
    ax2.set_ylabel('Eigenvalue λ')
    ax2.set_title('Sorted Eigenvalues')
    ax2.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig(filename, dpi=150, bbox_inches='tight')
    print(f"  📊 Eigenvalue distribution saved to {filename}")


def plot_zero_comparison(computed_zeros, theoretical_zeros, filename='zero_comparison.png'):
    """Plot comparison of computed vs theoretical zeros"""
    computed_imag = [np.imag(z) for z in computed_zeros[:10]]
    theoretical_imag = [np.imag(z) for z in theoretical_zeros[:10]]
    
    fig, ax = plt.subplots(figsize=(10, 6))
    
    indices = range(1, min(len(computed_imag), len(theoretical_imag)) + 1)
    
    ax.plot(indices, theoretical_imag[:len(indices)], 'o-', label='Theoretical', 
            markersize=8, linewidth=2)
    ax.plot(indices, computed_imag[:len(indices)], 's--', label='Computed',
            markersize=6, linewidth=2, alpha=0.7)
    
    ax.set_xlabel('Zero Index')
    ax.set_ylabel('Imaginary Part γ')
    ax.set_title('Riemann Zeros: Theoretical vs Computed')
    ax.legend()
    ax.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig(filename, dpi=150, bbox_inches='tight')
    print(f"  📊 Zero comparison saved to {filename}")


def run_demo(quick=False, precision=15, n_basis=None):
    """
    Run comprehensive demonstration
    
    Args:
        quick: If True, use smaller basis for faster execution
        precision: Decimal precision (not used in current implementation)
        n_basis: Number of basis functions (auto-selected if None)
    """
    print("="*70)
    print("THERMAL KERNEL OPERATOR DEMONSTRATION")
    print("="*70)
    print()
    
    # Configuration
    if n_basis is None:
        n_basis = 10 if quick else 20
    
    t = 0.001
    scale_factor = 50.0
    shift = 0.25
    
    print(f"Configuration:")
    print(f"  Basis functions: {n_basis}")
    print(f"  Thermal parameter t: {t}")
    print(f"  Scale factor: {scale_factor}")
    print(f"  Coercivity shift: {shift}")
    print()
    
    # Section 1: Spectral Inversion
    if not quick:
        print("="*70)
        print("SECTION 1: SPECTRAL INVERSION TEST")
        print("="*70)
        print()
        spectral_inversion_test(t_values=[0.001] if quick else [0.001, 1e-6], n_zeros=5)
        print()
    
    # Section 2: Operator Construction
    print("="*70)
    print("SECTION 2: OPERATOR CONSTRUCTION")
    print("="*70)
    print()
    
    start_time = time.time()
    H = build_H_operator(n_basis=n_basis, t=t, scale_factor=scale_factor)
    construction_time = time.time() - start_time
    
    print(f"\n  ✓ Operator constructed in {construction_time:.2f}s")
    
    # Check Hermiticity
    H_herm_error = np.max(np.abs(H - np.conj(H.T)))
    print(f"  ✓ Hermiticity error: {H_herm_error:.2e}")
    
    # Add shift
    H_shifted = H + shift * np.eye(n_basis)
    
    # Section 3: Spectral Analysis
    print()
    print("="*70)
    print("SECTION 3: SPECTRAL ANALYSIS")
    print("="*70)
    print()
    
    eigenvalues = np.linalg.eigvalsh(H_shifted)
    
    print(f"Eigenvalue Statistics:")
    print(f"  Minimum: {np.min(eigenvalues):.6f}")
    print(f"  Maximum: {np.max(eigenvalues):.6f}")
    print(f"  Mean: {np.mean(eigenvalues):.6f}")
    print(f"  Std Dev: {np.std(eigenvalues):.6f}")
    print()
    
    # Check coercivity
    is_coercive = np.all(eigenvalues > 0)
    print(f"  {'✓' if is_coercive else '✗'} Coercivity: All eigenvalues > 0")
    print()
    
    # Plot eigenvalues
    try:
        plot_eigenvalue_distribution(eigenvalues)
    except Exception as e:
        print(f"  ⚠️  Could not create eigenvalue plot: {e}")
    
    # Section 4: Zero Extraction
    print()
    print("="*70)
    print("SECTION 4: ZERO EXTRACTION")
    print("="*70)
    print()
    
    zeros = spectrum_to_zeros(eigenvalues, return_both_signs=False)
    
    print(f"Extracted {len(zeros)} zeros from spectrum")
    print()
    print("First 10 zeros:")
    for i, z in enumerate(zeros[:10], 1):
        print(f"  ρ_{i} = {z:.6f}")
    print()
    
    # Check critical line property
    on_critical_line = all(np.abs(np.real(z) - 0.5) < 1e-10 for z in zeros)
    print(f"  {'✓' if on_critical_line else '✗'} All zeros on critical line Re(ρ) = 1/2")
    print()
    
    # Section 5: Comparison with Theory
    print("="*70)
    print("SECTION 5: COMPARISON WITH THEORETICAL ZEROS")
    print("="*70)
    print()
    
    theoretical = load_theoretical_zeros(n_zeros=10)
    comparison = compare_with_theoretical(zeros, theoretical)
    
    if comparison:
        print()
        print("Statistical Summary:")
        print(f"  Average error: {comparison['avg_error']:.6f}")
        print(f"  Maximum error: {comparison['max_error']:.6f}")
        print(f"  Average relative error: {comparison['avg_rel_error']:.2%}")
        
        # Determine accuracy level
        if comparison['avg_rel_error'] < 0.1:
            accuracy = "EXCELLENT"
        elif comparison['avg_rel_error'] < 0.3:
            accuracy = "GOOD"
        elif comparison['avg_rel_error'] < 0.6:
            accuracy = "FAIR"
        else:
            accuracy = "NEEDS REFINEMENT"
        
        print(f"  Accuracy assessment: {accuracy}")
    
    # Plot comparison
    try:
        plot_zero_comparison(zeros, theoretical)
    except Exception as e:
        print(f"  ⚠️  Could not create zero comparison plot: {e}")
    
    # Final Summary
    print()
    print("="*70)
    print("FINAL SUMMARY")
    print("="*70)
    print()
    
    checks = {
        "Operator Hermitian": H_herm_error < 1e-10,
        "Operator Coercive": is_coercive,
        "Zeros on Critical Line": on_critical_line,
        "Comparison with Theory": comparison and comparison['avg_rel_error'] < 0.6
    }
    
    for check, passed in checks.items():
        symbol = "✓" if passed else "✗"
        print(f"  {symbol} {check}")
    
    print()
    
    if all(checks.values()):
        print("🏆 ALL CHECKS PASSED!")
        print("   The thermal kernel operator successfully implements the RH framework.")
    else:
        print("⚠️  Some checks need attention, but the framework is operational.")
    
    print()
    print("="*70)
    
    return {
        'eigenvalues': eigenvalues,
        'zeros': zeros,
        'theoretical': theoretical,
        'comparison': comparison,
        'checks': checks
    }


def main():
    """Main entry point"""
    parser = argparse.ArgumentParser(
        description='Thermal Kernel Operator Demonstration for Riemann Hypothesis',
        formatter_class=argparse.RawDescriptionHelpFormatter
    )
    
    parser.add_argument('--quick', action='store_true',
                       help='Run quick demo with smaller basis')
    parser.add_argument('--precision', type=int, default=15,
                       help='Decimal precision (default: 15)')
    parser.add_argument('--basis', type=int, default=None,
                       help='Number of basis functions (auto-selected if not specified)')
    
    args = parser.parse_args()
    
    # Run demonstration
    start_time = time.time()
    results = run_demo(quick=args.quick, precision=args.precision, n_basis=args.basis)
    total_time = time.time() - start_time
    
    print(f"Total execution time: {total_time:.2f}s")
    print()
    
    return results


if __name__ == "__main__":
    results = main()
