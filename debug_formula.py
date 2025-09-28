#!/usr/bin/env python3
"""
Debug script to identify the critical error in the explicit formula.

The main issue: absolute error > 2.8 and relative error ~100% is completely unacceptable
for mathematical validation of the Riemann Hypothesis.
"""

import mpmath as mp
import sympy as sp
from utils.mellin import truncated_gaussian, mellin_transform
import os

# Set precision
mp.mp.dps = 15

def debug_zero_sum():
    """Debug the zero sum calculation."""
    print("🔍 Debugging zero sum calculation...")
    
    # Load a few zeros for testing
    zeros_file = "zeros/zeros_t1e8.txt"
    actual_zeros = []
    
    if os.path.exists(zeros_file):
        with open(zeros_file, 'r') as f:
            for i, line in enumerate(f):
                if i >= 5:  # Just first 5 for debugging
                    break
                gamma = float(line.strip())
                actual_zeros.append(gamma)
    else:
        print("❌ No zeros file found")
        return
    
    print(f"Using zeros: {actual_zeros}")
    
    f = truncated_gaussian
    zero_sum = mp.mpf('0')
    
    for i, gamma in enumerate(actual_zeros):
        rho = mp.mpc(0.5, gamma)  # ρ = 1/2 + iγ on critical line
        
        # Debug the Mellin transform calculation
        print(f"\n  Zero {i}: γ = {gamma}")
        print(f"  ρ = {rho}")
        
        # Test different approaches to the Mellin transform
        # Standard approach: f̂(ρ) = ∫ f(u) exp((ρ-1)u) du
        f_hat_rho_v1 = mellin_transform(f, rho - 1, 5.0)
        
        # Alternative: f̂(s-1) = ∫ f(u) exp((s-1)u) du  
        f_hat_rho_v2 = mellin_transform(f, rho, 5.0)
        
        print(f"  Method 1 f̂(ρ-1): {f_hat_rho_v1}")
        print(f"  Method 2 f̂(ρ): {f_hat_rho_v2}")
        
        # Test function evaluation at key points
        print(f"  f(0) = {f(0)}")
        print(f"  f(1) = {f(1)}")
        print(f"  f(-1) = {f(-1)}")
        
        zero_sum += f_hat_rho_v1.real
    
    print(f"\nTotal zero sum: {zero_sum}")
    return zero_sum

def debug_prime_sum():
    """Debug the prime sum calculation."""
    print("\n🔍 Debugging prime sum calculation...")
    
    f = truncated_gaussian
    primes = list(sp.primerange(2, 100))  # Small set for debugging
    
    prime_sum_val = mp.mpf('0')
    
    for i, p in enumerate(primes[:10]):  # Just first 10 primes
        log_p = mp.log(p)
        
        print(f"\n  Prime {p}: log(p) = {log_p}")
        
        # Von Mangoldt function: Λ(p^k) = log(p) for prime powers
        for k in range(1, 4):  # k = 1, 2, 3
            n = p**k
            if n > 1000:
                break
                
            contrib = log_p * f(k * log_p)
            prime_sum_val += contrib
            
            print(f"    k={k}, n={n}, f({float(k * log_p):.3f}) = {float(f(k * log_p)):.6f}, contrib = {float(contrib):.6f}")
    
    print(f"\nTotal prime sum: {prime_sum_val}")
    return prime_sum_val

def debug_archimedean_integral():
    """Debug the archimedean integral calculation."""
    print("\n🔍 Debugging archimedean integral...")
    
    f = truncated_gaussian
    
    def arch_integrand(t):
        s = mp.mpc(0.5, t)
        f_hat_s = mellin_transform(f, s - 1, 5.0)
        # Archimedean factor: d/ds[log(Γ(s/2) * π^(-s/2))] = (1/2)[ψ(s/2) - log(π)]
        arch_kernel = 0.5 * (mp.digamma(s/2) - mp.log(mp.pi))
        return (f_hat_s * arch_kernel).real
    
    print("Testing integrand at key points:")
    for t in [0, 1, -1, 0.5, -0.5]:
        try:
            val = arch_integrand(t)
            print(f"  t={t}: integrand = {val}")
        except Exception as e:
            print(f"  t={t}: ERROR - {e}")
    
    # Try integration with small range
    T_limit = 2.0
    try:
        arch_integral = mp.quad(arch_integrand, [-T_limit, T_limit], maxdegree=4)
        arch_integral = arch_integral / (2 * mp.pi)  # Normalization
        print(f"\nArchimedean integral (T={T_limit}): {arch_integral}")
        
        # Test with sign flip
        arch_integral_flipped = -arch_integral
        print(f"With sign flip: {arch_integral_flipped}")
        
    except Exception as e:
        print(f"Integration failed: {e}")
        arch_integral = mp.mpf('0')
    
    return arch_integral

def main():
    """Debug the explicit formula components."""
    print("🚨 DEBUGGING CRITICAL EXPLICIT FORMULA ERROR")
    print("=" * 50)
    
    # Debug each component
    zero_sum = debug_zero_sum()
    prime_sum = debug_prime_sum()
    arch_integral = debug_archimedean_integral()
    
    # Pole term
    f = truncated_gaussian
    pole_term = f(0)
    print(f"\n🔍 Pole term f(0): {pole_term}")
    
    # Compare sides
    print("\n📊 EXPLICIT FORMULA COMPARISON")
    print("-" * 30)
    
    left_side = zero_sum + arch_integral + pole_term
    right_side = prime_sum
    
    print(f"Zero sum:           {zero_sum}")
    print(f"Archimedean:        {arch_integral}") 
    print(f"Pole term:          {pole_term}")
    print(f"LEFT SIDE:          {left_side}")
    print(f"RIGHT SIDE:         {right_side}")
    
    error = abs(left_side - right_side)
    rel_error = error / abs(right_side) if abs(right_side) > 0 else float('inf')
    
    print(f"\nAbsolute error:     {error}")
    print(f"Relative error:     {rel_error}")
    
    if rel_error > 0.1:
        print("🚨 CRITICAL ERROR: Relative error > 10% - Formula implementation is wrong!")
    elif rel_error > 1e-3:
        print("⚠️  WARNING: Relative error > 0.1% - Needs improvement")
    else:
        print("✅ Relative error acceptable")

if __name__ == "__main__":
    main()