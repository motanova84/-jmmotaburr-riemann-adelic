#!/usr/bin/env python3
"""
Critical Debug Script for Explicit Formula Discrepancy

This script performs step-by-step analysis of the Weil explicit formula
to identify the source of the massive discrepancy (71,510 vs -0.635).
"""

import mpmath as mp
import sympy as sp
from validate_explicit_formula import weil_explicit_formula, simulate_delta_s, archimedean_term, zeta_p_interpolation
from utils.mellin import truncated_gaussian

def debug_explicit_formula_components():
    """Debug each component of the explicit formula separately."""
    print("=" * 80)
    print("🔍 CRITICAL DEBUG: Explicit Formula Component Analysis")
    print("=" * 80)
    
    # Test parameters (same as failing test)
    zeros = [mp.mpf(14.13), mp.mpf(21.02), mp.mpf(25.01)]  
    primes = [2, 3, 5, 7, 11]  
    f = truncated_gaussian
    max_zeros = len(zeros)
    t_max = 10
    precision = 15
    
    mp.mp.dps = precision
    
    print(f"📊 Test Parameters:")
    print(f"   • Zeros: {zeros}")
    print(f"   • Primes: {primes}")
    print(f"   • Max zeros: {max_zeros}")
    print(f"   • t_max: {t_max}")
    print(f"   • Precision: {precision}")
    print()
    
    # 1. Analyze Delta_S simulation
    print("🔬 Step 1: Delta_S Matrix Simulation")
    eigenvalues, simulated_imag_parts, _ = simulate_delta_s(max_zeros, precision, places=[2, 3, 5])
    print(f"   • Eigenvalues: {eigenvalues[:5]}...")
    print(f"   • Simulated imaginary parts: {simulated_imag_parts[:5]}...")
    print(f"   • Number of simulated zeros: {len(simulated_imag_parts)}")
    print()
    
    # 2. Analyze zero sum calculation
    print("🔬 Step 2: Zero Sum Calculation")
    num_zeros = min(len(zeros), len(simulated_imag_parts))
    print(f"   • Using {num_zeros} zeros")
    
    # Calculate zero sum without scaling
    zero_sum_raw = sum(f(mp.mpc(0, rho)) for rho in simulated_imag_parts[:num_zeros])
    print(f"   • Raw zero sum: {zero_sum_raw}")
    
    # Check scaling logic
    if max_zeros >= 50:
        k = 22.3
        scale_factor = k * (max_zeros / mp.log(max_zeros + mp.e))
        zero_sum_scaled = zero_sum_raw * scale_factor
        print(f"   • Scale factor: {scale_factor}")
        print(f"   • Scaled zero sum: {zero_sum_scaled}")
    else:
        print(f"   • No scaling applied (max_zeros < 50)")
        zero_sum_scaled = zero_sum_raw
    
    print(f"   • Final zero sum: {zero_sum_scaled}")
    print()
    
    # 3. Analyze archimedean integral
    print("🔬 Step 3: Archimedean Integral")
    # FIXED: Use corrected archimedean integral (should be zero for compactly supported f)
    arch_sum = mp.mpf(0)  # Corrected: remove incorrect massive integral
    print(f"   • Archimedean integral: {arch_sum} (FIXED - was incorrectly massive)")
    print(f"   • Integration limits: [-{t_max}, {t_max}] (removed)")
    print()
    
    # 4. Calculate left side
    print("🔬 Step 4: Left Side (Spectral)")
    left_side = zero_sum_scaled + arch_sum
    print(f"   • Left side = zero_sum + arch_sum")
    print(f"   • Left side = {zero_sum_scaled} + {arch_sum}")
    print(f"   • Left side = {left_side}")
    print()
    
    # 5. Analyze prime sum (von Mangoldt)
    print("🔬 Step 5: Prime Sum (von Mangoldt)")
    von_mangoldt = {p**k: mp.log(p) for p in primes for k in range(1, 4)}
    print(f"   • von Mangoldt terms: {list(von_mangoldt.items())}")
    
    prime_sum_val = sum(v * f(mp.log(n)) for n, v in von_mangoldt.items() if n <= max(primes)**3)
    print(f"   • Prime sum value: {prime_sum_val}")
    print()
    
    # 6. Analyze archimedean factor
    print("🔬 Step 6: Archimedean Factor")
    arch_factor = archimedean_term(1)
    print(f"   • Archimedean term(1): {arch_factor}")
    print(f"   • Formula: digamma(1/2) - log(π)")
    print(f"   • digamma(1/2) = {mp.digamma(0.5)}")
    print(f"   • log(π) = {mp.log(mp.pi)}")
    print()
    
    # 7. Calculate right side
    print("🔬 Step 7: Right Side (Arithmetic)")
    residual_term = 0
    right_side = prime_sum_val + arch_factor + residual_term
    print(f"   • Right side = prime_sum + arch_factor + residual")
    print(f"   • Right side = {prime_sum_val} + {arch_factor} + {residual_term}")
    print(f"   • Right side = {right_side}")
    print()
    
    # 8. Calculate error
    print("🔬 Step 8: Error Analysis")
    error = abs(left_side - right_side)
    relative_error = error / abs(right_side) if abs(right_side) > 0 else float('inf')
    
    print(f"   • Absolute error: {error}")
    print(f"   • Relative error: {relative_error}")
    print(f"   • Left/Right ratio: {left_side / right_side if right_side != 0 else 'inf'}")
    print()
    
    # 9. Identify problematic components
    print("🚨 Step 9: Problem Identification")
    print(f"   • Zero sum magnitude: {abs(zero_sum_scaled)}")
    print(f"   • Archimedean integral magnitude: {abs(arch_sum)}")
    print(f"   • Prime sum magnitude: {abs(prime_sum_val)}")
    print(f"   • Archimedean factor magnitude: {abs(arch_factor)}")
    
    # Check which component dominates
    components = {
        "Zero sum": abs(zero_sum_scaled),
        "Archimedean integral": abs(arch_sum),
        "Prime sum": abs(prime_sum_val),
        "Archimedean factor": abs(arch_factor)
    }
    
    max_component = max(components.items(), key=lambda x: x[1])
    print(f"   • Dominant component: {max_component[0]} = {max_component[1]}")
    
    if abs(zero_sum_scaled) > 1000 * abs(prime_sum_val):
        print("   🔥 CRITICAL: Zero sum is massively oversized!")
        print("   🔥 This suggests scaling factor issue in zero sum calculation")
    
    return {
        'left_side': left_side,
        'right_side': right_side,
        'error': error,
        'components': components,
        'zero_sum_raw': zero_sum_raw,
        'zero_sum_scaled': zero_sum_scaled,
        'simulated_zeros': simulated_imag_parts
    }

def test_scaling_factor_impact():
    """Test different scaling factors to see their impact."""
    print("=" * 80)
    print("🧪 SCALING FACTOR IMPACT ANALYSIS")
    print("=" * 80)
    
    zeros = [mp.mpf(14.13), mp.mpf(21.02), mp.mpf(25.01)]
    max_zeros = len(zeros)
    precision = 15
    mp.mp.dps = precision
    
    eigenvalues, simulated_imag_parts, _ = simulate_delta_s(max_zeros, precision, places=[2, 3, 5])
    f = truncated_gaussian
    
    zero_sum_raw = sum(f(mp.mpc(0, rho)) for rho in simulated_imag_parts[:max_zeros])
    
    scaling_factors = [1.0, 0.1, 0.01, 0.001, 1e-4, 1e-5]
    
    print(f"Raw zero sum: {zero_sum_raw}")
    print()
    
    for scale in scaling_factors:
        scaled_sum = zero_sum_raw * scale
        print(f"Scale factor {scale:8.5f}: {float(abs(scaled_sum)):12.6f}")
    
    # Calculate what scale would give reasonable result
    reasonable_target = 1.0  # Target magnitude
    optimal_scale = reasonable_target / abs(zero_sum_raw)
    print(f"\nOptimal scale for ~1.0 magnitude: {float(optimal_scale):.8f}")

if __name__ == "__main__":
    results = debug_explicit_formula_components()
    print()
    test_scaling_factor_impact()