#!/usr/bin/env python3
"""
Debug the archimedean integral computation which is causing the massive error.
"""

import mpmath as mp
from utils.mellin import truncated_gaussian, mellin_transform

# Set precision
mp.mp.dps = 15

def debug_archimedean_integral():
    """Debug the archimedean integral calculation."""
    print("🔍 Debugging archimedean integral in detail...")
    
    f = truncated_gaussian
    
    # Test the mellin transform of our function at key points
    print("\n1. Testing Mellin transform f̂(s) at key points:")
    test_points = [
        mp.mpc(0, 0),      # s = 0
        mp.mpc(1, 0),      # s = 1  
        mp.mpc(0, 1),      # s = i
        mp.mpc(0, -1),     # s = -i
        mp.mpc(0.5, 0),    # s = 1/2
    ]
    
    for s in test_points:
        try:
            f_hat_s = mellin_transform(f, s, 5.0)
            print(f"  f̂({s}) = {f_hat_s}")
        except Exception as e:
            print(f"  f̂({s}) = ERROR: {e}")
    
    # Test the digamma function (which might be diverging)
    print("\n2. Testing digamma function ψ(1/2 + it/2) at key points:")
    for t in [0, 1, -1, 2, -2, 5, -5, 10, -10]:
        try:
            s = mp.mpc(0, t)
            arg = 0.5 + s/2  # 1/2 + it/2
            psi_val = mp.digamma(arg)
            print(f"  t={t}: ψ(1/2 + it/2) = ψ({arg}) = {psi_val}")
        except Exception as e:
            print(f"  t={t}: ERROR: {e}")
    
    # Test the complete integrand
    print("\n3. Testing complete integrand at key points:")
    def arch_integrand(t):
        s = mp.mpc(0, t)  # Pure imaginary: it
        f_hat_s = mellin_transform(f, s, 5.0)
        # Kernel: ψ(1/2 + it/2) - log(π)
        arch_kernel = mp.digamma(0.5 + s/2) - mp.log(mp.pi)
        return (f_hat_s * arch_kernel).real
    
    for t in [0, 0.1, -0.1, 0.5, -0.5, 1, -1]:
        try:
            val = arch_integrand(t)
            print(f"  t={t}: integrand = {val}")
        except Exception as e:
            print(f"  t={t}: ERROR: {e}")
    
    # Try smaller integration ranges
    print("\n4. Testing integration with different ranges:")
    for T_limit in [0.5, 1.0, 2.0, 5.0, 10.0]:
        try:
            integral = mp.quad(arch_integrand, [-T_limit, T_limit], maxdegree=4)
            normalized = integral / (2 * mp.pi)
            print(f"  T={T_limit}: raw = {integral}, normalized = {normalized}")
        except Exception as e:
            print(f"  T={T_limit}: ERROR: {e}")
    
    # Compare with alternative formulation
    print("\n5. Testing alternative archimedean formulation:")
    def alt_arch_integrand(t):
        """Alternative formulation based on functional equation."""
        s = mp.mpc(0.5, t)  # s = 1/2 + it on critical line
        f_hat_s = mellin_transform(f, s - 1, 5.0)  # f̂(s-1)
        # Logarithmic derivative of Γ(s/2)π^(-s/2)
        kernel = 0.5 * (mp.digamma(s/2) - mp.log(mp.pi))
        return (f_hat_s * kernel).real
    
    for t in [0, 1, -1]:
        try:
            val = alt_arch_integrand(t)
            print(f"  Alt t={t}: integrand = {val}")
        except Exception as e:
            print(f"  Alt t={t}: ERROR: {e}")
    
    # Test if the function decays properly at infinity
    print("\n6. Testing decay at large |t|:")
    large_t_values = [10, 20, 50, 100]
    for t in large_t_values:
        try:
            val_pos = arch_integrand(t)
            val_neg = arch_integrand(-t)
            print(f"  t=±{t}: {val_pos:.6e}, {val_neg:.6e}")
        except Exception as e:
            print(f"  t=±{t}: ERROR: {e}")

if __name__ == "__main__":
    debug_archimedean_integral()