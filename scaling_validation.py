"""
Systematic scaling validation to achieve error ≤10^{-6}
"""

import mpmath as mp
import sympy as sp
import time
import os

def simple_test_function(u):
    """Simple smooth test function with good convergence properties"""
    if abs(u) <= 1:
        return mp.exp(-1 / (1 - u**2))  # Smooth compactly supported
    else:
        return mp.mpf(0)

def fhat(f, s, lim):
    """Mellin transform"""
    return mp.quad(lambda u: f(u) * mp.exp(s * u), [-lim, lim], maxdegree=8)

def compute_arithmetic_side(f, P, T, lim):
    """Compute arithmetic side (prime + archimedean)"""
    
    # Prime sum (simplified to k=1 only for speed)
    prime_sum = mp.mpf(0)
    primes = list(sp.primerange(2, P))
    for p in primes:
        lp = mp.log(p)
        prime_sum += lp * f(lp)
    
    # Archimedean part with residue correction
    def integrand(t):
        s = mp.mpc(2.0, t)
        return (mp.digamma(s/2) - mp.log(mp.pi)) * fhat(f, s, lim)
    
    arch_integral = mp.quad(integrand, [-T, T], maxdegree=8) / (2 * mp.pi)
    residue = fhat(f, mp.mpf(1), lim)
    arch_sum = arch_integral - residue
    
    return prime_sum + arch_sum.real

def compute_zero_side(f, N_zeros, lim):
    """Compute zero side using zetazero"""
    zero_sum = mp.mpf(0)
    
    for n in range(1, N_zeros + 1):
        rho = mp.zetazero(n)
        gamma = mp.im(rho)
        zero_contribution = fhat(f, 1j * gamma, lim).real
        zero_sum += zero_contribution
        
        # Progress tracking
        if n % 1000 == 0:
            print(f"    Processed {n}/{N_zeros} zeros...")
    
    return zero_sum

def scaling_validation():
    """Test scaling to achieve target precision"""
    
    # Fixed parameters
    mp.mp.dps = 25  # Higher precision for final validation
    f = simple_test_function
    lim = 2.0
    P = 1000  # Fixed number of primes
    T = 20    # Fixed archimedean parameter
    
    # Test with increasing numbers of zeros
    zero_counts = [100, 500, 1000, 2000, 5000]
    
    print("🎯 Systematic scaling validation")
    print(f"Function: simple_test_function, P={P}, T={T}, lim={lim}")
    print(f"Precision: {mp.mp.dps} digits")
    
    # Compute arithmetic side once (it doesn't depend on number of zeros)
    print("\nComputing arithmetic side...")
    start_time = time.time()
    A = compute_arithmetic_side(f, P, T, lim)
    arith_time = time.time() - start_time
    print(f"Arithmetic side: {A} (computed in {arith_time:.2f}s)")
    
    results = []
    
    for N_zeros in zero_counts:
        print(f"\n{'='*60}")
        print(f"Testing with {N_zeros} zeros")
        print(f"{'='*60}")
        
        start_time = time.time()
        
        # Compute zero side
        print(f"Computing zero sum with {N_zeros} zeros...")
        Z = compute_zero_side(f, N_zeros, lim)
        
        zero_time = time.time() - start_time
        
        # Results
        error = abs(A - Z)
        rel_error = error / abs(A) if abs(A) > 0 else float('inf')
        
        result = {
            'N_zeros': N_zeros,
            'A': A,
            'Z': Z,
            'error': error,
            'rel_error': rel_error,
            'time': zero_time,
            'success': error <= 1e-6
        }
        results.append(result)
        
        print(f"Results for {N_zeros} zeros:")
        print(f"  Arithmetic side: {A}")
        print(f"  Zero side:       {Z}")
        print(f"  Error:           {error}")
        print(f"  Relative error:  {rel_error}")
        print(f"  Computation time: {zero_time:.2f}s")
        
        if error <= 1e-6:
            print(f"  🎯 SUCCESS: Target error achieved!")
        else:
            improvement_factor = error / 1e-6
            print(f"  ⚠️  Need {improvement_factor:.1f}x improvement")
            
            # Estimate zeros needed (assuming linear convergence)
            if len(results) > 1:
                prev_error = results[-2]['error']
                error_reduction = prev_error / error if error > 0 else 1
                if error_reduction > 1:
                    estimated_zeros = N_zeros * (error / 1e-6) / error_reduction
                    print(f"  📈 Estimated zeros needed: ~{int(estimated_zeros)}")
        
        # Check if we should continue
        if error <= 1e-6:
            print("\n🎉 Target achieved! Stopping.")
            break
        
        # Don't continue if error is not decreasing sufficiently
        if len(results) > 1:
            prev_error = results[-2]['error']
            if error >= prev_error * 0.5:  # Error didn't reduce by at least 50%
                print(f"\n⚠️  Error reduction slowing down. May need different approach.")
    
    # Summary
    print(f"\n{'='*60}")
    print("SCALING SUMMARY")
    print(f"{'='*60}")
    
    for r in results:
        status = "✅ SUCCESS" if r['success'] else "❌ WORKING"
        print(f"{status} {r['N_zeros']:5d} zeros: error={float(r['error']):.2e}, time={r['time']:6.1f}s")
    
    # Save best result
    if results:
        best = min(results, key=lambda x: x['error'])
        save_scaling_results(results, best)
        
        if best['success']:
            print(f"\n🎯 ACHIEVEMENT: {best['N_zeros']} zeros achieved target error!")
            return True
        else:
            print(f"\n📊 Best result: {best['N_zeros']} zeros, error {float(best['error']):.2e}")
            return False
    
    return False

def save_scaling_results(results, best):
    """Save scaling validation results"""
    os.makedirs('data', exist_ok=True)
    
    # Save summary
    with open('data/scaling_results.csv', 'w') as f:
        f.write("N_zeros,arithmetic_side,zero_side,absolute_error,relative_error,computation_time,success\n")
        for r in results:
            f.write(f"{r['N_zeros']},{r['A']},{r['Z']},{r['error']},{r['rel_error']},{r['time']},{r['success']}\n")
    
    # Save best config
    with open('data/scaling_best_config.txt', 'w') as f:
        f.write(f"# Best scaling validation result\n")
        f.write(f"N_zeros = {best['N_zeros']}\n")
        f.write(f"error = {best['error']}\n")
        f.write(f"success = {best['success']}\n")
        f.write(f"computation_time = {best['time']:.2f}s\n")
    
    print("📊 Scaling results saved to data/scaling_results.csv")

if __name__ == "__main__":
    success = scaling_validation()
    
    if success:
        print("\n✅ Scaling validation completed successfully!")
        exit(0)
    else:
        print("\n⚠️  Target precision not yet achieved - need more zeros or different approach")
        exit(1)