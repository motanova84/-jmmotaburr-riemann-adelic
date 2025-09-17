"""
Progressive validation test to find optimal parameters for ≤10^{-6} error
"""

import mpmath as mp
import sympy as sp
from utils.mellin import truncated_gaussian, mellin_transform
import time
import os

def test_validation_parameters():
    """Test different parameter combinations to find optimal settings."""
    
    # Test configurations (primes, zeros, precision)
    test_configs = [
        (50, 50, 15),    # Very small test
        (100, 100, 15),  # Small test  
        (200, 200, 20),  # Medium test
        (500, 500, 20),  # Larger test
        (1000, 1000, 25), # Big test
    ]
    
    results = []
    
    for P, max_zeros, precision in test_configs:
        print(f"\n{'='*60}")
        print(f"Testing: P={P}, zeros={max_zeros}, precision={precision}")
        print(f"{'='*60}")
        
        # Set precision
        mp.mp.dps = precision
        
        # Parameters
        K = 5
        sigma0 = 2.0
        T = max(10, min(50, max_zeros // 20))
        lim_u = 3.0
        
        try:
            start_time = time.time()
            
            f = truncated_gaussian
            zeros_file = 'zeros/zeros_t1e8.txt'
            
            # Compute arithmetic side
            print("Computing prime sum...")
            prime_total = mp.mpf('0')
            primes = list(sp.primerange(2, P + 1))
            for p in primes:
                lp = mp.log(p)
                for k in range(1, K + 1):
                    prime_total += lp * f(k * lp)
            
            print("Computing archimedean sum...")
            def integrand(t):
                s = sigma0 + 1j * t
                kernel = mp.digamma(s/2) - mp.log(mp.pi)
                return kernel * mellin_transform(f, s, lim_u)
            
            arch_integral = mp.quad(integrand, [-T, T])
            arch_total = (arch_integral / (2j * mp.pi)).real
            
            A = prime_total + arch_total
            
            # Compute zero side
            print("Computing zero sum...")
            zero_total = mp.mpf('0')
            count = 0
            with open(zeros_file) as file:
                for line in file:
                    if count >= max_zeros:
                        break
                    gamma = mp.mpf(line.strip())
                    zero_total += mellin_transform(f, 1j * gamma, lim_u).real
                    count += 1
            
            Z = zero_total
            
            # Calculate results
            error = abs(A - Z)
            rel_error = error / abs(A) if abs(A) > 0 else float('inf')
            elapsed = time.time() - start_time
            
            result = {
                'P': P,
                'max_zeros': max_zeros,
                'precision': precision,
                'T': T,
                'A': float(A),
                'Z': float(Z),
                'error': float(error),
                'rel_error': float(rel_error),
                'time': elapsed,
                'success': error <= 1e-6
            }
            
            results.append(result)
            
            print(f"Results:")
            print(f"  Arithmetic side: {A}")
            print(f"  Zero side:       {Z}")
            print(f"  Error:           {error:.2e}")
            print(f"  Rel error:       {rel_error:.2e}")
            print(f"  Time:            {elapsed:.1f}s")
            print(f"  Target met:      {error <= 1e-6}")
            
        except Exception as e:
            print(f"ERROR: {e}")
            result = {
                'P': P,
                'max_zeros': max_zeros,
                'precision': precision,
                'error': float('inf'),
                'success': False,
                'time': float('inf')
            }
            results.append(result)
    
    # Summary
    print(f"\n{'='*60}")
    print("SUMMARY OF TESTS")
    print(f"{'='*60}")
    
    for r in results:
        status = "✅ PASS" if r['success'] else "❌ FAIL"
        if r['success']:
            print(f"{status} P={r['P']:4d} zeros={r['max_zeros']:4d} prec={r['precision']:2d} error={r['error']:.2e} time={r['time']:5.1f}s")
        else:
            print(f"{status} P={r['P']:4d} zeros={r['max_zeros']:4d} prec={r['precision']:2d} FAILED")
    
    # Find best result
    successful = [r for r in results if r['success']]
    if successful:
        best = min(successful, key=lambda x: x['error'])
        print(f"\n🎯 Best result: P={best['P']}, zeros={best['max_zeros']}, error={best['error']:.2e}")
        
        # Save best configuration
        save_best_config(best)
    else:
        print("\n❌ No configuration achieved target error ≤ 10^{-6}")
        
        # Try to find what might work
        all_errors = [r['error'] for r in results if r['error'] != float('inf')]
        if all_errors:
            min_error = min(all_errors)
            print(f"   Minimum error achieved: {min_error:.2e}")
            print(f"   Need to improve by factor: {min_error / 1e-6:.1f}")

def save_best_config(config):
    """Save the best configuration for future use."""
    os.makedirs('data', exist_ok=True)
    with open('data/best_config.txt', 'w') as f:
        f.write(f"# Best configuration for error ≤ 10^-6\n")
        f.write(f"P = {config['P']}\n")
        f.write(f"max_zeros = {config['max_zeros']}\n")
        f.write(f"precision = {config['precision']}\n")
        f.write(f"T = {config['T']}\n")
        f.write(f"# Achieved error: {config['error']:.2e}\n")
        f.write(f"# Computation time: {config['time']:.1f}s\n")
    
    print(f"💾 Best configuration saved to data/best_config.txt")

if __name__ == "__main__":
    test_validation_parameters()