"""
Efficient validation for achieving 10^{-6} error using file-based zeros
"""

import mpmath as mp
import sympy as sp
import time
import os

def simple_test_function(u):
    """Simple smooth test function"""
    if abs(u) <= 1:
        return mp.exp(-1 / (1 - u**2))
    else:
        return mp.mpf(0)

def fhat(f, s, lim):
    """Mellin transform"""
    return mp.quad(lambda u: f(u) * mp.exp(s * u), [-lim, lim], maxdegree=8)

def compute_zero_side_from_file(f, filename, max_zeros, lim):
    """Compute zero side using file data efficiently"""
    zero_sum = mp.mpf(0)
    count = 0
    
    print(f"  Computing zero sum from file with up to {max_zeros} zeros...")
    start_time = time.time()
    
    with open(filename) as file:
        for line in file:
            if count >= max_zeros:
                break
            
            gamma = mp.mpf(line.strip())
            zero_contribution = fhat(f, 1j * gamma, lim).real
            zero_sum += zero_contribution
            count += 1
            
            # Progress tracking
            if count % 5000 == 0:
                elapsed = time.time() - start_time
                rate = count / elapsed if elapsed > 0 else 0
                eta = (max_zeros - count) / rate if rate > 0 else 0
                print(f"    Processed {count}/{max_zeros} zeros ({rate:.1f} zeros/s, ETA: {eta:.1f}s)")
    
    elapsed = time.time() - start_time
    print(f"  Zero sum completed: {count} zeros in {elapsed:.1f}s")
    return zero_sum

def efficient_validation():
    """Efficient validation using file-based zeros"""
    
    # Optimized parameters for speed vs precision
    mp.mp.dps = 20  # Reduced precision for speed
    f = simple_test_function
    lim = 1.5       # Reduced integration limit
    P = 500         # Reduced primes for speed
    T = 15          # Reduced archimedean parameter
    
    print("🚀 Efficient validation for 10^{-6} target")
    print(f"Parameters: P={P}, T={T}, lim={lim}, precision={mp.mp.dps}")
    
    zeros_file = 'zeros/zeros_t1e8.txt'
    if not os.path.exists(zeros_file):
        print(f"❌ Zeros file not found: {zeros_file}")
        return False
    
    # Check file size
    with open(zeros_file) as zeros_f:
        total_zeros = sum(1 for _ in zeros_f)
    print(f"Available zeros in file: {total_zeros}")
    
    # Compute arithmetic side once
    print("\nComputing arithmetic side...")
    start_time = time.time()
    
    # Prime sum
    prime_sum = mp.mpf(0)
    primes = list(sp.primerange(2, P))
    for p in primes:
        lp = mp.log(p)
        prime_sum += lp * f(lp)
    
    # Archimedean part
    def integrand(t):
        s = mp.mpc(2.0, t)
        return (mp.digamma(s/2) - mp.log(mp.pi)) * fhat(f, s, lim)
    
    arch_integral = mp.quad(integrand, [-T, T], maxdegree=8) / (2 * mp.pi)
    residue = fhat(f, mp.mpf(1), lim)
    arch_sum = arch_integral - residue
    
    A = prime_sum + arch_sum.real
    arith_time = time.time() - start_time
    
    print(f"Arithmetic side: {float(A):.6f} (computed in {arith_time:.1f}s)")
    
    # Test with exponentially increasing zero counts
    zero_counts = [1000, 5000, 10000, 25000, 50000, 100000]
    
    for N_zeros in zero_counts:
        if N_zeros > total_zeros:
            print(f"Skipping {N_zeros} (only {total_zeros} available)")
            continue
        
        print(f"\n{'='*50}")
        print(f"Testing with {N_zeros} zeros")
        print(f"{'='*50}")
        
        # Compute zero side
        Z = compute_zero_side_from_file(f, zeros_file, N_zeros, lim)
        
        # Results
        error = abs(A - Z)
        rel_error = float(error) / abs(float(A)) if A != 0 else float('inf')
        
        print(f"\nResults:")
        print(f"  Arithmetic side: {float(A):.6f}")
        print(f"  Zero side:       {float(Z):.6f}")
        print(f"  Error:           {float(error):.2e}")
        print(f"  Relative error:  {rel_error:.2e}")
        
        if error <= 1e-6:
            print(f"  🎯 SUCCESS: Target error achieved with {N_zeros} zeros!")
            
            # Save successful result
            save_successful_result(A, Z, error, N_zeros, P, T, lim)
            return True
        else:
            improvement_needed = float(error) / 1e-6
            print(f"  ⚠️  Need {improvement_needed:.1f}x improvement")
            
            # Estimate convergence
            zero_contribution_avg = float(Z) / N_zeros if N_zeros > 0 else 0
            estimated_zeros_needed = abs(float(A - Z)) / abs(zero_contribution_avg) if zero_contribution_avg != 0 else float('inf')
            
            if estimated_zeros_needed < total_zeros:
                print(f"  📈 Estimated zeros needed: ~{int(estimated_zeros_needed)}")
            else:
                print(f"  ⚠️  May need more zeros than available ({total_zeros})")
        
        # Check if we should continue
        if N_zeros >= total_zeros * 0.8:  # Used most available zeros
            print(f"\n⚠️  Used most available zeros. Consider higher precision or different function.")
            break
    
    print(f"\n❌ Target precision not achieved with available zeros")
    return False

def save_successful_result(A, Z, error, N_zeros, P, T, lim):
    """Save successful validation parameters"""
    os.makedirs('data', exist_ok=True)
    
    with open('data/successful_validation.csv', 'w') as f:
        f.write("parameter,value\n")
        f.write(f"arithmetic_side,{A}\n")
        f.write(f"zero_side,{Z}\n")
        f.write(f"absolute_error,{error}\n")
        f.write(f"N_zeros,{N_zeros}\n")
        f.write(f"P,{P}\n")
        f.write(f"T,{T}\n")
        f.write(f"lim,{lim}\n")
        f.write(f"precision,{mp.mp.dps}\n")
        f.write(f"target_achieved,True\n")
    
    print(f"💾 Successful parameters saved to data/successful_validation.csv")

if __name__ == "__main__":
    success = efficient_validation()
    
    if success:
        print("\n🎉 SUCCESS: Achieved target error ≤ 10^{-6}!")
        exit(0)
    else:
        print("\n📊 Target not yet achieved, but framework is working correctly")
        exit(1)