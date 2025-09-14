"""
Fixed validation script with proper complex number handling and mathematical corrections.
"""
import mpmath as mp
import sympy as sp
import csv
import os

mp.mp.dps = 30

def safe_float(x):
    """Safely convert mpmath number to float, handling complex."""
    if hasattr(x, 'real') and hasattr(x, 'imag'):
        # Complex number - take real part if imaginary is negligible
        if abs(x.imag) < 1e-10:
            return float(x.real)
        else:
            return float(abs(x))  # Use magnitude for complex
    else:
        return float(x)

def safe_format(x, precision=6):
    """Safely format mpmath number for display."""
    try:
        if hasattr(x, 'real') and hasattr(x, 'imag'):
            if abs(x.imag) < 1e-10:
                return f"{float(x.real):.{precision}f}"
            else:
                return f"{float(x.real):.{precision}f}+{float(x.imag):.{precision}f}j"
        else:
            return f"{float(x):.{precision}f}"
    except:
        return str(x)

def fhat(f, s, lim):
    """Fourier-like transform: ∫ f(u) * exp(s * u) du"""
    return mp.quad(lambda u: f(u) * mp.exp(s * u), [-lim, lim], maxdegree=8)

def prime_sum(f, P=1000, K=50):
    """Compute prime sum."""
    s = mp.mpf(0)
    primes = list(sp.primerange(2, P + 1))
    for p in primes:
        lp = mp.log(p)
        for k in range(1, K+1):
            s += lp * f(k * lp)
    return s

def A_infty(f, sigma0=2.0, lim=3, T=50):
    """Archimedean sum with residue correction."""
    def integrand(t):
        s = mp.mpc(sigma0, t)
        return (mp.digamma(s/2) - mp.log(mp.pi)) * fhat(f, s, lim)
    
    # Main integral
    integ = mp.quad(integrand, [-T, T], maxdegree=6) / (2 * mp.pi)
    
    # Residue term
    res1 = fhat(f, mp.mpf(1), lim)
    
    return integ - res1

def zero_sum_builtin(f, N=2000, lim=3):
    """Zero sum using mpmath's zetazeros."""
    s = mp.mpf(0)
    for n in range(1, N+1):
        try:
            rho = mp.zetazero(n)
            gamma = mp.im(rho)
            fhat_val = fhat(f, 1j * gamma, lim)
            s += fhat_val.real
        except Exception as e:
            print(f"Warning: Error with zero #{n}: {e}")
            break
    return s

def simple_validation_test():
    """Quick validation test with very reduced parameters."""
    print("🧪 Simple Validation Test")
    print("="*50)
    
    # Minimal parameters for speed
    P_test, K_test, N_test, T_test = 50, 5, 50, 10
    
    # Simple test function
    def f_test(u): 
        return mp.exp(-u**2) if abs(u) <= 2 else mp.mpf(0)
    
    print("Computing components...")
    
    try:
        ps = prime_sum(f_test, P_test, K_test)
        print(f"Prime sum: {safe_format(ps)}")
        
        ain = A_infty(f_test, sigma0=2.0, lim=2, T=T_test)
        print(f"A_infty: {safe_format(ain)}")
        
        # Take real part for arithmetic total
        arithmetic_real = safe_float(ps) + safe_float(ain.real if hasattr(ain, 'real') else ain)
        print(f"Arithmetic total: {arithmetic_real:.6f}")
        
        zs = zero_sum_builtin(f_test, N_test, lim=2)
        print(f"Zero sum: {safe_format(zs)}")
        
        error = abs(arithmetic_real - safe_float(zs))
        print(f"Error: {error:.2e}")
        print(f"Success: {error < 1e-5}")
        
        return {
            'prime_sum': safe_float(ps),
            'archimedean_sum': safe_float(ain.real if hasattr(ain, 'real') else ain),
            'arithmetic_total': arithmetic_real,
            'zero_sum': safe_float(zs),
            'absolute_error': error,
            'success': error < 1e-5
        }
        
    except Exception as e:
        print(f"Error in computation: {e}")
        return None

def main_validation():
    """Main validation with proper error handling."""
    print("🔬 Riemann Hypothesis Validation (Fixed Version)")
    print("="*60)
    
    # Test functions with appropriate limits
    test_cases = [
        ('f1', lambda u: mp.exp(-u**2/2) if abs(u) <= 3 else mp.mpf(0), 3),
        ('f2', lambda u: mp.exp(-u**2) if abs(u) <= 2 else mp.mpf(0), 2),
        ('f3', lambda u: (1 - u**2/4)**2 if abs(u) <= 2 else mp.mpf(0), 2)
    ]
    
    # Reduced parameters for testing
    P, K, N, T = 100, 10, 200, 15
    
    results = []
    
    for fname, f, lim in test_cases:
        print(f"\n📊 Testing {fname} (limit={lim})...")
        
        try:
            ps = prime_sum(f, P, K)
            ain = A_infty(f, sigma0=2.0, lim=lim, T=T)  
            zs = zero_sum_builtin(f, N, lim=lim)
            
            # Handle complex results properly
            ps_val = safe_float(ps)
            ain_val = safe_float(ain.real if hasattr(ain, 'real') else ain)
            arithmetic_total = ps_val + ain_val
            zs_val = safe_float(zs)
            
            error = abs(arithmetic_total - zs_val)
            rel_error = error / abs(arithmetic_total) if arithmetic_total != 0 else float('inf')
            success = error < 1e-5
            
            print(f"  Prime sum: {ps_val:.6f}")
            print(f"  A_∞: {ain_val:.6f}")
            print(f"  Arithmetic: {arithmetic_total:.6f}")  
            print(f"  Zero sum: {zs_val:.6f}")
            print(f"  Error: {error:.2e}")
            print(f"  Status: {'✅ SUCCESS' if success else '❌ FAIL'}")
            
            results.append({
                'function': fname,
                'prime_sum': ps_val,
                'archimedean_sum': ain_val,
                'arithmetic_total': arithmetic_total,
                'zero_sum': zs_val,
                'absolute_error': error,
                'relative_error': rel_error,
                'success': success
            })
            
        except Exception as e:
            print(f"  ❌ Error: {e}")
            results.append({
                'function': fname,
                'prime_sum': 0.0,
                'archimedean_sum': 0.0, 
                'arithmetic_total': 0.0,
                'zero_sum': 0.0,
                'absolute_error': float('inf'),
                'relative_error': float('inf'),
                'success': False
            })
    
    # Export results
    os.makedirs('data', exist_ok=True)
    with open('data/validation_output.csv', 'w', newline='') as csvfile:
        fieldnames = ['function', 'prime_sum', 'archimedean_sum', 'arithmetic_total',
                     'zero_sum', 'absolute_error', 'relative_error', 'success']
        writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
        writer.writeheader()
        for result in results:
            writer.writerow(result)
    
    print(f"\n📄 Results exported to data/validation_output.csv")
    
    # Summary
    successful = sum(1 for r in results if r['success'])
    total = len(results)
    print(f"\n🎯 FINAL: {successful}/{total} functions successful")
    
    return successful == total

if __name__ == "__main__":
    import sys
    
    if '--simple' in sys.argv:
        result = simple_validation_test()
    else:
        success = main_validation()
        
        # Generate HTML report
        try:
            from generate_report import generate_html_report
            generate_html_report('data/validation_output.csv', 'docs/validation.html')
        except ImportError:
            print("Could not generate HTML report")
        
        if not success:
            sys.exit(1)