"""
Debug version to understand the mathematical computation issues.
"""
import mpmath as mp
import sympy as sp

mp.mp.dps = 25

def fhat(f, s, lim):
    """Fourier-like transform with debug info."""
    try:
        result = mp.quad(lambda u: f(u) * mp.exp(s * u), [-lim, lim], maxdegree=10)
        return result
    except Exception as e:
        print(f"    ERROR in fhat: s={s}, lim={lim}, error={e}")
        return mp.mpf(0)

def debug_A_infty(f, sigma0=2.0, lim=3, T=10):
    """Debug version of A_infty."""
    print(f"  Debug A_∞: sigma0={sigma0}, lim={lim}, T={T}")
    
    def integrand(t):
        s = mp.mpc(sigma0, t)
        kernel = mp.digamma(s/2) - mp.log(mp.pi)
        fhat_val = fhat(f, s, lim)
        result = kernel * fhat_val
        return result
    
    print("    Computing main integral...")
    try:
        integ = mp.quad(integrand, [-T, T], maxdegree=6)
        integ_normalized = integ / (2 * mp.pi)
        print(f"    Raw integral: {integ}")
        print(f"    Normalized: {integ_normalized}")
    except Exception as e:
        print(f"    ERROR in integral: {e}")
        integ_normalized = mp.mpf(0)
    
    print("    Computing residue term...")
    try:
        res1 = fhat(f, mp.mpf(1), lim)
        print(f"    fhat(f, 1): {res1}")
        print(f"    Residue: {res1}")
    except Exception as e:
        print(f"    ERROR in residue: {e}")
        res1 = mp.mpf(0)
    
    result = integ_normalized - res1
    print(f"    A_∞ = {integ_normalized} - {res1} = {result}")
    
    return result

def debug_zero_sum(f, N=50, lim=3):
    """Debug version of zero sum with fewer zeros."""
    print(f"  Debug zero sum: N={N}, lim={lim}")
    
    s = mp.mpf(0)
    for n in range(1, min(N+1, 11)):  # Only first 10 for debugging
        try:
            rho = mp.zetazero(n) 
            gamma = mp.im(rho)
            print(f"    Zero #{n}: rho={rho}, gamma={gamma}")
            
            fhat_val = fhat(f, 1j * gamma, lim)
            contribution = fhat_val.real
            s += contribution
            
            print(f"      fhat(f, i*gamma): {fhat_val}")
            print(f"      Real part: {contribution}")
            print(f"      Running sum: {s}")
            
            if abs(contribution) > 1e10:
                print(f"      ⚠️  Large contribution detected!")
                break
                
        except Exception as e:
            print(f"      ERROR processing zero #{n}: {e}")
            break
    
    return s

def debug_simple_test():
    """Simple debug test."""
    print("🐛 Debug Test - Analyzing Mathematical Implementation")
    print("="*60)
    
    # Simple test function
    def f_simple(u):
        return mp.exp(-u**2/2) if abs(u) <= 2 else mp.mpf(0)
    
    print("\n1️⃣ Testing function properties...")
    print(f"  f(0) = {f_simple(0)}")
    print(f"  f(1) = {f_simple(1)}")
    print(f"  f(2) = {f_simple(2)}")
    print(f"  f(3) = {f_simple(3)}")
    
    print("\n2️⃣ Testing fhat transform...")
    fhat_0 = fhat(f_simple, 0, 2)
    fhat_1 = fhat(f_simple, 1, 2)
    fhat_i = fhat(f_simple, 1j, 2)
    
    print(f"  fhat(f, 0) = {fhat_0}")
    print(f"  fhat(f, 1) = {fhat_1}")  
    print(f"  fhat(f, i) = {fhat_i}")
    
    print("\n3️⃣ Testing A_infinity computation...")
    A_result = debug_A_infty(f_simple, sigma0=2.0, lim=2, T=5)
    print(f"  Final A_∞ = {A_result}")
    
    print("\n4️⃣ Testing zero sum (first few zeros)...")
    zero_result = debug_zero_sum(f_simple, N=5, lim=2)
    print(f"  Zero sum (5 terms) = {zero_result}")
    
    print("\n5️⃣ Error analysis...")
    if A_result != 0 and zero_result != 0:
        error = abs(A_result - zero_result)
        rel_error = error / abs(A_result)
        print(f"  Error = |{A_result} - {zero_result}| = {error}")
        print(f"  Relative error = {rel_error}")
    
    print("\n🎯 Debug completed.")

if __name__ == "__main__":
    debug_simple_test()