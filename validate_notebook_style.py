"""
Fixed validation script that matches the notebook's mathematical approach.
This resolves the Archimedean sum computation issues.
"""
import mpmath as mp
import sympy as sp
import csv
import os

mp.mp.dps = 30  # Precision suitable for validation

# Parameters as per specification
PARAMS = {
    'delta': 0.01,
    'P': 1000,
    'K': 50,
    'N_Xi': 2000,
    'sigma0': 2.0,
    'T': 50
}

# Test parameters (faster)
TEST_PARAMS = {
    'delta': 0.01,  
    'P': 100,
    'K': 10,
    'N_Xi': 200,
    'sigma0': 2.0,
    'T': 20
}

def fhat(f, s, lim):
    """Fourier-like transform: ∫ f(u) * exp(s * u) du"""
    return mp.quad(lambda u: f(u) * mp.exp(s * u), [-lim, lim], maxdegree=10)

def prime_sum(f, P=1000, K=50):
    """Compute prime sum as in notebook."""
    s = mp.mpf(0)
    primes = list(sp.primerange(2, 7919))[:P]  # Match notebook approach
    for p in primes:
        lp = mp.log(p)
        for k in range(1, K+1):
            s += lp * f(k * lp)
    return s

def A_infty(f, sigma0=2.0, lim=3, T=50):
    """Archimedean sum with correction term (as in notebook)."""
    def integrand(t):
        s = mp.mpc(sigma0, t)
        return (mp.digamma(s/2) - mp.log(mp.pi)) * fhat(f, s, lim)
    
    # Main integral
    integ = mp.quad(integrand, [-T, T], maxdegree=10) / (2 * mp.pi)
    
    # Correction/residue term
    res1 = fhat(f, mp.mpf(1), lim) / mp.mpf(1)
    
    return integ - res1

def zero_sum_builtin(f, N=2000, lim=3):
    """Zero sum using mpmath's built-in zetazeros (as in notebook)."""
    s = mp.mpf(0)
    for n in range(1, N+1):
        rho = mp.zetazero(n)
        s += fhat(f, mp.im(rho), lim).real
    return s

def zero_sum_file(f, filename, lim=3, N=2000):
    """Zero sum using zeros from file."""
    s = mp.mpf(0)
    count = 0
    
    if not os.path.exists(filename):
        raise FileNotFoundError(f"Zeros file not found: {filename}")
        
    with open(filename) as file:
        for line in file:
            if count >= N:
                break
            try:
                gamma = mp.mpf(line.strip())
                s += fhat(f, 1j * gamma, lim).real
                count += 1
            except ValueError:
                continue
                
    return s

def validate_notebook_style(use_test_params=True, use_file_zeros=False):
    """Validate using the notebook's exact approach."""
    
    params = TEST_PARAMS if use_test_params else PARAMS
    param_type = "TEST" if use_test_params else "PRODUCTION"
    zero_type = "FILE" if use_file_zeros else "BUILTIN"
    
    print(f"🔬 Validación Notebook-Style ({param_type} params, {zero_type} zeros)")
    print(f"Parámetros: P={params['P']}, K={params['K']}, N_Ξ={params['N_Xi']}, σ₀={params['sigma0']}, T={params['T']}")
    print("=" * 70)
    
    # Test functions with their limits (as in notebook)
    test_cases = [
        ('f1', lambda u: mp.exp(-u**2/2) if abs(u) <= 3 else mp.mpf(0), 3),
        ('f2', lambda u: mp.exp(-u**2) if abs(u) <= 2 else mp.mpf(0), 2), 
        ('f3', lambda u: (1 - u**2/4)**2 if abs(u) <= 2 else mp.mpf(0), 2)
    ]
    
    results = []
    
    for fname, f, lim in test_cases:
        print(f"\n📊 Validando función {fname} (lim={lim})...")
        
        try:
            # Compute prime sum
            ps = prime_sum(f, params['P'], params['K'])
            print(f"  Prime sum: {ps}")
            
            # Compute A_infinity  
            ain = A_infty(f, params['sigma0'], lim, params['T'])
            print(f"  A_∞: {ain}")
            
            # Total arithmetic side
            tot = ps + ain
            print(f"  Total arithmetic: {tot}")
            
            # Compute zero sum
            if use_file_zeros:
                zs = zero_sum_file(f, 'zeros/zeros_t1e8.txt', lim, params['N_Xi'])
            else:
                zs = zero_sum_builtin(f, params['N_Xi'], lim)
            print(f"  Zero sum: {zs}")
            
            # Error analysis
            err = abs(tot - zs)
            rel_err = err / abs(tot) if abs(tot) > 0 else float('inf')
            success = err < 1e-5
            
            print(f"  Error absoluto: {err:.2e}")
            print(f"  Error relativo: {rel_err:.2e}")
            print(f"  {'✅ ÉXITO' if success else '❌ FALLO'}")
            
            results.append({
                'function': fname,
                'prime_sum': float(ps),
                'archimedean_sum': float(ain),
                'arithmetic_total': float(tot),
                'zero_sum': float(zs),
                'absolute_error': float(err),
                'relative_error': float(rel_err),
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
    
    print(f"\n📄 Resultados exportados a: data/validation_output.csv")
    
    # Summary
    successful = sum(1 for r in results if r['success'])
    total = len(results)
    print(f"\n🎯 RESUMEN: {successful}/{total} funciones exitosas")
    
    return {
        'results': results,
        'summary': {
            'successful': successful,
            'total': total,
            'all_success': successful == total
        }
    }

if __name__ == "__main__":
    import sys
    
    # Parse command line args
    use_production = '--production' in sys.argv
    use_file_zeros = '--file-zeros' in sys.argv
    
    result = validate_notebook_style(
        use_test_params=not use_production,
        use_file_zeros=use_file_zeros
    )
    
    # Generate HTML report
    if result['summary']['total'] > 0:
        from generate_report import generate_html_report
        generate_html_report('data/validation_output.csv', 'docs/validation.html')
        
    # Exit with error if validation failed
    if not result['summary']['all_success']:
        sys.exit(1)