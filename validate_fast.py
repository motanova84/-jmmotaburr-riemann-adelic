import mpmath as mp
import sympy as sp
import csv
import os
from utils.mellin import mellin_transform

mp.mp.dps = 25  # Reduced precision for faster computation

# Production parameters (as per specification)
PROD_PARAMS = {
    'delta': 0.01,
    'P': 1000,
    'K': 50,
    'N_Xi': 2000,
    'sigma0': 2.0,
    'T': 50,
    'lim_u': 5.0
}

# Test parameters (faster for development/testing)
TEST_PARAMS = {
    'delta': 0.01,
    'P': 100,
    'K': 10, 
    'N_Xi': 200,
    'sigma0': 2.0,
    'T': 15,
    'lim_u': 3.0
}

def prime_sum(f, P, K):
    """Compute prime sum term."""
    total = mp.mpf('0')
    primes = list(sp.primerange(2, P + 1))
    for p in primes:
        lp = mp.log(p)
        for k in range(1, K + 1):
            total += lp * f(k * lp)
    return total

def archimedean_sum(f, sigma0, T, lim_u):
    """Compute Archimedean sum term."""
    def integrand(t):
        s = sigma0 + 1j * t
        kernel = mp.digamma(s / 2) - mp.log(mp.pi)
        return kernel * mellin_transform(f, s, lim_u)
    
    integral, err = mp.quad(integrand, [-T, T], error=True, maxdegree=6)
    return (integral / (2j * mp.pi)).real

def zero_sum(f, filename, lim_u=5, N_Xi=2000):
    """Compute zero sum term."""
    total = mp.mpf('0')
    count = 0
    
    if not os.path.exists(filename):
        raise FileNotFoundError(f"Zeros file not found: {filename}")
        
    with open(filename) as file:
        for line in file:
            if count >= N_Xi:
                break
            try:
                gamma = mp.mpf(line.strip())
                fhat_val = mellin_transform(f, 1j * gamma, lim_u)
                total += fhat_val.real
                count += 1
            except ValueError:
                continue  # Skip invalid lines
                
    print(f"  Processed {count} zeros")
    return total

def validate_riemann_formula(use_test_params=True, output_csv=True, verbose=True):
    """
    Main validation function for Riemann hypothesis.
    
    Args:
        use_test_params: If True, use faster test parameters. If False, use full production parameters.
        output_csv: Whether to output results to CSV
        verbose: Whether to print detailed output
        
    Returns:
        dict: Validation results
    """
    params = TEST_PARAMS if use_test_params else PROD_PARAMS
    
    if verbose:
        param_type = "TEST" if use_test_params else "PRODUCTION"
        print(f"🔬 Validación de Fórmula Explícita para Hipótesis de Riemann ({param_type})")
        print(f"Parámetros: δ={params['delta']}, P={params['P']}, K={params['K']}, N_Ξ={params['N_Xi']}, σ₀={params['sigma0']}, T={params['T']}")
        print("=" * 70)
    
    # Test functions
    def f1(u): return mp.exp(-u**2/2) if abs(u) <= 3 else mp.mpf(0)
    def f2(u): return mp.exp(-u**2) if abs(u) <= 2 else mp.mpf(0)
    def f3(u): return (1 - u**2/4)**2 if abs(u) <= 2 else mp.mpf(0)
    
    functions = [('f1', f1), ('f2', f2), ('f3', f3)]
    results = []
    
    for fname, f in functions:
        if verbose:
            print(f"\n📊 Validando función {fname}...")
        
        try:
            # Compute arithmetic side
            if verbose:
                print("  Calculando lado aritmético...")
            prime_term = prime_sum(f, params['P'], params['K'])
            arch_term = archimedean_sum(f, params['sigma0'], params['T'], params['lim_u'])
            A = prime_term + arch_term
            
            # Compute zero side  
            if verbose:
                print("  Calculando lado de ceros...")
            Z = zero_sum(f, 'zeros/zeros_t1e8.txt', params['lim_u'], params['N_Xi'])
            
            # Calculate errors
            error = abs(A - Z)
            rel_error = error / abs(A) if abs(A) > 0 else float('inf')
            success = error < 1e-5
            
            if verbose:
                print(f"  PrimeSum({fname}) = {prime_term}")
                print(f"  A_∞({fname}) = {arch_term}")
                print(f"  Aritmético Total: {A}")
                print(f"  Zero Sum: {Z}")
                print(f"  Error absoluto: {error}")
                print(f"  Error relativo: {rel_error}")
                print(f"  {'✅ ÉXITO' if success else '❌ FALLO (error > 1e-5)'}")
            
            results.append({
                'function': fname,
                'prime_sum': float(prime_term),
                'archimedean_sum': float(arch_term),
                'arithmetic_total': float(A),
                'zero_sum': float(Z),
                'absolute_error': float(error),
                'relative_error': float(rel_error),
                'success': success
            })
            
        except Exception as e:
            if verbose:
                print(f"  ❌ Error procesando {fname}: {e}")
            results.append({
                'function': fname,
                'prime_sum': 0.0,
                'archimedean_sum': 0.0,
                'arithmetic_total': 0.0,
                'zero_sum': 0.0,
                'absolute_error': float('inf'),
                'relative_error': float('inf'),
                'success': False,
                'error': str(e)
            })
    
    if output_csv:
        # Export to CSV
        os.makedirs('data', exist_ok=True)
        with open('data/validation_output.csv', 'w', newline='') as csvfile:
            fieldnames = ['function', 'prime_sum', 'archimedean_sum', 'arithmetic_total',
                         'zero_sum', 'absolute_error', 'relative_error', 'success']
            writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
            writer.writeheader()
            for result in results:
                # Remove error field for CSV if it exists
                csv_result = {k: v for k, v in result.items() if k != 'error'}
                writer.writerow(csv_result)
        
        if verbose:
            print(f"\n📄 Resultados exportados a: data/validation_output.csv")
    
    # Final summary
    successful_count = sum(1 for r in results if r['success'])
    total_count = len(results)
    all_success = successful_count == total_count
    
    if verbose:
        print(f"\n🎯 VALIDACIÓN FINAL: {successful_count}/{total_count} funciones exitosas")
        print(f"{'✅ TODAS LAS FUNCIONES EXITOSAS' if all_success else '❌ ALGUNAS FUNCIONES FALLARON'}")
    
    return {
        'results': results,
        'summary': {
            'successful': successful_count,
            'total': total_count,
            'all_success': all_success,
            'parameters': params
        }
    }

if __name__ == "__main__":
    import sys
    
    # Check for command line arguments
    use_production = '--production' in sys.argv
    quiet = '--quiet' in sys.argv
    
    validation_result = validate_riemann_formula(
        use_test_params=not use_production,
        verbose=not quiet
    )
    
    # Generate HTML report if validation ran
    if validation_result['summary']['total'] > 0:
        from generate_report import generate_html_report
        generate_html_report('data/validation_output.csv', 'docs/validation.html')
    
    # Exit with error code if validation failed
    if not validation_result['summary']['all_success']:
        sys.exit(1)