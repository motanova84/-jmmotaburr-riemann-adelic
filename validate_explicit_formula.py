"""
🚀 Copilot Objective:
Please ensure this script `validate_explicit_formula.py` runs flawlessly and confirms the mathematical claim:
- Input parameters should match those described in the associated paper or README
- Modify as needed to improve:
  - Accuracy (increase integration limits, use more zeros, refine discretization)
  - Performance (optimize loops, use numpy or mp math if helpful)
  - Robustness (add exception handling, check input validity)
  - Clarity (log intermediate values, write summary of results)
  - Symbolic coherence (annotate with references to frequency 141.7001 Hz, JMMB Ψ✧ signature, etc.)

✧ Goal: Confirm the spectral/arithmetic duality explicitly (e.g. PrimeSum(f) + A_∞(f) = Σρ f̂(ρ))
✧ Output: Print a clear YES/NO about whether the formula holds within tolerance (e.g. < 1e-6)
✧ Bonus: Suggest new test functions f if current results are unstable

🔬 Mathematical Context:
This validates the Weil-type explicit formula for canonical function D(s) via adelic flows:
- Arithmetic side: Prime sum + Archimedean contributions  
- Spectral side: Sum over nontrivial zeros of zeta function
- Expected relationship: PrimeSum(f) + A_∞(f) ≈ Σρ f̂(ρ) within numerical precision
- Frequency signature: 141.7001 Hz corresponds to JMMB Ψ✧ mathematical resonance
- Validation confirms José Manuel Mota Burruezo's S-finite adelic proof framework

🧠 Copilot Assistant Instructions:
- Analyze convergence patterns and suggest parameter adjustments
- Monitor intermediate calculations for numerical stability
- Recommend test function improvements if error exceeds tolerance
- Provide clear diagnostic output for mathematical verification
- Optimize computational efficiency while maintaining precision
"""

import mpmath as mp
import sympy as sp
import sys
import os
import time
import logging
from utils.mellin import truncated_gaussian, mellin_transform

# Configure logging for detailed diagnostics
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler('logs/validation.log'),
        logging.StreamHandler()
    ]
)
logger = logging.getLogger(__name__)

# Ensure logs directory exists
os.makedirs('logs', exist_ok=True)

# Mathematical precision configuration
mp.mp.dps = 25  # Increased precision for better accuracy

# Default experimental parameters (can be overridden by command line)
DEFAULT_PARAMS = {
    'P': 1000,           # Maximum prime
    'K': 5,              # Maximum powers per prime  
    'sigma0': 2.0,       # Integration contour
    'T': 50,             # Integration limit
    'lim_u': 5.0,        # Support limit for test functions
    'tolerance': 1e-6,   # Validation tolerance
    'frequency_signature': 141.7001  # JMMB Ψ✧ signature Hz
}

def validate_parameters(P, K, T, max_zeros, tolerance):
    """Validate input parameters for mathematical soundness."""
    errors = []
    
    if P <= 0 or P > 1000000:
        errors.append(f"Prime limit P={P} should be between 1 and 1,000,000")
    if K <= 0 or K > 100:
        errors.append(f"Power limit K={K} should be between 1 and 100")
    if T <= 0 or T > 1000:
        errors.append(f"Integration limit T={T} should be between 1 and 1000")
    if max_zeros <= 0 or max_zeros > 100000:
        errors.append(f"Zero count max_zeros={max_zeros} should be between 1 and 100,000")
    if tolerance <= 0 or tolerance >= 1:
        errors.append(f"Tolerance={tolerance} should be between 0 and 1")
    
    return errors

def log_computation_progress(stage, value=None, error=None):
    """Log computation progress with mathematical context."""
    if error:
        logger.error(f"❌ {stage}: {error}")
    elif value is not None:
        logger.info(f"✓ {stage}: {value}")
    else:
        logger.info(f"🔄 {stage}...")

def prime_sum(f, P, K):
    """Compute prime sum with enhanced logging and error handling."""
    log_computation_progress("Computing prime sum", f"P={P}, K={K}")
    
    try:
        total = mp.mpf('0')
        prime_count = 0
        
        # Generate all primes up to P with progress tracking
        primes = list(sp.primerange(2, P + 1))
        logger.info(f"📊 Generated {len(primes)} primes up to {P}")
        
        for p in primes:
            lp = mp.log(p)
            prime_contribution = mp.mpf('0')
            
            for k in range(1, K + 1):
                term = lp * f(k * lp)
                prime_contribution += term
                total += term
            
            prime_count += 1
            if prime_count % 100 == 0:
                logger.info(f"  Processed {prime_count}/{len(primes)} primes")
        
        logger.info(f"✅ Prime sum computed: {total}")
        return total
        
    except Exception as e:
        log_computation_progress("Prime sum computation", error=str(e))
        raise

def archimedean_sum(f, sigma0, T, lim_u):
    """Compute Archimedean sum with enhanced precision and logging."""
    log_computation_progress("Computing Archimedean sum", f"σ₀={sigma0}, T={T}")
    
    try:
        def integrand(t):
            s = sigma0 + 1j * t
            kernel = mp.digamma(s / 2) - mp.log(mp.pi)
            mellin_val = mellin_transform(f, s, lim_u)
            return kernel * mellin_val
        
        # Use higher precision integration
        integral, error = mp.quad(integrand, [-T, T], error=True, maxdegree=15)
        result = (integral / (2j * mp.pi)).real
        
        logger.info(f"📐 Integration error estimate: {error}")
        logger.info(f"✅ Archimedean sum computed: {result}")
        
        return result
        
    except Exception as e:
        log_computation_progress("Archimedean sum computation", error=str(e))
        raise

def zero_sum(f, filename, lim_u=5):
    """Compute zero sum with enhanced error handling."""
    log_computation_progress("Computing zero sum (all zeros)")
    
    try:
        total = mp.mpf('0')
        zero_count = 0
        
        with open(filename) as file:
            for line in file:
                gamma = mp.mpf(line.strip())
                contribution = mellin_transform(f, 1j * gamma, lim_u).real
                total += contribution
                zero_count += 1
                
                if zero_count % 500 == 0:
                    logger.info(f"  Processed {zero_count} zeros")
        
        logger.info(f"✅ Zero sum computed using {zero_count} zeros: {total}")
        return total
        
    except Exception as e:
        log_computation_progress("Zero sum computation", error=str(e))
        raise

def zero_sum_limited(f, filename, max_zeros, lim_u=5):
    """Compute zero sum using only first max_zeros from file with enhanced logging."""
    log_computation_progress("Computing zero sum (limited)", f"max_zeros={max_zeros}")
    
    try:
        total = mp.mpf('0')
        count = 0
        contributions = []
        
        with open(filename) as file:
            for line in file:
                if count >= max_zeros:
                    break
                    
                gamma = mp.mpf(line.strip())
                contribution = mellin_transform(f, 1j * gamma, lim_u).real
                total += contribution
                contributions.append(float(contribution))
                count += 1
                
                if count % 100 == 0:
                    logger.info(f"  Processed {count}/{max_zeros} zeros")
        
        # Analyze convergence
        if len(contributions) > 10:
            recent_avg = sum(contributions[-10:]) / 10
            logger.info(f"📈 Average of last 10 contributions: {recent_avg}")
        
        logger.info(f"✅ Zero sum computed using {count} zeros: {total}")
        return total
        
    except Exception as e:
        log_computation_progress("Zero sum computation", error=str(e))
        raise

def validate_explicit_formula(arithmetic_side, zero_side, tolerance, frequency_sig):
    """Validate the explicit formula with clear YES/NO output."""
    error = abs(arithmetic_side - zero_side)
    relative_error = error / abs(arithmetic_side) if abs(arithmetic_side) > 0 else float('inf')
    
    # Mathematical validation
    is_valid = error < tolerance
    
    print("\n" + "="*80)
    print("🔬 RIEMANN HYPOTHESIS EXPLICIT FORMULA VALIDATION")
    print("="*80)
    print(f"📐 Arithmetic Side (Primes + Archimedean): {arithmetic_side}")
    print(f"🌊 Spectral Side (Zero Sum):                {zero_side}")
    print(f"📊 Absolute Error:                          {error}")
    print(f"📈 Relative Error:                          {float(relative_error):.2e}")
    print(f"🎯 Tolerance Threshold:                     {tolerance}")
    print(f"🔊 JMMB Ψ✧ Frequency Signature:            {frequency_sig} Hz")
    print("-"*80)
    
    if is_valid:
        print("✅ VALIDATION RESULT: YES")
        print("🎉 The explicit formula holds within the specified tolerance!")
        print("🧮 Spectral/arithmetic duality CONFIRMED")
        result_emoji = "✅"
        result_text = "PASS"
    else:
        print("❌ VALIDATION RESULT: NO") 
        print("⚠️  The explicit formula does NOT hold within tolerance")
        print("🔧 Consider adjusting parameters or test functions")
        result_emoji = "❌"
        result_text = "FAIL"
    
    print("="*80)
    
    # Suggest improvements if validation fails
    if not is_valid:
        suggest_improvements(float(error), float(relative_error), tolerance)
    
    return {
        'is_valid': is_valid,
        'error': float(error),
        'relative_error': float(relative_error),
        'result_emoji': result_emoji,
        'result_text': result_text
    }

def suggest_improvements(error, relative_error, tolerance):
    """Suggest parameter improvements based on validation results."""
    print("\n🔧 COPILOT SUGGESTIONS FOR IMPROVEMENT:")
    print("-"*50)
    
    if relative_error > 0.1:
        print("• Error > 10%: Consider increasing precision (mp.dps)")
        print("• Try larger integration limits (T parameter)")
        print("• Use more zeros for zero sum computation")
    
    if error > tolerance * 1000:
        print("• Very large error: Check test function properties")
        print("• Consider different test functions (truncated_gaussian variants)")
        print("• Verify zero file integrity and format")
    
    print("• Suggested test functions to try:")
    print("  - f(u) = exp(-u²/4) * (1 + cos(πu/2)) for |u| ≤ 2")  
    print("  - f(u) = (1 - u²/9)² for |u| ≤ 3")
    print("  - f(u) = exp(-|u|) for |u| ≤ 5")
    
    print("• Parameter optimization suggestions:")
    print(f"  - Increase precision: mp.dps = 30-50")
    print(f"  - Larger integration: T = 100-200") 
    print(f"  - More zeros: max_zeros = 5000-10000")
    print(f"  - Smaller support: lim_u = 3.0-4.0")
    print("-"*50)

if __name__ == "__main__":
    import argparse
    import time
    
    start_time = time.time()
    
    # Enhanced argument parser
    parser = argparse.ArgumentParser(
        description='🔬 Validate Riemann Hypothesis Explicit Formula - JMMB Ψ✧ Framework',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python validate_explicit_formula.py --max_primes 1000 --max_zeros 2000
  python validate_explicit_formula.py --tolerance 1e-8 --precision 30
  python validate_explicit_formula.py --fast-test  # Quick validation
        """
    )
    
    parser.add_argument('--max_primes', type=int, default=DEFAULT_PARAMS['P'], 
                       help=f'Maximum prime P to use (default: {DEFAULT_PARAMS["P"]})')
    parser.add_argument('--max_zeros', type=int, default=2000,
                       help='Maximum number of zeros to use (default: 2000)')
    parser.add_argument('--tolerance', type=float, default=DEFAULT_PARAMS['tolerance'],
                       help=f'Validation tolerance (default: {DEFAULT_PARAMS["tolerance"]})')
    parser.add_argument('--precision', type=int, default=25,
                       help='Decimal precision for mpmath (default: 25)')
    parser.add_argument('--integration_limit', type=float, default=DEFAULT_PARAMS['T'],
                       help=f'Integration limit T (default: {DEFAULT_PARAMS["T"]})')
    parser.add_argument('--support_limit', type=float, default=DEFAULT_PARAMS['lim_u'],
                       help=f'Test function support limit (default: {DEFAULT_PARAMS["lim_u"]})')
    parser.add_argument('--fast-test', action='store_true',
                       help='Run quick test with reduced parameters')
    parser.add_argument('--verbose', action='store_true',
                       help='Enable verbose logging')
    parser.add_argument('--export-html', action='store_true',
                       help='Export results to HTML report')
    
    args = parser.parse_args()
    
    # Configure precision
    mp.mp.dps = args.precision
    logger.info(f"🔧 Set mpmath precision to {args.precision} decimal places")
    
    # Handle fast test mode
    if args.fast_test:
        args.max_primes = 100
        args.max_zeros = 50
        args.integration_limit = 10
        args.tolerance = 1e-3
        logger.info("🚀 Fast test mode enabled - using reduced parameters")
    
    # Parameter validation
    validation_errors = validate_parameters(
        args.max_primes, 5, args.integration_limit, 
        args.max_zeros, args.tolerance
    )
    
    if validation_errors:
        logger.error("❌ Parameter validation failed:")
        for error in validation_errors:
            logger.error(f"  • {error}")
        sys.exit(1)
    
    # Configuration summary
    config = {
        'P': min(args.max_primes, 10000),  # Safety cap
        'K': 5,
        'sigma0': DEFAULT_PARAMS['sigma0'],
        'T': args.integration_limit,
        'lim_u': args.support_limit,
        'max_zeros': args.max_zeros,
        'tolerance': args.tolerance,
        'frequency_sig': DEFAULT_PARAMS['frequency_signature']
    }
    
    print("🚀 RIEMANN HYPOTHESIS VALIDATION - JMMB Ψ✧ FRAMEWORK")
    print("="*60)
    print("🧮 Configuration:")
    for key, value in config.items():
        print(f"  {key}: {value}")
    print(f"  precision: {args.precision} decimal places")
    print("="*60)
    
    try:
        # Initialize test function
        f = truncated_gaussian
        logger.info("📝 Using truncated_gaussian test function")
        
        # Verify zeros file
        zeros_file = 'zeros/zeros_t1e8.txt'
        if not os.path.exists(zeros_file):
            logger.error(f"❌ Zeros file not found: {zeros_file}")
            print("\n🔧 COPILOT SUGGESTION:")
            print("• Download Odlyzko zeros data or generate zeros file")
            print("• Check repository README for data setup instructions")
            sys.exit(1)
        
        logger.info(f"✅ Found zeros file: {zeros_file}")
        
        # COMPUTATION PHASE
        print("\n🧮 COMPUTATION PHASE")
        print("-"*40)
        
        # Compute arithmetic side
        print("🔢 Computing arithmetic side...")
        prime_part = prime_sum(f, config['P'], config['K'])
        arch_part = archimedean_sum(f, config['sigma0'], config['T'], config['lim_u'])
        arithmetic_side = prime_part + arch_part
        
        print(f"  Prime contribution:       {prime_part}")
        print(f"  Archimedean contribution: {arch_part}")
        print(f"  Total arithmetic side:    {arithmetic_side}")
        
        # Compute spectral side  
        print("\n🌊 Computing spectral side...")
        zero_side = zero_sum_limited(f, zeros_file, config['max_zeros'], config['lim_u'])
        print(f"  Zero sum contribution:    {zero_side}")
        
        # VALIDATION PHASE
        print("\n🔍 VALIDATION PHASE")
        print("-"*40)
        
        validation_result = validate_explicit_formula(
            arithmetic_side, zero_side, config['tolerance'], config['frequency_sig']
        )
        
        # Save comprehensive results
        os.makedirs('data', exist_ok=True)
        results_file = 'data/validation_results.csv'
        
        with open(results_file, 'w') as f:
            f.write("parameter,value,description\n")
            f.write(f"arithmetic_side,{arithmetic_side},Prime sum + Archimedean sum\n")
            f.write(f"prime_contribution,{prime_part},Sum over prime powers\n")
            f.write(f"archimedean_contribution,{arch_part},Archimedean integral\n")
            f.write(f"zero_side,{zero_side},Sum over nontrivial zeros\n")
            f.write(f"absolute_error,{validation_result['error']},|Arithmetic - Spectral|\n")
            f.write(f"relative_error,{validation_result['relative_error']},Relative error\n")
            f.write(f"tolerance,{config['tolerance']},Validation tolerance\n")
            f.write(f"validation_result,{validation_result['result_text']},PASS or FAIL\n")
            f.write(f"max_primes,{config['P']},Maximum prime used\n")
            f.write(f"K,{config['K']},Maximum prime powers\n")
            f.write(f"T,{config['T']},Integration limit\n")
            f.write(f"max_zeros,{config['max_zeros']},Number of zeros used\n")
            f.write(f"precision,{args.precision},Decimal precision\n")
            f.write(f"frequency_signature,{config['frequency_sig']},JMMB Ψ✧ signature Hz\n")
            f.write(f"computation_time,{time.time() - start_time:.2f},Total time in seconds\n")
        
        print(f"\n📊 Results saved to {results_file}")
        
        # Export HTML report if requested
        if args.export_html:
            create_html_report(validation_result, config, args, time.time() - start_time)
        
        # Summary
        print(f"\n⏱️  Total computation time: {time.time() - start_time:.2f} seconds")
        print(f"🎯 Final result: {validation_result['result_emoji']} {validation_result['result_text']}")
        
        # Exit with appropriate code
        sys.exit(0 if validation_result['is_valid'] else 1)
        
    except KeyboardInterrupt:
        logger.info("⏹️  Computation interrupted by user")
        sys.exit(130)
    except Exception as e:
        logger.error(f"❌ Unexpected error: {e}")
        import traceback
        logger.error(traceback.format_exc())
        sys.exit(1)

def create_html_report(validation_result, config, args, computation_time):
    """Create an HTML report of the validation results."""
    html_content = f"""
    <!DOCTYPE html>
    <html>
    <head>
        <title>Riemann Hypothesis Validation Report</title>
        <style>
            body {{ font-family: Arial, sans-serif; margin: 40px; }}
            .header {{ background: #f0f8ff; padding: 20px; border-radius: 10px; }}
            .result {{ background: {'#e8f5e8' if validation_result['is_valid'] else '#ffe8e8'}; 
                      padding: 15px; border-radius: 5px; margin: 20px 0; }}
            .config {{ background: #f9f9f9; padding: 15px; border-radius: 5px; }}
            table {{ border-collapse: collapse; width: 100%; }}
            th, td {{ border: 1px solid #ddd; padding: 8px; text-align: left; }}
            th {{ background-color: #f2f2f2; }}
        </style>
    </head>
    <body>
        <div class="header">
            <h1>🔬 Riemann Hypothesis Validation Report</h1>
            <h2>JMMB Ψ✧ Framework - José Manuel Mota Burruezo</h2>
            <p>Generated: {time.strftime('%Y-%m-%d %H:%M:%S')}</p>
        </div>
        
        <div class="result">
            <h2>{validation_result['result_emoji']} Validation Result: {validation_result['result_text']}</h2>
            <p><strong>Error:</strong> {validation_result['error']:.2e}</p>
            <p><strong>Tolerance:</strong> {config['tolerance']:.2e}</p>
            <p><strong>Computation Time:</strong> {computation_time:.2f} seconds</p>
        </div>
        
        <div class="config">
            <h3>Configuration Parameters</h3>
            <table>
                <tr><th>Parameter</th><th>Value</th><th>Description</th></tr>
                <tr><td>max_primes</td><td>{config['P']}</td><td>Maximum prime used</td></tr>
                <tr><td>max_zeros</td><td>{config['max_zeros']}</td><td>Number of zeros</td></tr>
                <tr><td>precision</td><td>{args.precision}</td><td>Decimal precision</td></tr>
                <tr><td>tolerance</td><td>{config['tolerance']}</td><td>Validation tolerance</td></tr>
                <tr><td>frequency_sig</td><td>{config['frequency_sig']} Hz</td><td>JMMB Ψ✧ signature</td></tr>
            </table>
        </div>
    </body>
    </html>
    """
    
    os.makedirs('docs', exist_ok=True)
    with open('docs/validation_report.html', 'w') as f:
        f.write(html_content)
    
    print("📄 HTML report saved to docs/validation_report.html")

