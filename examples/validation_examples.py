#!/usr/bin/env python3
"""
JMMB Riemann Hypothesis Validation: Example Scenarios and Benchmarks
===================================================================

This script demonstrates various usage scenarios for the enhanced Copilot-aware
validation system and provides performance benchmarks for different parameter
combinations.

Run with: python examples/validation_examples.py
"""

import os
import sys
import time
import subprocess
import json
from pathlib import Path

# Add parent directory to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

def run_validation(args, description):
    """Run validation with given arguments and capture results."""
    print(f"\n{'='*60}")
    print(f"🧪 {description}")
    print('='*60)
    
    cmd = [sys.executable, "validate_explicit_formula.py"] + args
    start_time = time.time()
    
    try:
        result = subprocess.run(cmd, capture_output=True, text=True, cwd="..")
        end_time = time.time()
        
        print(f"⏱️  Execution time: {end_time - start_time:.2f} seconds")
        print(f"🔍 Exit code: {result.returncode}")
        
        if result.stdout:
            print(f"📊 Output:\n{result.stdout}")
        
        if result.stderr:
            print(f"⚠️  Stderr:\n{result.stderr}")
            
        # Try to extract key metrics from CSV if it exists
        csv_path = "../data/validation_results.csv"
        if os.path.exists(csv_path):
            with open(csv_path, 'r') as f:
                lines = f.readlines()
                metrics = {}
                for line in lines[1:]:  # Skip header
                    if ',' in line:
                        key, value = line.strip().split(',', 1)
                        metrics[key] = value
                
                print(f"\n📈 Key Metrics:")
                if 'validation_result' in metrics:
                    print(f"   Result: {metrics['validation_result']}")
                if 'absolute_error' in metrics:
                    print(f"   Error: {metrics['absolute_error']}")
                if 'computation_time' in metrics:
                    print(f"   Time: {metrics['computation_time']}s")
        
        return {
            'success': result.returncode == 0,
            'time': end_time - start_time,
            'args': args,
            'description': description
        }
        
    except Exception as e:
        print(f"❌ Error running validation: {e}")
        return {'success': False, 'error': str(e), 'args': args}

def main():
    """Run comprehensive validation examples and benchmarks."""
    print("🧠 JMMB Riemann Hypothesis Validation: Example Scenarios")
    print("=" * 80)
    print("🔬 Testing various parameter combinations and modes")
    print("✧ Demonstrating Copilot-aware mathematical validation")
    print("=" * 80)
    
    # Change to the repository root directory
    os.chdir(Path(__file__).parent.parent)
    
    examples = [
        {
            'args': ['--help'],
            'description': 'Help and Usage Information'
        },
        {
            'args': ['--quick', '--max_primes', '30', '--max_zeros', '10'],
            'description': 'Ultra-Fast Validation (Development Mode)'
        },
        {
            'args': ['--quick', '--verbose'],
            'description': 'Quick Mode with Verbose Logging'
        },
        {
            'args': ['--max_primes', '100', '--max_zeros', '50', '--tolerance', '1e-3'],
            'description': 'Small-Scale Validation with Relaxed Tolerance'
        },
        {
            'args': ['--max_primes', '500', '--max_zeros', '200', '--precision', '15'],
            'description': 'Medium-Scale Validation (Balanced Performance)'
        },
        {
            'args': ['--max_primes', '200', '--max_zeros', '100', '--tolerance', '1e-8', '--verbose'],
            'description': 'High-Precision Validation with Detailed Logging'
        },
        {
            'args': ['--max_primes', '1000', '--max_zeros', '500', '--precision', '25'],
            'description': 'Large-Scale Validation (Production Mode)'
        }
    ]
    
    results = []
    
    for example in examples:
        try:
            result = run_validation(example['args'], example['description'])
            results.append(result)
            
            # Add small delay between runs
            time.sleep(1)
            
        except KeyboardInterrupt:
            print("\n⏹️  Interrupted by user")
            break
        except Exception as e:
            print(f"❌ Unexpected error: {e}")
            continue
    
    # Performance Summary
    print(f"\n{'='*80}")
    print("📊 PERFORMANCE SUMMARY")
    print('='*80)
    
    successful_runs = [r for r in results if r.get('success', False)]
    
    if successful_runs:
        print(f"✅ Successful runs: {len(successful_runs)}/{len(results)}")
        
        times = [r['time'] for r in successful_runs if 'time' in r]
        if times:
            print(f"⏱️  Average execution time: {sum(times)/len(times):.2f}s")
            print(f"⚡ Fastest run: {min(times):.2f}s")
            print(f"🐌 Slowest run: {max(times):.2f}s")
        
        print(f"\n🎯 Recommended configurations:")
        print(f"   Development: --quick --max_primes 50 --max_zeros 20")
        print(f"   Testing: --max_primes 200 --max_zeros 100 --tolerance 1e-6")
        print(f"   Production: --max_primes 1000 --max_zeros 500 --precision 20")
    
    # Copilot Suggestions
    print(f"\n{'='*80}")
    print("🚀 COPILOT INTEGRATION SUGGESTIONS")
    print('='*80)
    print("""
💡 To get the most out of Copilot with this validation system:

1. **Interactive Development**:
   - Use --verbose mode to see detailed mathematical steps
   - Start with --quick mode for rapid iteration
   - Gradually increase parameters as needed

2. **Parameter Optimization**:
   - Monitor the absolute_error in CSV output
   - Adjust --tolerance based on your precision needs
   - Use --precision to balance accuracy vs. speed

3. **Debugging and Analysis**:
   - Check coherence_factor for JMMB signature analysis
   - Compare different tolerance levels
   - Use verbose output to identify bottlenecks

4. **Batch Processing**:
   - Create parameter sweep scripts
   - Use CSV output for automated analysis
   - Monitor computation_time for performance tuning

5. **Mathematical Exploration**:
   - Try different max_zeros values to study convergence
   - Experiment with precision levels
   - Analyze error patterns across parameter ranges
    """)
    
    print(f"\n{'='*80}")
    print("✨ VALIDATION EXAMPLES COMPLETED")
    print('='*80)
    print("🔬 The enhanced validation system is ready for mathematical exploration!")
    print("🧠 Use these examples as templates for your own Copilot-assisted research.")
    print("=" * 80)

if __name__ == "__main__":
    main()