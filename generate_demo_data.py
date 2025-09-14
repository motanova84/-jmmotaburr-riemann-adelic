#!/usr/bin/env python3
"""
🧠 Copilot Enhancement: Generate demonstration validation data

Creates a set of validation runs with different parameters to demonstrate
the computational framework capabilities.
"""

import os
import time
from utils.validation_core import ComputationalValidator
import mpmath as mp

def generate_demo_data():
    """Generate a series of validation runs for demonstration."""
    
    print("🧮 Generating demonstration validation data...")
    
    validator = ComputationalValidator("data/validation_runs")
    
    # Set lower precision for faster demo generation
    mp.mp.dps = 20
    
    # Configuration for different validation scenarios
    scenarios = [
        {
            'name': 'quick_test',
            'max_primes': 20,
            'max_zeros': 10,
            'sigma0': 2.0,
            'T': 20.0
        },
        {
            'name': 'medium_test', 
            'max_primes': 100,
            'max_zeros': 50,
            'sigma0': 2.0,
            'T': 50.0
        },
        {
            'name': 'precision_test',
            'max_primes': 50,
            'max_zeros': 25,
            'sigma0': 1.5,
            'T': 30.0
        }
    ]
    
    results_summary = []
    
    for i, scenario in enumerate(scenarios):
        print(f"\n📊 Running scenario {i+1}/3: {scenario['name']}")
        
        try:
            results = validator.run_partial_validation(
                max_primes=scenario['max_primes'],
                max_zeros=scenario['max_zeros'],
                sigma0=scenario['sigma0'],
                T=scenario['T']
            )
            
            print(f"  ✅ Completed: {results.run_id}")
            print(f"  🔒 Hash: {results.computed_hash}")
            
            # Extract key metrics for summary
            if 'absolute_error' in results.results:
                abs_error = results.results['absolute_error']['value']
                results_summary.append({
                    'scenario': scenario['name'],
                    'run_id': results.run_id,
                    'absolute_error': abs_error,
                    'hash': results.computed_hash
                })
            
            # Small delay between runs
            time.sleep(1)
            
        except Exception as e:
            print(f"  ❌ Failed: {e}")
    
    print(f"\n📋 Demo Data Generation Complete")
    print(f"Generated {len(results_summary)} validation runs")
    
    # Display summary
    if results_summary:
        print(f"\n📊 Results Summary:")
        for result in results_summary:
            print(f"  {result['scenario']}: Error = {result['absolute_error']}")
    
    print(f"\n💾 Data saved to: data/validation_runs/")
    print(f"📖 Use 'python analyze_results.py --verify --analyze' to analyze")
    
    return results_summary

if __name__ == "__main__":
    generate_demo_data()