#!/usr/bin/env python3
"""
🧠 Copilot Enhancement: Result Analysis and Verification Tools

This script provides utilities for:
- Batch verification of validation results
- Statistical analysis of multiple runs  
- Generation of comparison reports
- Data integrity checking across runs
"""

import os
import json
import glob
import pandas as pd
from pathlib import Path
from typing import List, Dict, Any
import argparse

from utils.validation_core import ComputationalValidator


def analyze_validation_runs(directory: str = "data/validation_runs") -> pd.DataFrame:
    """Analyze all validation runs in a directory and create comparison DataFrame."""
    
    results_data = []
    json_files = glob.glob(os.path.join(directory, "*_full.json"))
    
    print(f"🔍 Found {len(json_files)} validation runs to analyze")
    
    for json_file in json_files:
        try:
            with open(json_file, 'r') as f:
                data = json.load(f)
                
            # Extract key metrics
            row = {
                'run_id': data['run_id'],
                'timestamp': data['timestamp'],
                'max_primes': data['params'].get('max_primes', 'N/A'),
                'max_zeros': data['params'].get('max_zeros', 'N/A'),
                'precision': data['params'].get('precision', 'N/A'),
            }
            
            # Add computational results
            for key in ['prime_sum', 'archimedean_sum', 'arithmetic_side', 'zero_sum', 'absolute_error', 'relative_error']:
                if key in data['results']:
                    row[key] = data['results'][key]['value']
                else:
                    row[key] = 'N/A'
                    
            # Add integrity info
            row['stored_hash'] = data.get('computed_hash', 'N/A')
            
            results_data.append(row)
            
        except Exception as e:
            print(f"⚠️  Warning: Could not process {json_file}: {e}")
            
    return pd.DataFrame(results_data)


def verify_all_runs(directory: str = "data/validation_runs") -> Dict[str, Any]:
    """Verify integrity of all validation runs in directory."""
    
    validator = ComputationalValidator()
    json_files = glob.glob(os.path.join(directory, "*_full.json"))
    
    verification_results = {
        'total_files': len(json_files),
        'verified': 0,
        'failed': 0,
        'details': []
    }
    
    print(f"🔒 Verifying integrity of {len(json_files)} result files...")
    
    for json_file in json_files:
        try:
            result = validator.verify_result_integrity(json_file)
            verification_results['details'].append(result)
            
            if result['integrity_verified']:
                verification_results['verified'] += 1
                print(f"  ✅ {result['run_id']}")
            else:
                verification_results['failed'] += 1
                print(f"  ❌ {result['run_id']} - INTEGRITY FAILED")
                
        except Exception as e:
            verification_results['failed'] += 1
            print(f"  ❌ {json_file} - ERROR: {e}")
            
    return verification_results


def generate_comparison_report(directory: str = "data/validation_runs", output_file: str = None):
    """Generate a comprehensive comparison report."""
    
    df = analyze_validation_runs(directory)
    
    if df.empty:
        print("❌ No validation runs found for analysis")
        return
        
    print(f"\n📊 Analysis of {len(df)} validation runs:")
    print("=" * 60)
    
    # Basic statistics
    print(f"\n📈 Parameter ranges:")
    if 'max_primes' in df.columns:
        primes_col = pd.to_numeric(df['max_primes'], errors='coerce').dropna()
        if not primes_col.empty:
            print(f"  Max primes: {primes_col.min()} - {primes_col.max()}")
            
    if 'max_zeros' in df.columns:
        zeros_col = pd.to_numeric(df['max_zeros'], errors='coerce').dropna()
        if not zeros_col.empty:
            print(f"  Max zeros:  {zeros_col.min()} - {zeros_col.max()}")
    
    # Error analysis
    print(f"\n🎯 Error analysis:")
    if 'absolute_error' in df.columns:
        abs_errors = pd.to_numeric(df['absolute_error'], errors='coerce').dropna()
        if not abs_errors.empty:
            print(f"  Absolute errors: {abs_errors.min():.2e} - {abs_errors.max():.2e}")
            print(f"  Mean abs error:  {abs_errors.mean():.2e}")
            
    if 'relative_error' in df.columns:
        rel_errors = pd.to_numeric(df['relative_error'], errors='coerce').dropna()
        if not rel_errors.empty:
            print(f"  Relative errors: {rel_errors.min():.2e} - {rel_errors.max():.2e}")
            print(f"  Mean rel error:  {rel_errors.mean():.2e}")
    
    # Save detailed report if requested
    if output_file:
        output_path = Path(output_file)
        output_path.parent.mkdir(parents=True, exist_ok=True)
        
        # Save as CSV
        csv_path = output_path.with_suffix('.csv')
        df.to_csv(csv_path, index=False)
        print(f"\n💾 Detailed results saved to: {csv_path}")
        
        # Save summary as text
        summary_path = output_path.with_suffix('.txt')
        with open(summary_path, 'w') as f:
            f.write("Riemann Hypothesis Validation Run Analysis\n")
            f.write("=" * 50 + "\n\n")
            f.write(f"Total runs analyzed: {len(df)}\n")
            f.write(f"Analysis timestamp: {pd.Timestamp.now()}\n\n")
            
            f.write("Summary Statistics:\n")
            f.write(df.describe().to_string())
            f.write("\n\nDetailed Data:\n")
            f.write(df.to_string())
            
        print(f"💾 Summary report saved to: {summary_path}")


def main():
    parser = argparse.ArgumentParser(description='Analyze and verify Riemann validation results')
    parser.add_argument('--directory', '-d', default='data/validation_runs',
                        help='Directory containing validation results')
    parser.add_argument('--verify', action='store_true',
                        help='Verify integrity of all results')
    parser.add_argument('--analyze', action='store_true',
                        help='Analyze and compare results')
    parser.add_argument('--report', '-r', type=str,
                        help='Generate detailed report (specify output file base name)')
    
    args = parser.parse_args()
    
    if not (args.verify or args.analyze or args.report):
        print("❌ Please specify --verify, --analyze, or --report")
        parser.print_help()
        return 1
        
    directory = args.directory
    
    if not os.path.exists(directory):
        print(f"❌ Directory not found: {directory}")
        return 1
        
    if args.verify:
        verification_results = verify_all_runs(directory)
        print(f"\n🔒 Verification Summary:")
        print(f"  Total files: {verification_results['total_files']}")
        print(f"  Verified:    {verification_results['verified']}")
        print(f"  Failed:      {verification_results['failed']}")
        
        if verification_results['failed'] > 0:
            print(f"\n❌ {verification_results['failed']} files failed verification!")
            return 1
        else:
            print(f"\n✅ All files passed integrity verification")
            
    if args.analyze or args.report:
        generate_comparison_report(directory, args.report)
        
    return 0


if __name__ == "__main__":
    import sys
    sys.exit(main())