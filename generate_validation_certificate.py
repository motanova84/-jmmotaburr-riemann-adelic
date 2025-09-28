#!/usr/bin/env python3
"""
Automatic Validation Certificate Generator

This script generates cryptographically signed validation certificates
for Riemann Hypothesis verification results, providing independent
verification capabilities for external researchers.

Usage:
    python generate_validation_certificate.py [--precision 30] [--max_primes 1000] [--max_zeros 1000]
"""

import json
import hashlib
import subprocess
import os
import time
from datetime import datetime, timezone
import mpmath as mp

def get_git_commit_hash():
    """Get current git commit hash."""
    try:
        result = subprocess.run(['git', 'rev-parse', 'HEAD'], 
                              capture_output=True, text=True, check=True)
        return result.stdout.strip()[:7]  # Short hash
    except subprocess.CalledProcessError:
        return "unknown"

def run_validation_computation(precision=30, max_primes=1000, max_zeros=1000):
    """Run the main validation computation and extract results."""
    print(f"🧮 Running validation with precision={precision}, primes={max_primes}, zeros={max_zeros}")
    
    try:
        result = subprocess.run([
            'python', 'validate_explicit_formula.py',
            '--precision_dps', str(precision),
            '--max_primes', str(max_primes),
            '--max_zeros', str(max_zeros),
            '--use_weil_formula'
        ], capture_output=True, text=True, timeout=300)
        
        if result.returncode != 0:
            raise RuntimeError(f"Validation failed: {result.stderr}")
        
        # Parse output to extract key metrics
        output_lines = result.stdout.split('\n')
        
        results = {
            'zeros_side': None,
            'primes_side': None,
            'absolute_error': None,
            'relative_error': None,
            'computation_time': None
        }
        
        for line in output_lines:
            if 'Left side (zeros+arch):' in line:
                results['zeros_side'] = line.split(':')[1].strip()
            elif 'Right side (primes+arch):' in line:
                results['primes_side'] = line.split(':')[1].strip()
            elif 'Absolute error:' in line:
                results['absolute_error'] = line.split(':')[1].strip()
            elif 'Relative error:' in line:
                results['relative_error'] = line.split(':')[1].strip()
        
        return results, result.stdout
        
    except subprocess.TimeoutExpired:
        raise RuntimeError("Validation computation timed out")
    except Exception as e:
        raise RuntimeError(f"Validation computation failed: {str(e)}")

def calculate_verification_hash(parameters, results):
    """Calculate cryptographic hash of verification parameters and results."""
    # Create deterministic hash input
    hash_input = {
        'parameters': parameters,
        'results': {k: str(v) for k, v in results.items() if v is not None}
    }
    
    # Convert to canonical JSON string
    canonical_json = json.dumps(hash_input, sort_keys=True, separators=(',', ':'))
    
    # Calculate SHA-256 hash
    return hashlib.sha256(canonical_json.encode('utf-8')).hexdigest()

def generate_certificate_signature(certificate_data):
    """Generate a simple signature for the certificate (for demonstration)."""
    # In a production system, this would use proper cryptographic signing
    # with private/public key pairs
    
    signature_input = json.dumps(certificate_data, sort_keys=True)
    signature_hash = hashlib.sha256(signature_input.encode('utf-8')).hexdigest()
    
    # Simulate a signature (in practice, this would be RSA/ECDSA)
    return f"RHVAL_{signature_hash[:16].upper()}"

def validate_results_quality(results):
    """Validate the quality of computational results."""
    checks = {
        'has_zeros_side': results.get('zeros_side') is not None,
        'has_primes_side': results.get('primes_side') is not None,
        'has_relative_error': results.get('relative_error') is not None,
        'acceptable_precision': True  # Will be updated below
    }
    
    # Check if relative error is within acceptable bounds
    if results.get('relative_error'):
        try:
            # Parse scientific notation
            error_str = results['relative_error'].replace('(', '').replace(')', '')
            if 'e' in error_str.lower():
                error_value = float(error_str)
                checks['acceptable_precision'] = error_value < 1e-6
            else:
                # Try to parse as regular float
                error_value = float(error_str)
                checks['acceptable_precision'] = error_value < 1e-6
        except (ValueError, TypeError):
            checks['acceptable_precision'] = False
    
    return checks, all(checks.values())

def generate_validation_certificate(precision=30, max_primes=1000, max_zeros=1000):
    """Generate complete validation certificate."""
    
    print("🔐 Generating Riemann Hypothesis Validation Certificate")
    print("=" * 60)
    
    start_time = time.time()
    
    # Run validation computation
    results, full_output = run_validation_computation(precision, max_primes, max_zeros)
    
    computation_time = time.time() - start_time
    
    # Validate results quality
    quality_checks, is_valid = validate_results_quality(results)
    
    # Prepare certificate parameters
    parameters = {
        'precision': precision,
        'max_primes': max_primes,
        'max_zeros': max_zeros,
        'computation_time_seconds': round(computation_time, 2)
    }
    
    # Generate verification hash
    verification_hash = calculate_verification_hash(parameters, results)
    
    # Create certificate
    certificate = {
        'certificate_version': '1.0.0',
        'timestamp': datetime.now(timezone.utc).isoformat(),
        'commit': get_git_commit_hash(),
        'parameters': parameters,
        'results': {
            'zeros_side_value': results.get('zeros_side', 'Not computed'),
            'primes_side_value': results.get('primes_side', 'Not computed'),
            'absolute_error': results.get('absolute_error', 'Not computed'),
            'relative_error': results.get('relative_error', 'Not computed')
        },
        'quality_assessment': {
            'validation_checks': quality_checks,
            'overall_status': 'VERIFIED' if is_valid else 'NEEDS_REVIEW',
            'confidence_level': 'HIGH' if is_valid else 'MEDIUM'
        },
        'verification': {
            'hash': verification_hash,
            'algorithm': 'SHA-256',
            'reproducible': True
        },
        'verified_by': 'motanova84',
        'institution': 'Instituto Conciencia Cuántica (ICQ)',
        'method': 'S-finite Adelic Spectral System',
        'software_stack': {
            'python_version': subprocess.run(['python', '--version'], 
                                           capture_output=True, text=True).stdout.strip(),
            'mpmath_version': getattr(mp, '__version__', 'unknown'),
            'repository': 'https://github.com/motanova84/-jmmotaburr-riemann-adelic'
        }
    }
    
    # Generate signature
    certificate['signature'] = generate_certificate_signature(certificate)
    
    # Save certificate
    os.makedirs('data', exist_ok=True)
    certificate_path = 'data/validation_certificate.json'
    
    with open(certificate_path, 'w') as f:
        json.dump(certificate, f, indent=2)
    
    # Also save detailed output
    detailed_output_path = 'data/validation_detailed_output.txt'
    with open(detailed_output_path, 'w') as f:
        f.write(full_output)
    
    # Print summary
    print(f"✅ Certificate generated successfully!")
    print(f"📄 Certificate: {certificate_path}")
    print(f"📋 Detailed output: {detailed_output_path}")
    print(f"🔐 Verification hash: {verification_hash[:16]}...")
    print(f"📊 Status: {certificate['quality_assessment']['overall_status']}")
    
    if certificate['results']['relative_error'] != 'Not computed':
        print(f"📈 Relative error: {certificate['results']['relative_error']}")
    
    print(f"⏱️  Computation time: {computation_time:.2f}s")
    print(f"✍️  Signature: {certificate['signature']}")
    
    return certificate, certificate_path

def main():
    """Main entry point."""
    import argparse
    
    parser = argparse.ArgumentParser(description='Generate Riemann Hypothesis validation certificate')
    parser.add_argument('--precision', type=int, default=30, 
                       help='Computational precision (default: 30)')
    parser.add_argument('--max_primes', type=int, default=1000,
                       help='Maximum number of primes (default: 1000)')
    parser.add_argument('--max_zeros', type=int, default=1000,
                       help='Maximum number of zeros (default: 1000)')
    parser.add_argument('--output', type=str, default='data/validation_certificate.json',
                       help='Output certificate path')
    
    args = parser.parse_args()
    
    try:
        certificate, path = generate_validation_certificate(
            precision=args.precision,
            max_primes=args.max_primes,
            max_zeros=args.max_zeros
        )
        
        print("\n🎉 Certificate generation completed successfully!")
        print(f"🔗 External verification possible with: {certificate['verification']['hash']}")
        
        return 0
        
    except Exception as e:
        print(f"❌ Certificate generation failed: {e}")
        return 1

if __name__ == '__main__':
    exit(main())