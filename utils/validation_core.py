"""
🧠 Copilot Enhancement: Core validation framework for computational Riemann Hypothesis verification

This module provides:
- SHA256 integrity checking for validation data
- CSV output generation for reproducible results
- Result archiving and comparison utilities
- Partial simulation run capabilities
"""

import os
import csv
import json
import hashlib
import datetime
from pathlib import Path
from typing import Dict, List, Tuple, Optional, Any

import mpmath as mp
import sympy as sp
from utils.mellin import truncated_gaussian, mellin_transform


class ValidationResults:
    """Container for validation run results with metadata."""
    
    def __init__(self, run_id: str, params: Dict[str, Any]):
        self.run_id = run_id
        self.params = params
        self.timestamp = datetime.datetime.now().isoformat()
        self.results = {}
        self.metadata = {}
        self.computed_hash = None
        
    def add_result(self, key: str, value: Any, metadata: Optional[Dict] = None):
        """Add a computation result with optional metadata."""
        self.results[key] = {
            'value': str(value) if isinstance(value, (mp.mpf, mp.mpc)) else value,
            'metadata': metadata or {}
        }
        
    def compute_integrity_hash(self) -> str:
        """Compute SHA256 hash of core results for integrity verification."""
        # Include only deterministic computational results, exclude timestamps
        hash_data = {
            'params': self.params,
            'results': {k: v['value'] for k, v in self.results.items()}
        }
        
        json_str = json.dumps(hash_data, sort_keys=True, separators=(',', ':'))
        self.computed_hash = hashlib.sha256(json_str.encode()).hexdigest()
        return self.computed_hash
        
    def to_dict(self) -> Dict[str, Any]:
        """Convert to dictionary for JSON serialization."""
        return {
            'run_id': self.run_id,
            'timestamp': self.timestamp,
            'params': self.params,
            'results': self.results,
            'metadata': self.metadata,
            'computed_hash': self.computed_hash or self.compute_integrity_hash()
        }
        
    def save_csv(self, filepath: str):
        """Save results to CSV for analysis."""
        os.makedirs(os.path.dirname(filepath), exist_ok=True)
        
        with open(filepath, 'w', newline='') as f:
            writer = csv.writer(f)
            
            # Header with metadata
            writer.writerow(['# Riemann Hypothesis Validation Results'])
            writer.writerow(['# Run ID:', self.run_id])
            writer.writerow(['# Timestamp:', self.timestamp])
            writer.writerow(['# SHA256:', self.computed_hash or self.compute_integrity_hash()])
            writer.writerow([])
            
            # Parameters
            writer.writerow(['# Parameters'])
            for key, value in self.params.items():
                writer.writerow([key, str(value)])
            writer.writerow([])
            
            # Results
            writer.writerow(['# Results'])
            writer.writerow(['key', 'value', 'error_bound', 'metadata'])
            for key, data in self.results.items():
                metadata_str = json.dumps(data.get('metadata', {}))
                error_bound = data.get('metadata', {}).get('error_bound', '')
                writer.writerow([key, data['value'], error_bound, metadata_str])


class ComputationalValidator:
    """Enhanced validator with integrity checking and result archiving."""
    
    def __init__(self, output_dir: str = "data/validation_runs"):
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)
        
    def run_partial_validation(
        self, 
        test_functions: List[str] = None,
        max_primes: int = 1000,
        max_zeros: int = 100,
        sigma0: float = 2.0,
        T: float = 50.0
    ) -> ValidationResults:
        """Run partial validation with specified parameters for faster testing."""
        
        run_id = f"partial_{datetime.datetime.now().strftime('%Y%m%d_%H%M%S')}"
        params = {
            'test_functions': test_functions or ['truncated_gaussian'],
            'max_primes': max_primes,
            'max_zeros': max_zeros,
            'sigma0': sigma0,
            'T': T,
            'precision': mp.mp.dps
        }
        
        results = ValidationResults(run_id, params)
        
        # Use truncated Gaussian as default test function
        f = truncated_gaussian
        lim_u = 5.0
        
        # Prime sum computation
        prime_sum = self._compute_prime_sum(f, max_primes, K=5)
        results.add_result('prime_sum', prime_sum, {'computation': 'prime_contribution'})
        
        # Archimedean sum computation  
        arch_sum = self._compute_archimedean_sum(f, sigma0, T, lim_u)
        results.add_result('archimedean_sum', arch_sum, {'computation': 'archimedean_contribution'})
        
        arithmetic_side = prime_sum + arch_sum
        results.add_result('arithmetic_side', arithmetic_side, {'type': 'sum_of_contributions'})
        
        # Zero sum computation (truncated for partial validation)
        zero_sum = self._compute_zero_sum_partial(f, max_zeros, lim_u)
        results.add_result('zero_sum', zero_sum, {'computation': 'spectral_side', 'zeros_used': max_zeros})
        
        # Error analysis
        absolute_error = abs(arithmetic_side - zero_sum)
        relative_error = absolute_error / abs(arithmetic_side) if arithmetic_side != 0 else mp.inf
        
        results.add_result('absolute_error', absolute_error, {'type': 'difference'})
        results.add_result('relative_error', relative_error, {'type': 'normalized_difference'})
        
        # Save results
        csv_path = self.output_dir / f"{run_id}_results.csv"
        results.save_csv(str(csv_path))
        
        json_path = self.output_dir / f"{run_id}_full.json"
        with open(json_path, 'w') as f:
            json.dump(results.to_dict(), f, indent=2)
            
        return results
        
    def _compute_prime_sum(self, f, max_primes: int, K: int = 5) -> mp.mpf:
        """Compute prime sum contribution."""
        total = mp.mpf('0')
        primes = list(sp.primerange(2, max_primes))
        
        for p in primes:
            lp = mp.log(p)
            for k in range(1, K + 1):
                total += lp * f(k * lp)
        return total
        
    def _compute_archimedean_sum(self, f, sigma0: float, T: float, lim_u: float) -> mp.mpf:
        """Compute Archimedean contribution."""
        def integrand(t):
            s = sigma0 + 1j * t
            kernel = mp.digamma(s / 2) - mp.log(mp.pi)
            mellin_val = mellin_transform(f, s, lim_u)
            return kernel * mellin_val
            
        try:
            integral, err = mp.quad(integrand, [-T, T], error=True, maxdegree=10)
            result = (integral / (2j * mp.pi)).real
            return result if mp.isfinite(result) else mp.mpf('0')
        except Exception as e:
            # Return 0 if integration fails but log the issue
            print(f"Warning: Archimedean integration failed: {e}")
            return mp.mpf('0')
        
    def _compute_zero_sum_partial(self, f, max_zeros: int, lim_u: float) -> mp.mpf:
        """Compute zero sum using first N zeros for partial validation."""
        zeros_file = "zeros/zeros_t1e8.txt"
        total = mp.mpf('0')
        
        count = 0
        if os.path.exists(zeros_file):
            with open(zeros_file) as file:
                for line in file:
                    if count >= max_zeros:
                        break
                    gamma = mp.mpf(line.strip())
                    total += mellin_transform(f, 1j * gamma, lim_u).real
                    count += 1
                    
        return total
        
    def verify_result_integrity(self, filepath: str) -> Dict[str, Any]:
        """Verify the integrity of a saved validation result."""
        with open(filepath) as f:
            data = json.load(f)
            
        # Recompute hash from results
        hash_data = {
            'params': data['params'],
            'results': {k: v['value'] for k, v in data['results'].items()}
        }
        json_str = json.dumps(hash_data, sort_keys=True, separators=(',', ':'))
        computed_hash = hashlib.sha256(json_str.encode()).hexdigest()
        
        stored_hash = data.get('computed_hash')
        
        return {
            'file': filepath,
            'stored_hash': stored_hash,
            'computed_hash': computed_hash,
            'integrity_verified': stored_hash == computed_hash,
            'timestamp': data.get('timestamp'),
            'run_id': data.get('run_id')
        }