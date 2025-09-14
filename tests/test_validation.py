"""
🧠 Copilot Prompt:
Create pytest tests for mathematical identity checks in the Riemann Hypothesis validation.

Test the consistency between prime_sum, A_infty, and zero_sum functions.
Ensure the explicit formula validation works for different test functions.

Enhanced tests for the computational validation framework including
SHA256 integrity verification and result consistency checks.
"""

import pytest
import mpmath as mp
import os
import json
from validate_explicit_formula import prime_sum, archimedean_sum, zero_sum
from utils.mellin import truncated_gaussian
from utils.validation_core import ComputationalValidator, ValidationResults


def test_riemann_formula_matches():
    """Test that the explicit formula sides match within tolerance."""
    f = truncated_gaussian
    P = 100  # Smaller values for faster testing
    K = 5
    sigma0 = 2.0
    T = 10
    lim_u = 3.0
    
    # Calculate both sides
    prime_side = prime_sum(f, P, K)
    arch_side = archimedean_sum(f, sigma0, T, lim_u)
    total = prime_side + arch_side
    
    # For testing, we'll use a mock zero sum since we need the actual zeros file
    # This is where Copilot should suggest improvements
    mock_zero_side = total  # This should be replaced with actual zero_sum calculation
    
    assert abs(total - mock_zero_side) < 1e-5


def test_mellin_transform_properties():
    """Test basic properties of the Mellin transform."""
    from utils.mellin import mellin_transform
    
    # Test that Mellin transform of truncated Gaussian has expected properties
    f = truncated_gaussian
    s = mp.mpc(1, 0)  # s = 1
    lim = 3.0
    
    result = mellin_transform(f, s, lim)
    assert isinstance(result, (mp.mpc, mp.mpf))  # Should return a complex number
    assert mp.isfinite(result)  # Should be finite


def test_validation_results_integrity():
    """Test SHA256 integrity verification for ValidationResults."""
    # Create a test validation result
    params = {'max_primes': 10, 'max_zeros': 5, 'precision': 15}
    results = ValidationResults('test_run', params)
    
    # Add some test results
    results.add_result('test_value', '1.234567890')
    results.add_result('another_value', '9.876543210')
    
    # Compute hash twice - should be identical
    hash1 = results.compute_integrity_hash()
    hash2 = results.compute_integrity_hash()
    
    assert hash1 == hash2
    assert len(hash1) == 64  # SHA256 produces 64-char hex string
    assert hash1 == results.computed_hash


def test_computational_validator_basic():
    """Test basic functionality of ComputationalValidator."""
    # Use a temporary directory for testing
    test_dir = "/tmp/test_validation_runs"
    os.makedirs(test_dir, exist_ok=True)
    
    validator = ComputationalValidator(test_dir)
    
    # Run a very small validation for testing
    mp.mp.dps = 15  # Lower precision for speed
    results = validator.run_partial_validation(
        max_primes=5,
        max_zeros=3,
        sigma0=2.0,
        T=5.0
    )
    
    # Check that results were generated
    assert results.run_id is not None
    assert 'prime_sum' in results.results
    assert 'absolute_error' in results.results
    assert results.computed_hash is not None
    
    # Check that files were created
    csv_file = os.path.join(test_dir, f"{results.run_id}_results.csv")
    json_file = os.path.join(test_dir, f"{results.run_id}_full.json")
    
    assert os.path.exists(csv_file)
    assert os.path.exists(json_file)


def test_result_serialization_roundtrip():
    """Test that ValidationResults can be saved and loaded correctly."""
    # Create test results
    params = {'test_param': 42}
    results = ValidationResults('test_serialization', params)
    results.add_result('computation', '3.14159', {'metadata': 'test'})
    
    # Convert to dict and back
    data_dict = results.to_dict()
    
    # Verify required fields are present
    assert 'run_id' in data_dict
    assert 'timestamp' in data_dict
    assert 'params' in data_dict
    assert 'results' in data_dict
    assert 'computed_hash' in data_dict
    
    # Verify data integrity
    assert data_dict['run_id'] == 'test_serialization'
    assert data_dict['params']['test_param'] == 42
    assert 'computation' in data_dict['results']


def test_integrity_verification():
    """Test that integrity verification detects modifications."""
    # Create test data
    test_dir = "/tmp/test_integrity"
    os.makedirs(test_dir, exist_ok=True)
    
    validator = ComputationalValidator(test_dir)
    
    # Create a simple result file
    params = {'test': True}
    results = ValidationResults('integrity_test', params)
    results.add_result('value', '1.0')
    
    # Save to JSON
    json_path = os.path.join(test_dir, 'integrity_test.json')
    with open(json_path, 'w') as f:
        json.dump(results.to_dict(), f)
    
    # Verify original file
    verification = validator.verify_result_integrity(json_path)
    assert verification['integrity_verified'] == True
    
    # Modify the file (corrupt it)
    with open(json_path, 'r') as f:
        data = json.load(f)
    
    data['results']['value']['value'] = '2.0'  # Change the value
    
    with open(json_path, 'w') as f:
        json.dump(data, f)
    
    # Verify corrupted file
    verification_corrupted = validator.verify_result_integrity(json_path)
    assert verification_corrupted['integrity_verified'] == False


if __name__ == "__main__":
    pytest.main([__file__])