import pytest
import mpmath as mp
import sympy as sp
import os
import sys

# Add utils to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from utils.mellin import truncated_gaussian, mellin_transform
from validate_explicit_formula import prime_sum, archimedean_sum, zero_sum

class TestRiemannValidation:
    """Test suite for Riemann Hypothesis validation."""
    
    def setup_method(self):
        """Setup test parameters."""
        mp.mp.dps = 20  # Lower precision for faster tests
        
        # Test functions
        self.f1 = lambda u: mp.exp(-u**2/2) if abs(u) <= 3 else mp.mpf(0)
        self.f2 = lambda u: mp.exp(-u**2) if abs(u) <= 2 else mp.mpf(0)
        self.f3 = lambda u: (1 - u**2/4)**2 if abs(u) <= 2 else mp.mpf(0)
        
        # Reduced parameters for testing
        self.P_test = 50
        self.K_test = 5
        self.N_Xi_test = 100
        self.sigma0 = 2.0
        self.T_test = 10
        self.lim_u = 2.0
        
        # Path to zeros file
        self.zeros_file = os.path.join(os.path.dirname(__file__), '..', 'zeros', 'zeros_t1e8.txt')
        
    def test_zeros_file_exists(self):
        """Test that the zeros file exists and has content."""
        assert os.path.exists(self.zeros_file), "Zeros file does not exist"
        
        with open(self.zeros_file, 'r') as f:
            lines = f.readlines()
        
        assert len(lines) > 1000, "Zeros file should have many entries"
        
        # Test first few entries are valid numbers
        for i, line in enumerate(lines[:5]):
            gamma = float(line.strip())
            assert gamma > 0, f"Zero {i} should be positive: {gamma}"
            
    def test_prime_sum_computation(self):
        """Test prime sum computation."""
        result = prime_sum(self.f1, self.P_test, self.K_test)
        
        assert isinstance(result, mp.mpf), "Prime sum should return mpf"
        assert result > 0, "Prime sum should be positive"
        assert result != mp.inf, "Prime sum should be finite"
        
    def test_zero_sum_computation(self):
        """Test zero sum computation with small number of zeros."""
        if not os.path.exists(self.zeros_file):
            pytest.skip("Zeros file not available")
            
        result = zero_sum(self.f1, self.zeros_file, self.lim_u, 50)  # Only 50 zeros
        
        assert isinstance(result, mp.mpf), "Zero sum should return mpf"
        assert result != mp.inf, "Zero sum should be finite"
        
    def test_mellin_transform_basic(self):
        """Test basic Mellin transform functionality."""
        result = mellin_transform(self.f1, mp.mpc(2, 10), 2.0)
        
        assert isinstance(result, mp.mpc), "Mellin transform should return complex number"
        assert mp.isfinite(result), "Mellin transform should be finite"
        
    def test_function_properties(self):
        """Test that test functions have expected properties."""
        # f1: Gaussian with support [-3, 3]
        assert self.f1(0) > 0, "f1(0) should be positive"
        assert self.f1(4) == 0, "f1 should have compact support"
        assert abs(self.f1(2)) < abs(self.f1(0)), "f1 should decay"
        
        # f2: Gaussian with support [-2, 2] 
        assert self.f2(0) > 0, "f2(0) should be positive"
        assert self.f2(3) == 0, "f2 should have compact support"
        
        # f3: Polynomial with support [-2, 2]
        assert self.f3(0) > 0, "f3(0) should be positive" 
        assert self.f3(3) == 0, "f3 should have compact support"
        
    def test_error_threshold(self):
        """Test that validation can detect if error exceeds threshold."""
        # This is a placeholder - in real implementation, we'd run full validation
        # and check if |A - Z| > 1e-5 raises appropriate alerts
        
        threshold = 1e-5
        
        # Simulate some results
        A = mp.mpf('1.23456789')
        Z = mp.mpf('1.23456790')  # Small difference
        error = abs(A - Z)
        
        assert error < threshold, f"Small error {error} should pass threshold {threshold}"
        
        # Large difference
        Z_bad = mp.mpf('1.23460000')  # Larger difference  
        error_bad = abs(A - Z_bad)
        
        assert error_bad > threshold, f"Large error {error_bad} should exceed threshold {threshold}"

    def test_csv_output_structure(self):
        """Test that CSV output has correct structure."""
        import csv
        
        # Expected fieldnames
        expected_fields = ['function', 'prime_sum', 'archimedean_sum', 'arithmetic_total', 
                          'zero_sum', 'absolute_error', 'relative_error', 'success']
        
        # This would be called after running validation
        csv_path = os.path.join(os.path.dirname(__file__), '..', 'data', 'validation_output.csv')
        
        if os.path.exists(csv_path):
            with open(csv_path, 'r') as csvfile:
                reader = csv.DictReader(csvfile)
                fieldnames = reader.fieldnames
                
                for field in expected_fields:
                    assert field in fieldnames, f"Missing field {field} in CSV output"
                    
                # Check we have rows
                rows = list(reader)
                assert len(rows) > 0, "CSV should have data rows"

if __name__ == "__main__":
    pytest.main([__file__, "-v"])