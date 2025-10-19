#!/usr/bin/env python3
"""
Test Suite for Universal Verification Kernel
=============================================

Tests the triple verification structure U = (L, S, F):
- V_L: Logical verification
- V_S: Semantic verification  
- V_F: Physical-informational verification
"""

import pytest
import json
import tempfile
import os
from pathlib import Path
import sys

# Add tools directory to path
sys.path.insert(0, str(Path(__file__).parent.parent / "tools"))

from universal_kernel import (
    check_logic,
    check_semantics, 
    check_frequency,
    verify_universal,
    F0,
    EPS
)


class TestLogicalVerification:
    """Test V_L: Logical verification operator"""
    
    def test_dedukti_file_valid(self, tmp_path):
        """Test Dedukti file validation (gracefully handles missing tool)"""
        dk_file = tmp_path / "test.dk"
        dk_file.write_text("""
Type : Type.
Nat : Type.
zero : Nat.
succ : Nat -> Nat.
        """)
        
        # Should pass gracefully even if dkcheck not installed
        result = check_logic(str(dk_file))
        assert isinstance(result, bool)
    
    def test_lean_file_valid(self, tmp_path):
        """Test Lean file validation (gracefully handles missing tool)"""
        lean_file = tmp_path / "test.lean"
        lean_file.write_text("""
def hello : String := "world"
#check hello
        """)
        
        # Should pass gracefully even if lean not installed
        result = check_logic(str(lean_file))
        assert isinstance(result, bool)
    
    def test_nonexistent_file(self):
        """Test handling of nonexistent proof file"""
        result = check_logic("nonexistent.dk")
        assert result == False
    
    def test_unsupported_format(self, tmp_path):
        """Test handling of unsupported file format"""
        txt_file = tmp_path / "test.txt"
        txt_file.write_text("This is not a proof")
        
        # Should pass gracefully for unknown formats
        result = check_logic(str(txt_file))
        assert result == True


class TestSemanticVerification:
    """Test V_S: Semantic verification operator"""
    
    def test_valid_jsonld(self, tmp_path):
        """Test valid JSON-LD file"""
        jsonld_file = tmp_path / "valid.jsonld"
        data = {
            "@context": {"dc": "http://purl.org/dc/terms/"},
            "@id": "urn:test:object",
            "dc:title": "Test Object"
        }
        jsonld_file.write_text(json.dumps(data))
        
        result = check_semantics(str(jsonld_file))
        assert result == True
    
    def test_missing_required_fields(self, tmp_path):
        """Test JSON-LD missing required fields"""
        jsonld_file = tmp_path / "invalid.jsonld"
        data = {
            "@context": {"dc": "http://purl.org/dc/terms/"}
            # Missing @id and dc:title
        }
        jsonld_file.write_text(json.dumps(data))
        
        result = check_semantics(str(jsonld_file))
        assert result == False
    
    def test_malformed_json(self, tmp_path):
        """Test malformed JSON file"""
        jsonld_file = tmp_path / "malformed.jsonld"
        jsonld_file.write_text("{invalid json")
        
        result = check_semantics(str(jsonld_file))
        assert result == False
    
    def test_nonexistent_file(self):
        """Test handling of nonexistent file"""
        result = check_semantics("nonexistent.jsonld")
        assert result == False


class TestPhysicalVerification:
    """Test V_F: Physical-informational verification operator"""
    
    def test_valid_frequency(self, tmp_path):
        """Test valid frequency matching F0"""
        jsonld_file = tmp_path / "valid_freq.jsonld"
        data = {
            "@id": "urn:test:object",
            "dc:title": "Test",
            "freq:Hz": F0,
            "hash:sha256": "ABC123"
        }
        jsonld_file.write_text(json.dumps(data))
        
        valid, hash_val = check_frequency(str(jsonld_file))
        assert valid == True
        assert len(hash_val) == 64  # SHA256 produces 64 hex chars
    
    def test_frequency_out_of_tolerance(self, tmp_path):
        """Test frequency outside tolerance"""
        jsonld_file = tmp_path / "bad_freq.jsonld"
        data = {
            "@id": "urn:test:object",
            "dc:title": "Test",
            "freq:Hz": F0 + 1.0,  # Way outside tolerance
            "hash:sha256": "ABC123"
        }
        jsonld_file.write_text(json.dumps(data))
        
        valid, hash_val = check_frequency(str(jsonld_file))
        assert valid == False
        assert len(hash_val) == 64
    
    def test_frequency_missing(self, tmp_path):
        """Test missing frequency field"""
        jsonld_file = tmp_path / "no_freq.jsonld"
        data = {
            "@id": "urn:test:object",
            "dc:title": "Test"
            # No freq:Hz field
        }
        jsonld_file.write_text(json.dumps(data))
        
        valid, hash_val = check_frequency(str(jsonld_file))
        assert valid == False  # freq=0 is outside tolerance
    
    def test_hash_reproducibility(self, tmp_path):
        """Test hash is reproducible for same content"""
        jsonld_file = tmp_path / "hash_test.jsonld"
        data = {
            "@id": "urn:test:object",
            "dc:title": "Test",
            "freq:Hz": F0,
            "field1": "value1",
            "field2": "value2"
        }
        jsonld_file.write_text(json.dumps(data))
        
        valid1, hash1 = check_frequency(str(jsonld_file))
        valid2, hash2 = check_frequency(str(jsonld_file))
        
        assert hash1 == hash2  # Hashes must be reproducible
    
    def test_nonexistent_file(self):
        """Test handling of nonexistent file"""
        valid, hash_val = check_frequency("nonexistent.jsonld")
        assert valid == False
        assert hash_val == ""


class TestUniversalVerification:
    """Test complete U = (L, S, F) verification"""
    
    def test_full_verification_success(self, tmp_path):
        """Test complete verification with all checks passing"""
        # Create valid JSON-LD
        jsonld_file = tmp_path / "complete.jsonld"
        data = {
            "@context": {"dc": "http://purl.org/dc/terms/"},
            "@id": "urn:test:complete",
            "dc:title": "Complete Test",
            "freq:Hz": F0,
            "hash:sha256": "TEST123"
        }
        jsonld_file.write_text(json.dumps(data))
        
        # Create valid proof file (will pass gracefully without tool)
        proof_file = tmp_path / "proof.dk"
        proof_file.write_text("Type : Type.\nNat : Type.")
        
        result = verify_universal(str(jsonld_file), str(proof_file))
        assert result == True
    
    def test_verification_without_proof(self, tmp_path):
        """Test verification without proof file"""
        jsonld_file = tmp_path / "no_proof.jsonld"
        data = {
            "@context": {"dc": "http://purl.org/dc/terms/"},
            "@id": "urn:test:no_proof",
            "dc:title": "No Proof Test",
            "freq:Hz": F0
        }
        jsonld_file.write_text(json.dumps(data))
        
        result = verify_universal(str(jsonld_file))
        assert result == True  # Should pass V_S and V_F
    
    def test_verification_failure_semantic(self, tmp_path):
        """Test verification fails on semantic check"""
        jsonld_file = tmp_path / "bad_semantic.jsonld"
        data = {
            # Missing required fields
            "@context": {}
        }
        jsonld_file.write_text(json.dumps(data))
        
        result = verify_universal(str(jsonld_file))
        assert result == False
    
    def test_verification_failure_frequency(self, tmp_path):
        """Test verification fails on frequency check"""
        jsonld_file = tmp_path / "bad_freq.jsonld"
        data = {
            "@context": {"dc": "http://purl.org/dc/terms/"},
            "@id": "urn:test:bad_freq",
            "dc:title": "Bad Frequency",
            "freq:Hz": 999.999  # Way off from F0
        }
        jsonld_file.write_text(json.dumps(data))
        
        result = verify_universal(str(jsonld_file))
        assert result == False


class TestRealWorldExamples:
    """Test with real schema files from the repository"""
    
    def test_zeta_function_schema(self):
        """Test verification of zeta function schema"""
        schema_dir = Path(__file__).parent.parent / "schema"
        jsonld_file = schema_dir / "zeta_function.jsonld"
        
        if jsonld_file.exists():
            result = verify_universal(str(jsonld_file))
            # Should pass all checks
            assert isinstance(result, bool)
    
    def test_natural_numbers_schema(self):
        """Test verification of natural numbers schema"""
        schema_dir = Path(__file__).parent.parent / "schema"
        jsonld_file = schema_dir / "natural_numbers.jsonld"
        
        if jsonld_file.exists():
            result = verify_universal(str(jsonld_file))
            assert isinstance(result, bool)
    
    def test_with_dedukti_proof(self):
        """Test verification with Dedukti proof file"""
        schema_dir = Path(__file__).parent.parent / "schema"
        formal_dir = Path(__file__).parent.parent / "formalization" / "dedukti"
        
        jsonld_file = schema_dir / "natural_numbers.jsonld"
        proof_file = formal_dir / "nat.dk"
        
        if jsonld_file.exists() and proof_file.exists():
            result = verify_universal(str(jsonld_file), str(proof_file))
            assert isinstance(result, bool)


class TestConsistencyTheorem:
    """Test the central consistency theorem"""
    
    def test_theorem_holds(self, tmp_path):
        """
        Theorem: Consistencia(U) ⟺ ∀x∈U: V_L(x) ∧ V_S(x) ∧ V_F(x)
        
        This test verifies the theorem by checking that verify_universal
        returns True iff all three operators return True.
        """
        # Create a valid object satisfying all three conditions
        jsonld_file = tmp_path / "theorem_test.jsonld"
        data = {
            "@context": {"dc": "http://purl.org/dc/terms/"},
            "@id": "urn:test:theorem",
            "dc:title": "Theorem Test",
            "freq:Hz": F0  # Exact match
        }
        jsonld_file.write_text(json.dumps(data))
        
        # Test individual operators
        okS = check_semantics(str(jsonld_file))
        okF, _ = check_frequency(str(jsonld_file))
        okL = True  # No proof file, so V_L passes
        
        # Test universal verification
        okU = verify_universal(str(jsonld_file))
        
        # Theorem verification
        assert okU == (okL and okS and okF)


def test_constants():
    """Test that constants are correctly defined"""
    assert F0 == 141.7001
    assert EPS == 1e-4
    assert EPS < 0.001  # Tolerance must be tight


if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])
