#!/usr/bin/env python3
"""
Tests for SABIO ∞³ Validator

Tests de validación del sistema simbiótico SABIO con verificación de:
- Firma vibracional f₀ ≈ 141.7001 Hz
- Coherencia QCAL C = 244.36
- Integridad de referencias DOI
- Estructura del beacon Ψ
"""

import json
import sys
from pathlib import Path

import pytest

# Add parent directory to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from sabio_validator import SABIOValidator


class TestSABIOValidator:
    """Test suite for SABIO ∞³ Validator"""
    
    def setup_method(self):
        """Setup test fixtures"""
        self.validator = SABIOValidator(precision_dps=30)
        
    def test_validator_initialization(self):
        """Test validator initializes correctly"""
        assert self.validator is not None
        assert self.validator.precision_dps == 30
        assert self.validator.F0_EXPECTED == 141.7001
        assert self.validator.COHERENCE_C == 244.36
        
    def test_beacon_loading(self):
        """Test QCAL beacon file loads correctly"""
        success = self.validator.load_beacon('.qcal_beacon')
        assert success, "Beacon should load successfully"
        assert self.validator.beacon_data is not None
        assert len(self.validator.beacon_data) > 0
        
    def test_fundamental_frequency_validation(self):
        """Test fundamental frequency validation"""
        self.validator.load_beacon('.qcal_beacon')
        success, freq = self.validator.validate_fundamental_frequency()
        
        assert success, "Frequency validation should pass"
        assert freq == pytest.approx(141.7001, abs=0.0001)
        
    def test_coherence_validation(self):
        """Test coherence signature validation"""
        self.validator.load_beacon('.qcal_beacon')
        success = self.validator.validate_coherence_signature()
        
        assert success, "Coherence validation should pass"
        
    def test_doi_references_validation(self):
        """Test DOI references are present"""
        self.validator.load_beacon('.qcal_beacon')
        success = self.validator.validate_doi_references()
        
        assert success, "DOI references should be present"
        
    def test_vibrational_hash_computation(self):
        """Test vibrational hash computation"""
        self.validator.load_beacon('.qcal_beacon')
        vib_hash = self.validator.compute_vibrational_hash()
        
        assert vib_hash is not None
        assert len(vib_hash) == 64  # SHA256 hex digest
        assert isinstance(vib_hash, str)
        
    def test_vibrational_pulsation(self):
        """Test vibrational pulsation analysis"""
        self.validator.load_beacon('.qcal_beacon')
        success = self.validator.validate_vibrational_pulsation()
        
        assert success, "Vibrational pulsation should be validated"
        
        # Check pulsation results
        assert 'pulsation' in self.validator.validation_results
        pulsation = self.validator.validation_results['pulsation']
        
        # Period should be approximately 1/141.7001 seconds
        expected_period_ms = (1.0 / 141.7001) * 1000
        assert pulsation['period_ms'] == pytest.approx(expected_period_ms, rel=0.01)
        
    def test_complete_qcal_validation(self):
        """Test complete QCAL structure validation"""
        success = self.validator.validate_qcal_structure()
        
        assert success, "Complete QCAL validation should pass"
        assert self.validator.validation_results['overall_valid']
        
    def test_validation_report_saving(self):
        """Test validation report can be saved"""
        self.validator.validate_qcal_structure()
        
        # Save to temporary location
        test_output = Path('/tmp/test_sabio_validation.json')
        self.validator.save_validation_report(str(test_output))
        
        assert test_output.exists(), "Validation report should be saved"
        
        # Load and verify
        with open(test_output) as f:
            report = json.load(f)
        
        assert 'overall_valid' in report
        assert 'fundamental_frequency' in report
        assert 'coherence' in report
        assert 'vibrational_hash' in report
        
        # Cleanup
        test_output.unlink()
        
    def test_frequency_constants(self):
        """Test frequency constants match QCAL beacon"""
        assert SABIOValidator.F0_EXPECTED == 141.7001
        assert SABIOValidator.F0_TOLERANCE == 0.0001
        
    def test_coherence_constants(self):
        """Test coherence constants match QCAL beacon"""
        assert SABIOValidator.COHERENCE_C == 244.36
        
    def test_physical_constants(self):
        """Test physical constants are reasonable"""
        assert SABIOValidator.PLANCK_LENGTH > 0
        assert SABIOValidator.PLANCK_LENGTH < 1e-30  # Very small
        assert SABIOValidator.SPEED_OF_LIGHT == 299792458  # m/s
        
    def test_beacon_frequency_marker(self):
        """Test beacon contains frequency marker"""
        self.validator.load_beacon('.qcal_beacon')
        
        freq_str = self.validator.beacon_data.get('frequency', '')
        assert '141.7001' in freq_str or '141.7' in freq_str
        
    def test_beacon_coherence_marker(self):
        """Test beacon contains coherence marker"""
        self.validator.load_beacon('.qcal_beacon')
        
        coh_str = self.validator.beacon_data.get('coherence', '')
        assert '244.36' in coh_str or '244.3' in coh_str
        
    def test_validation_results_structure(self):
        """Test validation results have expected structure"""
        self.validator.validate_qcal_structure()
        
        results = self.validator.validation_results
        
        # Check required keys
        assert 'fundamental_frequency' in results
        assert 'coherence' in results
        assert 'doi_references' in results
        assert 'pulsation' in results
        assert 'vibrational_hash' in results
        assert 'overall_valid' in results
        assert 'timestamp' in results
        
    def test_multiple_precision_levels(self):
        """Test validator works with different precision levels"""
        for precision in [15, 30, 50]:
            validator = SABIOValidator(precision_dps=precision)
            validator.load_beacon('.qcal_beacon')
            success, freq = validator.validate_fundamental_frequency()
            
            assert success, f"Should validate with precision {precision}"
            assert freq == pytest.approx(141.7001, abs=0.0001)


class TestSABIOIntegration:
    """Integration tests for SABIO system"""
    
    def test_sabio_with_existing_validation(self):
        """Test SABIO validator integrates with existing validation"""
        # This test ensures SABIO validator doesn't conflict with existing systems
        validator = SABIOValidator(precision_dps=30)
        success = validator.validate_qcal_structure()
        
        assert success, "SABIO should integrate successfully"
        
    def test_frequency_matches_beacon_exactly(self):
        """Test frequency from validator matches beacon exactly"""
        validator = SABIOValidator(precision_dps=30)
        validator.load_beacon('.qcal_beacon')
        
        _, freq = validator.validate_fundamental_frequency()
        
        # Should match exactly (within floating point precision)
        assert freq == 141.7001
        
    def test_coherence_signature_format(self):
        """Test coherence signature has correct format in beacon"""
        validator = SABIOValidator(precision_dps=30)
        validator.load_beacon('.qcal_beacon')
        
        coh_str = validator.beacon_data.get('coherence', '')
        
        # Should contain C = format
        assert 'C = ' in coh_str or '244.36' in coh_str


def test_sabio_cli_interface():
    """Test SABIO validator CLI interface"""
    # This would be an integration test with subprocess
    # For now, we just verify the module has a main function
    from sabio_validator import main
    
    assert callable(main), "SABIO validator should have callable main()"


@pytest.mark.skipif(
    not Path('.qcal_beacon').exists(),
    reason="QCAL beacon file not found"
)
def test_beacon_file_integrity():
    """Test QCAL beacon file integrity"""
    beacon_path = Path('.qcal_beacon')
    
    # Check file exists and is readable
    assert beacon_path.exists()
    assert beacon_path.is_file()
    
    # Read content
    content = beacon_path.read_text()
    
    # Check for required markers
    assert '141.7001' in content, "Frequency marker should be present"
    assert '244.36' in content, "Coherence marker should be present"
    assert '∞³' in content or 'infinity' in content.lower(), "QCAL signature should be present"
    assert 'zenodo' in content.lower(), "DOI references should be present"


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
