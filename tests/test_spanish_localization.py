#!/usr/bin/env python3
"""
Test Spanish Localization Features
==================================

This test module verifies the Spanish language support and localization
features of the V5 Coronación validation framework.
"""

import subprocess
import sys
import os
import pytest
from pathlib import Path

# Get the repository root directory
REPO_ROOT = Path(__file__).parent.parent

class TestSpanishLocalization:
    """Test Spanish language wrapper and localization features"""
    
    def test_spanish_wrapper_exists(self):
        """Test that the Spanish wrapper script exists and is executable"""
        wrapper_path = REPO_ROOT / "validar_v5_coronacion.py"
        assert wrapper_path.exists(), "Spanish wrapper script should exist"
        assert os.access(wrapper_path, os.R_OK), "Spanish wrapper should be readable"
    
    def test_spanish_help_functionality(self):
        """Test that Spanish help text is displayed correctly"""
        wrapper_path = REPO_ROOT / "validar_v5_coronacion.py"
        
        # Test various help flags
        for help_flag in ["--help", "-h", "--ayuda", "ayuda"]:
            result = subprocess.run([
                sys.executable, str(wrapper_path), help_flag
            ], capture_output=True, text=True, cwd=str(REPO_ROOT))
            
            assert result.returncode == 0, f"Help with {help_flag} should succeed"
            
            # Check for Spanish content in help text
            output = result.stdout.lower()
            spanish_terms = [
                "validador v5 coronación",
                "hipótesis de riemann", 
                "validación completa",
                "sistemas adélicos",
                "josé manuel mota burruezo",
                "precisión decimal",
                "certificado matemático"
            ]
            
            found_terms = [term for term in spanish_terms if term in output]
            assert len(found_terms) >= 4, f"Should find Spanish terms in help output for {help_flag}"
    
    def test_spanish_wrapper_execution(self):
        """Test that the Spanish wrapper successfully executes validation"""
        wrapper_path = REPO_ROOT / "validar_v5_coronacion.py"
        
        # Run a quick validation with low precision
        result = subprocess.run([
            sys.executable, str(wrapper_path), "--precision", "10"
        ], capture_output=True, text=True, cwd=str(REPO_ROOT), timeout=60)
        
        assert result.returncode == 0, "Spanish wrapper validation should succeed"
        
        # Check for expected output patterns
        output = result.stdout
        assert "iniciando validación v5 coronación" in output.lower(), "Should show Spanish initialization message"
        assert "validación v5 coronación completada exitosamente" in output.lower(), "Should show Spanish success message"
        assert "v5 coronación validation: complete success" in output.lower(), "Should show English validation results"
    
    def test_spanish_error_handling(self):
        """Test Spanish error handling for invalid arguments"""
        wrapper_path = REPO_ROOT / "validar_v5_coronacion.py"
        
        # Test with invalid precision argument
        result = subprocess.run([
            sys.executable, str(wrapper_path), "--precision", "invalid"
        ], capture_output=True, text=True, cwd=str(REPO_ROOT))
        
        assert result.returncode != 0, "Invalid arguments should cause failure"
    
    def test_spanish_wrapper_vs_main_script(self):
        """Test that Spanish wrapper produces same validation results as main script"""
        wrapper_path = REPO_ROOT / "validar_v5_coronacion.py"
        main_script_path = REPO_ROOT / "validate_v5_coronacion.py"
        
        # Run both with same parameters
        precision = "10"
        
        # Spanish wrapper
        spanish_result = subprocess.run([
            sys.executable, str(wrapper_path), "--precision", precision
        ], capture_output=True, text=True, cwd=str(REPO_ROOT), timeout=60)
        
        # Main script
        main_result = subprocess.run([
            sys.executable, str(main_script_path), "--precision", precision
        ], capture_output=True, text=True, cwd=str(REPO_ROOT), timeout=60)
        
        # Both should succeed
        assert spanish_result.returncode == 0, "Spanish wrapper should succeed"
        assert main_result.returncode == 0, "Main script should succeed"
        
        # Both should report same validation results (ignoring language-specific messages)
        spanish_output = spanish_result.stdout
        main_output = main_result.stdout
        
        # Check that both contain the main validation success pattern
        success_pattern = "v5 coronación validation: complete success"
        assert success_pattern in spanish_output.lower(), "Spanish wrapper should show success"
        assert success_pattern in main_output.lower(), "Main script should show success"
    
    def test_readme_spanish_content(self):
        """Test that README contains proper Spanish documentation"""
        readme_path = REPO_ROOT / "README.md"
        
        with open(readme_path, 'r', encoding='utf-8') as f:
            readme_content = f.read().lower()
        
        # Check for Spanish documentation sections
        spanish_sections = [
            "validación completa (v5 coronación)",
            "interfaz en español",
            "modos de validación",
            "objetivo científico",
            "estructura del repositorio",
            "ejemplos concretos",
            "resultados esperados"
        ]
        
        for section in spanish_sections:
            assert section in readme_content, f"README should contain Spanish section: {section}"
    
    def test_spanish_terminology_consistency(self):
        """Test that Spanish terminology is used consistently"""
        wrapper_path = REPO_ROOT / "validar_v5_coronacion.py"
        
        with open(wrapper_path, 'r', encoding='utf-8') as f:
            wrapper_content = f.read()
        
        # Check for consistent Spanish terminology
        spanish_terms = {
            "validación": "validation",
            "coronación": "coronación", 
            "hipótesis de riemann": "riemann hypothesis",
            "precisión": "precision",
            "certificado": "certificate",
            "matemático": "mathematical"
        }
        
        for spanish_term, english_equivalent in spanish_terms.items():
            assert spanish_term.lower() in wrapper_content.lower(), f"Should use Spanish term: {spanish_term}"

class TestSpanishIntegration:
    """Test integration between Spanish and English components"""
    
    def test_bilingual_output(self):
        """Test that the system properly handles bilingual output"""
        wrapper_path = REPO_ROOT / "validar_v5_coronacion.py"
        
        result = subprocess.run([
            sys.executable, str(wrapper_path), "--precision", "10"
        ], capture_output=True, text=True, cwd=str(REPO_ROOT), timeout=60)
        
        output = result.stdout.lower()
        
        # Should contain both Spanish wrapper messages and English validation core
        assert "iniciando validación" in output, "Should have Spanish initialization"
        assert "v5 coronación validation" in output, "Should have English validation core"
        assert "validación v5 coronación completada" in output, "Should have Spanish completion"
    
    def test_spanish_command_line_robustness(self):
        """Test robustness of Spanish command line interface"""
        wrapper_path = REPO_ROOT / "validar_v5_coronacion.py"
        
        test_cases = [
            ["--precision", "15"],
            ["--precision", "15", "--verbose"],
            ["--precision", "20", "--save-certificate"],
        ]
        
        for args in test_cases:
            result = subprocess.run([
                sys.executable, str(wrapper_path)
            ] + args, capture_output=True, text=True, cwd=str(REPO_ROOT), timeout=90)
            
            assert result.returncode == 0, f"Spanish wrapper should handle args: {args}"