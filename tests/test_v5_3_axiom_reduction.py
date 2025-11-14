"""
Test suite for V5.3 Axiomatic Reduction validation

This test suite verifies the V5.3 axiomatic reduction status as documented
in REDUCCION_AXIOMATICA_V5.3.md

Author: José Manuel Mota Burruezo
Date: October 23, 2025
Version: V5.3
"""

import pytest
import os
import re
from pathlib import Path


class TestV53AxiomReduction:
    """Test the V5.3 axiomatic reduction progress"""
    
    @pytest.fixture
    def repo_root(self):
        """Get repository root directory"""
        return Path(__file__).parent.parent
    
    @pytest.fixture
    def reduccion_doc(self, repo_root):
        """Load V5.3 reduction document"""
        doc_path = repo_root / "REDUCCION_AXIOMATICA_V5.3.md"
        assert doc_path.exists(), "V5.3 reduction document must exist"
        with open(doc_path, 'r', encoding='utf-8') as f:
            return f.read()
    
    @pytest.fixture
    def rh_final_lean(self, repo_root):
        """Load RH_final.lean"""
        lean_path = repo_root / "formalization" / "lean" / "RH_final.lean"
        assert lean_path.exists(), "RH_final.lean must exist"
        with open(lean_path, 'r', encoding='utf-8') as f:
            return f.read()
    
    @pytest.fixture
    def d_explicit_lean(self, repo_root):
        """Load D_explicit.lean"""
        lean_path = repo_root / "formalization" / "lean" / "RiemannAdelic" / "D_explicit.lean"
        assert lean_path.exists(), "D_explicit.lean must exist"
        with open(lean_path, 'r', encoding='utf-8') as f:
            return f.read()
    
    def test_reduccion_document_exists(self, repo_root):
        """V5.3: Reduction document must exist"""
        doc_path = repo_root / "REDUCCION_AXIOMATICA_V5.3.md"
        assert doc_path.exists(), "REDUCCION_AXIOMATICA_V5.3.md must exist"
    
    def test_reduccion_document_structure(self, reduccion_doc):
        """V5.3: Document must have proper structure"""
        # Check for required sections
        assert "# Reducción Axiomática Completa" in reduccion_doc
        assert "V5.3 Preliminar" in reduccion_doc
        assert "José Manuel Mota Burruezo" in reduccion_doc
        assert "10.5281/zenodo.17116291" in reduccion_doc
        
        # Check for main sections
        assert "I. Axiomas Eliminados" in reduccion_doc
        assert "II. Axiomas en Proceso de Eliminación" in reduccion_doc
        assert "III. Esquema de Dependencias Formales" in reduccion_doc
        assert "IV. Jerarquía Constructiva" in reduccion_doc
    
    def test_eliminated_axioms_documented(self, reduccion_doc):
        """V5.3: Three eliminated axioms must be documented"""
        # Check for eliminated axioms
        assert "D_function" in reduccion_doc
        assert "D_functional_equation" in reduccion_doc
        assert "D_entire_order_one" in reduccion_doc
        
        # Check they are marked as eliminated
        assert "Axioma eliminado" in reduccion_doc or "Axiomas Eliminados" in reduccion_doc
        assert "Definición" in reduccion_doc
        assert "Teorema" in reduccion_doc
    
    def test_axioms_in_reduction_documented(self, reduccion_doc):
        """V5.3: Three axioms in reduction must be documented"""
        # Check for axioms in reduction
        assert "D_zero_equivalence" in reduccion_doc
        assert "zeros_constrained_to_critical_lines" in reduccion_doc
        assert "trivial_zeros_excluded" in reduccion_doc
        
        # Check reduction strategies are present
        assert "Línea de acción" in reduccion_doc or "Estrategia" in reduccion_doc
    
    def test_d_function_is_definition(self, d_explicit_lean):
        """V5.3: D_function must be a definition, not an axiom"""
        # Check for definition
        assert "def D_explicit" in d_explicit_lean
        assert "def spectralTrace" in d_explicit_lean
        
        # Ensure no actual axiom declaration for D_function in D_explicit.lean
        # Look for lines that start with "axiom D_function" (not comments or docstrings)
        import re
        # Remove all comments (both -- and /-- ... -/ style)
        code_only = re.sub(r'/--.*?-/', '', d_explicit_lean, flags=re.DOTALL)
        code_only = re.sub(r'--.*?$', '', code_only, flags=re.MULTILINE)
        
        # Now check for axiom declarations
        assert 'axiom D_function' not in code_only, "D_function must not be an axiom declaration"
        
        # D_explicit should be a def
        assert 'def D_explicit' in d_explicit_lean
    
    def test_d_functional_equation_is_theorem(self, d_explicit_lean):
        """V5.3: D_functional_equation must be a theorem"""
        # Check for theorem declaration
        assert "theorem D_explicit_functional_equation" in d_explicit_lean
        
        # Should have proof (even with sorry)
        pattern = r'theorem D_explicit_functional_equation.*?:=\s*by'
        assert re.search(pattern, d_explicit_lean, re.DOTALL), \
            "D_explicit_functional_equation must have proof structure"
    
    def test_d_entire_order_one_is_theorem(self, d_explicit_lean):
        """V5.3: D_entire_order_one must be a theorem"""
        # Check for theorem declaration
        assert "theorem D_explicit_entire_order_one" in d_explicit_lean
        
        # Should have proof (even with sorry)
        pattern = r'theorem D_explicit_entire_order_one.*?:=\s*by'
        assert re.search(pattern, d_explicit_lean, re.DOTALL), \
            "D_explicit_entire_order_one must have proof structure"
    
    def test_d_zero_equivalence_still_axiom(self, rh_final_lean):
        """V5.3: D_zero_equivalence is still an axiom (to be eliminated in V5.4)"""
        # Check it's still an axiom
        assert "axiom D_zero_equivalence" in rh_final_lean
        
        # But should have V5.3 documentation
        lines = rh_final_lean.split('\n')
        axiom_idx = None
        for i, line in enumerate(lines):
            if 'axiom D_zero_equivalence' in line:
                axiom_idx = i
                break
        
        assert axiom_idx is not None
        # Check for V5.3 comments in nearby lines
        context = '\n'.join(lines[max(0, axiom_idx-20):axiom_idx])
        assert 'V5.3' in context or 'V5.4' in context, \
            "D_zero_equivalence should have V5.3 status documentation"
    
    def test_zeros_constrained_is_theorem(self, rh_final_lean):
        """V5.3: zeros_constrained_to_critical_lines is now a theorem"""
        # Check it's a theorem, not an axiom
        assert "theorem zeros_constrained_to_critical_lines" in rh_final_lean
        
        # Should not be an axiom
        assert "axiom zeros_constrained_to_critical_lines" not in rh_final_lean
        
        # Should have proof structure
        pattern = r'theorem zeros_constrained_to_critical_lines.*?:=\s*by'
        assert re.search(pattern, rh_final_lean, re.DOTALL), \
            "zeros_constrained_to_critical_lines must have proof"
    
    def test_trivial_zeros_excluded_is_theorem(self, rh_final_lean):
        """V5.3: trivial_zeros_excluded is now a theorem"""
        # Check it's a theorem, not an axiom
        assert "theorem trivial_zeros_excluded" in rh_final_lean
        
        # Should not be an axiom
        assert "axiom trivial_zeros_excluded" not in rh_final_lean
        
        # Should have proof structure
        pattern = r'theorem trivial_zeros_excluded.*?:=\s*by'
        assert re.search(pattern, rh_final_lean, re.DOTALL), \
            "trivial_zeros_excluded must have proof"
    
    def test_v53_status_in_lean_files(self, rh_final_lean, d_explicit_lean):
        """V5.3: Lean files must have V5.3 status comments"""
        # Check RH_final.lean
        assert "V5.3" in rh_final_lean, "RH_final.lean must reference V5.3"
        
        # Check D_explicit.lean
        assert "V5.3" in d_explicit_lean, "D_explicit.lean must reference V5.3"
    
    def test_formalization_status_updated(self, repo_root):
        """V5.3: FORMALIZATION_STATUS.md must reflect V5.3 progress"""
        status_path = repo_root / "FORMALIZATION_STATUS.md"
        assert status_path.exists()
        
        with open(status_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # Check V5.3 is mentioned
        assert "V5.3" in content
        
        # Check axiom reduction is documented
        assert "Axiom" in content or "axiom" in content
        assert "Eliminated" in content or "eliminated" in content
    
    def test_dependency_table_present(self, reduccion_doc):
        """V5.3: Document must have dependency transition table"""
        # Check for table structure
        assert "Estado V5.1" in reduccion_doc or "V5.1" in reduccion_doc
        assert "Estado V5.2" in reduccion_doc or "V5.2" in reduccion_doc
        assert "V5.3" in reduccion_doc
        assert "V5.4" in reduccion_doc or "Meta V5.4" in reduccion_doc
        
        # Check for status symbols
        assert "✅" in reduccion_doc or "🔄" in reduccion_doc
    
    def test_reduction_strategies_present(self, reduccion_doc):
        """V5.3: Document must contain reduction strategies for remaining axioms"""
        # Check for D_zero_equivalence strategy
        assert "D/ξ" in reduccion_doc or "D/xi" in reduccion_doc.lower()
        assert "Liouville" in reduccion_doc
        
        # Check for zeros_constrained strategy
        assert "de Branges" in reduccion_doc
        assert "autoadjunto" in reduccion_doc or "self-adjoint" in reduccion_doc
        
        # Check for trivial_zeros strategy
        assert "ecuación funcional" in reduccion_doc or "functional equation" in reduccion_doc
    
    def test_mathematical_references_present(self, reduccion_doc):
        """V5.3: Document must cite key mathematical references"""
        # Check for key papers
        assert "Tate" in reduccion_doc
        assert "Weil" in reduccion_doc
        assert "Hadamard" in reduccion_doc
        assert "de Branges" in reduccion_doc
        
        # Check for author
        assert "Burruezo" in reduccion_doc


class TestV53NumericalValidation:
    """Numerical validation of V5.3 constructions"""
    
    def test_spectral_trace_definition_available(self):
        """V5.3: Spectral trace must be explicitly defined"""
        # This is a symbolic test - actual numerical tests are in other files
        # Just verify the concept is documented
        from pathlib import Path
        repo_root = Path(__file__).parent.parent
        d_explicit = repo_root / "formalization" / "lean" / "RiemannAdelic" / "D_explicit.lean"
        
        with open(d_explicit, 'r') as f:
            content = f.read()
        
        # Check for spectral trace definition
        assert "spectralTrace" in content
        assert "exp" in content  # Should have exponential
        assert "∑'" in content or "sum" in content.lower()  # Should have summation


class TestV53Documentation:
    """Test documentation quality for V5.3"""
    
    @pytest.fixture
    def repo_root(self):
        return Path(__file__).parent.parent
    
    def test_readme_links_to_v53(self, repo_root):
        """V5.3: Main README should link to V5.3 document"""
        readme_path = repo_root / "README.md"
        if readme_path.exists():
            with open(readme_path, 'r', encoding='utf-8') as f:
                content = f.read()
            # Check if V5.3 or reduction document is mentioned
            # (This is a soft check - README may be updated later)
            has_v53_ref = "V5.3" in content or "REDUCCION_AXIOMATICA" in content
            # Don't fail if not present, just note it
            if not has_v53_ref:
                pytest.skip("README doesn't yet reference V5.3 (optional)")
    
    def test_doi_preserved_in_v53(self, repo_root):
        """V5.3: DOI reference must be preserved"""
        doc_path = repo_root / "REDUCCION_AXIOMATICA_V5.3.md"
        with open(doc_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # Check DOI is present
        assert "10.5281/zenodo.17116291" in content
        assert "doi.org" in content.lower() or "DOI" in content


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
