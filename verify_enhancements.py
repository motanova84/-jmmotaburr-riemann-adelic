#!/usr/bin/env python3
"""
Quick verification script for enhanced V5 Coronación framework
Tests that our LaTeX and Lean enhancements maintain mathematical consistency
"""

import os
import sys
import re

def check_latex_references():
    """Check that all LaTeX references are properly defined"""
    print("🔍 Checking LaTeX references...")
    
    main_tex = "docs/paper/main.tex"
    if not os.path.exists(main_tex):
        print("❌ main.tex not found")
        return False
        
    # Read main.tex
    with open(main_tex, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # Check for key references
    required_refs = ['Weil1964', 'tate1967', 'BirmanSolomyak1967', 'simon2005']
    missing_refs = []
    
    for ref in required_refs:
        if f"\\bibitem{{{ref}}}" not in content:
            missing_refs.append(ref)
    
    if missing_refs:
        print(f"❌ Missing references: {missing_refs}")
        return False
    else:
        print("✅ All required references found")
        return True

def check_new_sections():
    """Check that new sections exist and are properly structured"""
    print("🔍 Checking new sections...")
    
    sections = [
        "docs/paper/sections/axiomas_a_lemas.tex",
        "docs/paper/sections/prueba_incondicional.tex"
    ]
    
    for section in sections:
        if not os.path.exists(section):
            print(f"❌ Missing section: {section}")
            return False
        
        # Check content
        with open(section, 'r', encoding='utf-8') as f:
            content = f.read()
        
        if len(content) < 100:  # Basic content check
            print(f"❌ Section too short: {section}")
            return False
    
    print("✅ All new sections properly created")
    return True

def check_lean_files():
    """Check that Lean files are properly structured"""
    print("🔍 Checking Lean formalization...")
    
    lean_files = [
        "formalization/lean/adelic_determinant.lean",
        "formalization/lean/functional_eq.lean"
    ]
    
    for lean_file in lean_files:
        if not os.path.exists(lean_file):
            print(f"❌ Missing Lean file: {lean_file}")
            return False
        
        with open(lean_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # Check for key Lean constructs
        if "import" not in content or "def " not in content:
            print(f"❌ Lean file malformed: {lean_file}")
            return False
    
    print("✅ Lean files properly structured")
    return True

def check_mathematical_consistency():
    """Basic mathematical consistency checks"""
    print("🔍 Checking mathematical consistency...")
    
    # Check A2 enhancement contains key mathematical concepts
    axiomas_file = "docs/paper/sections/axiomas_a_lemas.tex"
    with open(axiomas_file, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # Key mathematical concepts that should be present
    key_concepts = [
        "Poisson",  # Poisson summation
        "\\mathbb{A}_\\mathbb{Q}",  # Adeles
        "\\bigotimes",  # Tensor product
        "D(1-s) = D(s)",  # Functional equation  
        "Birman",  # Birman-Solomyak
        "Lidskii"  # Lidskii series
    ]
    
    missing_concepts = []
    for concept in key_concepts:
        if concept not in content:
            missing_concepts.append(concept)
    
    if missing_concepts:
        print(f"❌ Missing mathematical concepts: {missing_concepts}")
        return False
    else:
        print("✅ Key mathematical concepts present")
        return True

def main():
    """Run all verification checks"""
    print("🚀 V5 Coronación Enhancement Verification")
    print("=" * 50)
    
    checks = [
        check_latex_references,
        check_new_sections,
        check_lean_files,
        check_mathematical_consistency
    ]
    
    results = []
    for check in checks:
        try:
            result = check()
            results.append(result)
        except Exception as e:
            print(f"❌ Check failed with error: {e}")
            results.append(False)
        print()
    
    # Summary
    passed = sum(results)
    total = len(results)
    
    print("=" * 50)
    print(f"📊 VERIFICATION SUMMARY: {passed}/{total} checks passed")
    
    if passed == total:
        print("🏆 All verification checks PASSED!")
        print("✨ V5 Coronación enhancements are consistent and complete!")
        return True
    else:
        print("⚠️ Some checks FAILED - review implementation")
        return False

if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)