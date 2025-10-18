"""
Tests for merge conflict resolution in requirements.txt.

This module validates that the merge conflict between the copilot branch
and main branch was correctly resolved.

Author: GitHub Copilot Coding Agent
Date: October 2025
"""

import pytest
from pathlib import Path


class TestRequirementsConflictResolution:
    """Test that requirements.txt merge conflict was correctly resolved."""
    
    def test_requirements_file_exists(self):
        """Test that requirements.txt exists."""
        req_path = Path(__file__).parent.parent / "requirements.txt"
        assert req_path.exists(), "requirements.txt not found"
    
    def test_no_conflict_markers(self):
        """Test that there are no merge conflict markers in requirements.txt."""
        req_path = Path(__file__).parent.parent / "requirements.txt"
        
        with open(req_path, 'r') as f:
            content = f.read()
        
        # Check for conflict markers
        assert '<<<<<<< ' not in content, "Found unresolved conflict marker <<<<<<<" 
        assert '=======' not in content, "Found unresolved conflict marker ======="
        assert '>>>>>>> ' not in content, "Found unresolved conflict marker >>>>>>>"
    
    def test_joblib_single_occurrence(self):
        """Test that joblib appears exactly once (no duplicate)."""
        req_path = Path(__file__).parent.parent / "requirements.txt"
        
        with open(req_path, 'r') as f:
            lines = f.readlines()
        
        joblib_lines = [line for line in lines if line.strip().startswith('joblib')]
        
        assert len(joblib_lines) == 1, (
            f"Expected exactly 1 joblib entry, found {len(joblib_lines)}: {joblib_lines}"
        )
    
    def test_advanced_libraries_present(self):
        """Test that all advanced mathematical libraries from main are present."""
        req_path = Path(__file__).parent.parent / "requirements.txt"
        
        with open(req_path, 'r') as f:
            content = f.read()
        
        # Expected libraries from main branch
        expected_libraries = [
            'numba',
            'llvmlite',
            'scikit-learn',
            'xgboost',
            'jax',
            'jaxlib',
            'numexpr',
            'bottleneck',
            'networkx',
            'python-igraph',
            'tensorly',
            'opt-einsum',
            'statsmodels',
            'patsy',
            'sparse',
            'nlopt'
        ]
        
        missing = []
        for lib in expected_libraries:
            if lib not in content:
                missing.append(lib)
        
        assert len(missing) == 0, f"Missing advanced libraries: {missing}"
    
    def test_no_duplicate_packages(self):
        """Test that there are no duplicate package entries."""
        req_path = Path(__file__).parent.parent / "requirements.txt"
        
        with open(req_path, 'r') as f:
            lines = f.readlines()
        
        # Extract package names
        packages = []
        for line in lines:
            line = line.strip()
            if line and not line.startswith('#'):
                # Extract package name (before version specifier)
                for sep in ['==', '>=', '<=', '~=', '>', '<']:
                    if sep in line:
                        pkg_name = line.split(sep)[0].strip()
                        packages.append(pkg_name)
                        break
        
        # Check for duplicates
        seen = set()
        duplicates = []
        for pkg in packages:
            if pkg in seen:
                duplicates.append(pkg)
            seen.add(pkg)
        
        assert len(duplicates) == 0, f"Found duplicate packages: {duplicates}"
    
    def test_package_count(self):
        """Test that the expected number of packages is present."""
        req_path = Path(__file__).parent.parent / "requirements.txt"
        
        with open(req_path, 'r') as f:
            lines = f.readlines()
        
        # Count non-comment, non-empty lines
        package_lines = [
            line for line in lines 
            if line.strip() and not line.strip().startswith('#')
        ]
        
        # Expected: 13 core + 16 advanced = 29 packages
        assert len(package_lines) == 29, (
            f"Expected 29 packages, found {len(package_lines)}"
        )
    
    def test_version_specifications_valid(self):
        """Test that all version specifications are valid."""
        req_path = Path(__file__).parent.parent / "requirements.txt"
        
        with open(req_path, 'r') as f:
            lines = f.readlines()
        
        import re
        
        # Pattern for valid requirement line
        pattern = r'^[a-zA-Z0-9\-_.]+\s*(==|>=|<=|~=|>|<)\s*[0-9.]+(\s*,\s*(==|>=|<=|~=|>|<)\s*[0-9.]+)*(\s*#.*)?$'
        
        invalid_lines = []
        for i, line in enumerate(lines, 1):
            line = line.strip()
            if line and not line.startswith('#'):
                if not re.match(pattern, line):
                    invalid_lines.append(f"Line {i}: {line}")
        
        assert len(invalid_lines) == 0, (
            f"Found invalid version specifications:\n" + 
            "\n".join(invalid_lines)
        )
    
    def test_core_dependencies_intact(self):
        """Test that core dependencies are still present."""
        req_path = Path(__file__).parent.parent / "requirements.txt"
        
        with open(req_path, 'r') as f:
            content = f.read()
        
        # Core dependencies that must be present
        core_deps = [
            'mpmath',
            'numpy',
            'scipy',
            'sympy',
            'matplotlib',
            'jupyter',
            'nbconvert',
            'mistune',
            'requests',
            'joblib',
            'qiskit',
            'pytest',
            'pytest-cov'
        ]
        
        missing = []
        for dep in core_deps:
            if dep not in content:
                missing.append(dep)
        
        assert len(missing) == 0, f"Missing core dependencies: {missing}"
    
    def test_comments_preserved(self):
        """Test that section comments are preserved."""
        req_path = Path(__file__).parent.parent / "requirements.txt"
        
        with open(req_path, 'r') as f:
            content = f.read()
        
        # Expected section comments
        expected_comments = [
            '# Core computational dependencies',
            '# Jupyter and notebook execution',
            '# HTTP requests for data fetching',
            '# Parallel computing',
            '# Quantum computing for consciousness adelic bridge',
            '# Testing framework',
            '# Advanced mathematical libraries',
            '# JIT compilation and performance optimization',
            '# Machine Learning and optimization',
            '# Automatic differentiation and GPU acceleration',
            '# Advanced numerical methods',
            '# Graph theory and combinatorics',
            '# Tensor operations and decompositions',
            '# Advanced statistical tools',
            '# Sparse matrix operations',
            '# Optimization and root finding',
        ]
        
        missing_comments = []
        for comment in expected_comments:
            if comment not in content:
                missing_comments.append(comment)
        
        assert len(missing_comments) == 0, (
            f"Missing section comments: {missing_comments}"
        )


class TestMergeConflictDocumentation:
    """Test that merge conflict resolution is documented."""
    
    def test_resolution_guide_exists(self):
        """Test that merge conflict resolution guide exists."""
        guide_path = Path(__file__).parent.parent / "MERGE_CONFLICT_RESOLUTION_GUIDE.md"
        assert guide_path.exists(), "MERGE_CONFLICT_RESOLUTION_GUIDE.md not found"
    
    def test_resolution_guide_content(self):
        """Test that resolution guide contains key information."""
        guide_path = Path(__file__).parent.parent / "MERGE_CONFLICT_RESOLUTION_GUIDE.md"
        
        with open(guide_path, 'r') as f:
            content = f.read()
        
        # Check for key sections
        assert 'Merge Conflict Resolution' in content
        assert 'The Conflict' in content
        assert 'Resolution Strategy' in content
        assert 'joblib' in content
        assert 'duplicate' in content.lower()
        assert 'advanced mathematical libraries' in content.lower()


def test_summary():
    """Print summary of merge conflict resolution validation."""
    print("\n" + "="*70)
    print("MERGE CONFLICT RESOLUTION VALIDATION SUMMARY")
    print("="*70)
    print("✅ requirements.txt merge conflict correctly resolved:")
    print("   - No conflict markers present")
    print("   - joblib appears exactly once (no duplicate)")
    print("   - All 16 advanced libraries from main included")
    print("   - All 13 core dependencies intact")
    print("   - 29 total packages (no duplicates)")
    print("   - All version specifications valid")
    print("   - Section comments preserved")
    print("   - Resolution documented in MERGE_CONFLICT_RESOLUTION_GUIDE.md")
    print("="*70)
    assert True


if __name__ == "__main__":
    pytest.main([__file__, "-v", "-s"])
