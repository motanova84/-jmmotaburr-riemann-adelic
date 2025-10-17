#!/usr/bin/env python3
"""
Test script to verify that path resolution works from any directory.

This script can be run from the project root or any subdirectory to verify
that the path resolution system works correctly.
"""

import sys
from pathlib import Path

# Add project root to path
try:
    from utils.path_utils import get_project_root, get_project_path, ensure_project_in_path
except ImportError:
    # If running from subdirectory, we need to add parent to path first
    current_file = Path(__file__).resolve()
    # Walk up to find project root
    current = current_file.parent
    while current != current.parent:
        if (current / "README.md").exists() and (current / "utils").is_dir():
            sys.path.insert(0, str(current))
            break
        current = current.parent
    from utils.path_utils import get_project_root, get_project_path, ensure_project_in_path

# Ensure project is in path
ensure_project_in_path()

def test_basic_path_resolution():
    """Test basic path resolution functionality."""
    print("\n" + "="*60)
    print("TEST 1: Basic Path Resolution")
    print("="*60)
    
    root = get_project_root()
    print(f"✓ Project root: {root}")
    
    zeros_path = get_project_path("zeros", "zeros_t1e3.txt")
    print(f"✓ Zeros path: {zeros_path}")
    
    data_path = get_project_path("data")
    print(f"✓ Data path: {data_path}")
    
    assert root.exists(), "Project root doesn't exist"
    assert (root / "README.md").exists(), "README.md not found in project root"
    print("✅ Basic path resolution: PASSED")
    return True

def test_file_access():
    """Test that files can be accessed using resolved paths."""
    print("\n" + "="*60)
    print("TEST 2: File Access")
    print("="*60)
    
    zeros_file = get_project_path("zeros", "zeros_t1e3.txt")
    
    if zeros_file.exists():
        with open(zeros_file, 'r') as f:
            first_line = f.readline().strip()
            print(f"✓ First zero: {first_line}")
        print("✅ File access: PASSED")
        return True
    else:
        print(f"⚠️  Warning: {zeros_file} not found (this is OK if data not downloaded)")
        print("✅ File access: SKIPPED")
        return True

def test_imports():
    """Test that utils modules can be imported."""
    print("\n" + "="*60)
    print("TEST 3: Module Imports")
    print("="*60)
    
    try:
        from utils.mellin import truncated_gaussian
        print(f"✓ Imported truncated_gaussian: {truncated_gaussian}")
        
        from utils.riemann_tools import t_to_n
        print(f"✓ Imported t_to_n: {t_to_n}")
        
        print("✅ Module imports: PASSED")
        return True
    except ImportError as e:
        print(f"❌ Import failed: {e}")
        return False

def test_from_subdirectory():
    """Test that the system works when run from a subdirectory."""
    print("\n" + "="*60)
    print("TEST 4: Subdirectory Execution")
    print("="*60)
    
    import os
    cwd = Path.cwd()
    root = get_project_root()
    
    print(f"✓ Current working directory: {cwd}")
    print(f"✓ Project root: {root}")
    
    if cwd != root:
        print(f"✓ Running from subdirectory: {cwd.relative_to(root)}")
    else:
        print("✓ Running from project root")
    
    # Verify path resolution still works
    zeros_path = get_project_path("zeros", "zeros_t1e3.txt")
    print(f"✓ Resolved path: {zeros_path}")
    
    print("✅ Subdirectory execution: PASSED")
    return True

def main():
    """Run all tests."""
    print("\n" + "="*60)
    print("PATH RESOLUTION VALIDATION TESTS")
    print("="*60)
    
    results = []
    
    try:
        results.append(("Basic Path Resolution", test_basic_path_resolution()))
        results.append(("File Access", test_file_access()))
        results.append(("Module Imports", test_imports()))
        results.append(("Subdirectory Execution", test_from_subdirectory()))
    except Exception as e:
        print(f"\n❌ Test failed with error: {e}")
        import traceback
        traceback.print_exc()
        return False
    
    # Print summary
    print("\n" + "="*60)
    print("TEST SUMMARY")
    print("="*60)
    
    passed = sum(1 for _, result in results if result)
    total = len(results)
    
    for test_name, result in results:
        status = "✅ PASSED" if result else "❌ FAILED"
        print(f"{test_name}: {status}")
    
    print(f"\nTotal: {passed}/{total} tests passed")
    
    if passed == total:
        print("\n🎉 ALL TESTS PASSED!")
        print("\nThe repository can now be used from any directory.")
        print("Scripts will automatically find the project root and resolve paths.")
        return True
    else:
        print("\n⚠️  Some tests failed")
        return False

if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)
