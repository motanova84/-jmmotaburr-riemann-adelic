#!/usr/bin/env python3
"""
System dependency validator for advanced mathematical environments.
Author: José Manuel Mota Burruezo
Date: October 2025
"""

import sys
import subprocess
from datetime import datetime
from pathlib import Path

LOG_PATH = Path("system_validation.log")

def log(msg):
    print(msg)
    with LOG_PATH.open("a", encoding="utf-8") as f:
        f.write(msg + "\n")

def print_header(title):
    log("\n" + "=" * 70)
    log(f"  {title}")
    log("=" * 70)

def check_python_package(pkg, import_name=None):
    if import_name is None:
        import_name = pkg
    try:
        mod = __import__(import_name)
        version = getattr(mod, "__version__", "unknown")
        log(f"  [OK] {pkg:20s} : {version}")
        return True
    except ImportError:
        log(f"  [FAIL] {pkg:20s} : NOT INSTALLED")
        return False

def check_system_command(cmd, pkg_hint=None):
    try:
        result = subprocess.run(
            [cmd, "--version"],
            capture_output=True,
            text=True,
            timeout=5
        )
        if result.returncode == 0:
            first = result.stdout.strip().split("\n")[0]
            log(f"  [OK] {cmd:20s} : {first}")
            return True
        else:
            log(f"  [WARN] {cmd:20s} : NOT FOUND")
            if pkg_hint:
                log(f"         Install with: sudo apt-get install {pkg_hint}")
            return False
    except FileNotFoundError:
        log(f"  [WARN] {cmd:20s} : NOT FOUND")
        if pkg_hint:
            log(f"         Install with: sudo apt-get install {pkg_hint}")
        return False
    except Exception as e:
        log(f"  [ERR] {cmd:20s} : ERROR ({e})")
        return False

def check_llvm_binding():
    try:
        from llvmlite import binding
        binding.initialize_native_target()
        binding.initialize_native_asmprinter()
        t = binding.Target.from_default_triple()
        log(f"  [OK] LLVM binding       : {t.triple}")
        return True
    except Exception as e:
        log(f"  [FAIL] LLVM binding       : {e}")
        return False

def check_numba_jit():
    try:
        from numba import jit
        import numpy as np
        @jit(nopython=True)
        def f(x): return x * x
        assert f(5.0) == 25.0
        log(f"  [OK] numba JIT          : working")
        return True
    except Exception as e:
        log(f"  [FAIL] numba JIT          : {e}")
        return False

def check_igraph_c_library():
    try:
        import igraph
        g = igraph.Graph([(0, 1), (1, 2)])
        assert g.vcount() == 3 and g.ecount() == 2
        log(f"  [OK] igraph C library   : working")
        return True
    except Exception as e:
        log(f"  [FAIL] igraph C library   : {e}")
        return False

def check_numexpr_eval():
    try:
        import numexpr as ne
        import numpy as np
        x = np.array([1.0, 2.0, 3.0])
        y = ne.evaluate("x**2")
        assert np.allclose(y, [1,4,9])
        log(f"  [OK] numexpr evaluation : working ({ne.detect_number_of_cores()} cores)")
        return True
    except Exception as e:
        log(f"  [FAIL] numexpr evaluation : {e}")
        return False

def main():
    LOG_PATH.write_text(f"System Validation Log - {datetime.now().isoformat()}\n\n", encoding="utf-8")

    print_header("SYSTEM DEPENDENCIES VALIDATION")
    log(f"Python version: {sys.version.split()[0]}")
    log(f"Platform: {sys.platform}")

    results = []
    print_header("Python Packages")
    for pkg in [
        ("numpy", None), ("scipy", None), ("mpmath", None),
        ("llvmlite", None), ("numba", None),
        ("python-igraph", "igraph"), ("numexpr", None),
        ("networkx", None), ("scikit-learn", "sklearn")
    ]:
        results.append(check_python_package(*pkg))

    print_header("System Commands")
    check_system_command("llvm-config", "llvm-14-dev")
    check_system_command("pkg-config")

    print_header("LLVM Binding");        results.append(check_llvm_binding())
    print_header("Numba JIT Compilation");results.append(check_numba_jit())
    print_header("igraph C Library");     results.append(check_igraph_c_library())
    print_header("numexpr Evaluation");   results.append(check_numexpr_eval())

    print_header("VALIDATION SUMMARY")
    total = len(results); ok = sum(results)
    log(f"\nTotal checks : {total}")
    log(f"Passed       : {ok}")
    log(f"Failed       : {total - ok}")

    if total == ok:
        log("\nAll dependencies working correctly.")
        return 0
    else:
        log("\nSome dependencies failed. Suggested fixes:")
        log("  sudo apt-get install -y llvm-14 llvm-14-dev libigraph-dev libigraph3t64")
        log("  pip install -r requirements.txt")
        return 1

if __name__ == "__main__":
    sys.exit(main())
