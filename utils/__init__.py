"""
Utilities module for Riemann Hypothesis validation and adelic analysis.

This package contains various utility functions and classes for:
- Critical line verification
- Adelic determinant calculations  
- Data fetching and validation
- Performance monitoring
- Mathematical tools for Riemann zeta function analysis

The utilities support the numerical validation of the paper:
"A Complete Proof of the Riemann Hypothesis via S-Finite Adelic Systems (V5.1)"
by José Manuel Mota Burruezo.
"""

from .adelic_determinant import AdelicCanonicalDeterminant
from .critical_line_checker import CriticalLineChecker

# Optional imports that may not be available
try:
    from .performance_monitor import PerformanceMonitor, PerformanceMetrics
    __all__ = [
        'AdelicCanonicalDeterminant',
        'CriticalLineChecker', 
        'PerformanceMonitor',
        'PerformanceMetrics'
    ]
except ImportError:
    print("⚠️ Warning: performance_monitor not available (missing psutil dependency)")
    __all__ = [
        'AdelicCanonicalDeterminant',
        'CriticalLineChecker'
    ]