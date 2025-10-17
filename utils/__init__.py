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

# Use lazy imports to avoid import errors when dependencies are not installed
# Import only what's needed when it's needed
def __getattr__(name):
    if name == 'AdelicCanonicalDeterminant':
        from .adelic_determinant import AdelicCanonicalDeterminant
        return AdelicCanonicalDeterminant
    elif name == 'CriticalLineChecker':
        from .critical_line_checker import CriticalLineChecker
        return CriticalLineChecker
    elif name == 'PerformanceMonitor':
        from .performance_monitor import PerformanceMonitor
        return PerformanceMonitor
    elif name == 'PerformanceMetrics':
        from .performance_monitor import PerformanceMetrics
        return PerformanceMetrics
    raise AttributeError(f"module {__name__!r} has no attribute {name!r}")

__all__ = [
    'AdelicCanonicalDeterminant',
    'CriticalLineChecker', 
    'PerformanceMonitor',
    'PerformanceMetrics',
    'path_utils'
]