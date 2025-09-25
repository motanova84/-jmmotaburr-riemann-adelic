import math
from mpmath import mp
from utils.adelic_determinant import AdelicCanonicalDeterminant

def test_symmetry_exact():
    det = AdelicCanonicalDeterminant(max_zeros=30, dps=80)
    s = mp.mpf("0.5") + (2.3456789j)
    assert abs(det.D(s) - det.D(1 - s)) < mp.mpf("1e-60")

def test_zero_is_zero_truncated():
    det = AdelicCanonicalDeterminant(max_zeros=10, dps=80)
    t = det.ts[0]
    val = det.D(mp.mpf("0.5") + 1j * t)
    assert abs(val) == 0  # exact for included zeros

def test_normalization():
    """Test that D(1/2) = 1 exactly"""
    det = AdelicCanonicalDeterminant(max_zeros=20, dps=80)
    val = det.D(mp.mpf("0.5"))
    assert val == mp.mpf(1)

def test_functional_form():
    """Test the convenience functional form"""
    from utils.adelic_determinant import D
    s = mp.mpf("0.5") + 2j
    val1 = D(s, max_zeros=20, dps=50)
    val2 = D(1-s, max_zeros=20, dps=50) 
    assert abs(val1 - val2) < mp.mpf("1e-40")