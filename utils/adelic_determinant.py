# utils/adelic_determinant.py
# Zeta-free canonical determinant built from the zero measure (pairs around 1/2)
# D(s) = ∏_t (1 + ((s - 1/2)^2) / t^2), truncated to the zeros provided.

from mpmath import mp

def load_zero_ordinates(path: str, max_zeros: int | None = None) -> list[mp.mpf]:
    ts: list[mp.mpf] = []
    with open(path, "r", encoding="utf-8", errors="ignore") as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            try:
                # admit e.g. "14.134725141" or "1 14.134725141 ..." (idx + value)
                parts = line.split()
                val = parts[0] if len(parts) == 1 else parts[1]
                ts.append(mp.mpf(val))
            except Exception:
                continue
            if max_zeros is not None and len(ts) >= max_zeros:
                break
    if not ts:
        raise ValueError(f"No zeros loaded from {path}")
    return ts

class AdelicCanonicalDeterminant:
    """
    Canonical zeta-free determinant from zero measure (truncated).
    Symmetry: D(1-s) = D(s) (exact).
    Zeros: at s = 1/2 ± i t for every loaded ordinate t.
    Normalization: D(1/2) = 1 (exact).
    """
    def __init__(self, zeros_path: str = "zeros/zeros_t1e3.txt",
                 max_zeros: int | None = None, dps: int = 50) -> None:
        mp.dps = dps
        self.ts = load_zero_ordinates(zeros_path, max_zeros=max_zeros)

    def D(self, s: complex) -> mp.mpf | complex:
        z = s - mp.mpf("0.5")
        prod = mp.mpf(1)
        for t in self.ts:
            prod *= (1 + (z / t) ** 2)
        # D(1/2) = 1 since z=0 -> every factor equals 1
        return prod

# Convenience functional form
def D(s: complex, zeros_path: str = "zeros/zeros_t1e3.txt",
      max_zeros: int | None = None, dps: int = 50):
    return AdelicCanonicalDeterminant(zeros_path=zeros_path,
                                      max_zeros=max_zeros, dps=dps).D(s)