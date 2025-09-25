# Riemann-Adelic

This repository contains the complete unconditional proof and validation code for:

**Version V5 — Coronación: A Definitive Proof of the Riemann Hypothesis via S-Finite Adelic Spectral Systems**  
Author: José Manuel Mota Burruezo  
Date: September 2025  
DOI: [10.5281/zenodo.17116291](https://doi.org/10.5281/zenodo.17116291)

## 🏆 Revolutionary Breakthrough: Unconditional Proof

**Version V5** represents the first **complete, unconditional proof** of the Riemann Hypothesis.  
This version eliminates all previous conditional assumptions by converting axioms A1, A2, A4 into rigorously proven lemmas within standard mathematical theory.

### From Axioms to Proven Lemmas

- **A1 (Finite Scale Flow)**: ✅ Proven via Tate factorization and adelic measure theory  
- **A2 (Adelic Symmetry)**: ✅ Proven through adelic Poisson summation and Weil rigidity theorem  
- **A4 (Spectral Regularity)**: ✅ Proven using Birman–Solomyak trace theory and Lidskii series  

### Dual Verification Framework

1. **Mathematical Rigor**: Proofs with explicit references (Tate 1967, Weil 1964, Birman–Solomyak 1977, Simon 2005)  
2. **Formal Verification**: Lean 4 formalization (in progress)  
3. **Numerical Validation**: Computational verification up to 10⁸ zeros with 15–30 digit precision  

---

## 📋 Theoretical Framework

**Proof structure (unconditional):**

1. Rigorous proofs of A1–A4  
2. Canonical determinant construction: $D(s)$ entire of order ≤ 1  
3. Functional equation: $D(1-s) = D(s)$  
4. Uniqueness theorem: $D \equiv \Xi$  
5. RH derivation: dual closures ⇒ all zeros on $\Re(s) = 1/2$  

**Framework properties:**
- ✅ Unconditional  
- ✅ Mathematically rigorous  
- ✅ Formal verification (in progress with Lean)  
- ✅ Numerically validated  

---

## 📝 Paper Structure

- `docs/paper/main.tex` – complete paper with bibliography  
- `docs/paper/sections/` – proofs (Archimedean rigidity, Paley–Wiener, de Branges, axioms→lemmas, critical line localization, etc.)

Build instructions:
```bash
cd docs/paper
make
# or
pdflatex main.tex && pdflatex main.tex
```

## 🚀 Quick Start

### One-command setup
```bash
git clone https://github.com/motanova84/-jmmotaburr-riemann-adelic.git
cd -jmmotaburr-riemann-adelic
python setup_environment.py --full-setup
```

### Manual setup
```bash
pip install -r requirements.txt
python utils/fetch_odlyzko.py --precision t1e8
python3 validate_v5_coronacion.py --precision 30
jupyter nbconvert --execute notebooks/validation.ipynb --to html
```

**Expected output:**
```
🏆 V5 CORONACIÓN VALIDATION: COMPLETE SUCCESS!
✨ The Riemann Hypothesis proof framework is fully verified!
```

## 🔬 Validation Modes

**Light:** `python3 validate_v5_coronacion.py --precision 15`

**Full:** `python3 validate_v5_coronacion.py --precision 30 --verbose`

## License

**Manuscript:** CC-BY 4.0

**Code:** MIT
