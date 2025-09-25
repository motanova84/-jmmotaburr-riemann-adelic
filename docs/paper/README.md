# Core Theorems towards a Complete Proof of the Riemann Hypothesis

This folder contains the **foundational theorems** that bridge the gap between a
conditional adelic framework and a **full mathematical proof** of the Riemann
Hypothesis (RH).

## Structure

- **sections/rigidez_arquimediana.tex**  
  *Theorem of Archimedean Rigidity*: proves that the only admissible archimedean
  local factor compatible with global reciprocity and functional symmetry is  
  \(\pi^{-s/2}\Gamma(s/2)\).

- **sections/unicidad_paley_wiener.tex**  
  *Paley--Wiener Uniqueness with Multiplicities*: ensures that if a function shares
  order \(\leq 1\), symmetry, spectral measure of zeros (with multiplicities),
  and normalization at \(s=1/2\), then it coincides identically with \(\Xi(s)\).

- **sections/de_branges.tex**  
  *de Branges Scheme for \(D(s)\)*: embeds \(D(s)\) into a de Branges space
  \(\mathcal{H}(E)\). Positivity of the Hamiltonian ensures that the spectrum is
  real, forcing all zeros of \(D(s)\) onto the critical line.

- **main.tex**  
  Document driver that assembles the full paper.

- **references.bib**  
  Bibliography entries for the paper.

- **Makefile**  
  Simple build system to generate `main.pdf` with BibTeX integration.

## Compilation

```bash
cd docs/paper
make
```

This produces `main.pdf` with all core theorems and references.

## Purpose

These documents represent the mathematical backbone required to elevate the
framework from conditional validity to a Millennium Problem-level proof:

- Eliminate the dependency on ad hoc axioms (A1--A4).
- Derive the Archimedean factor rigorously.
- Ensure uniqueness of \(D(s) \equiv \Xi(s)\).
- Force analytically that all zeros lie on the critical line.

Together, they form the checklist of missing steps for a universally accepted
resolution of RH.

**Author:** José Manuel Mota Burruezo  
**Affiliation:** Instituto Conciencia Cuántica -- 2025
