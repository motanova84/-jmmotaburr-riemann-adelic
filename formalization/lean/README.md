# Lean formalisation blueprint

This folder mirrors the analytic decomposition of the adelic programme.  Each
module should eventually depend on mathlib (Lean 4 + Lake).

## Getting started
1. Install Lean 4 and Lake following <https://leanprover-community.github.io/get_started.html>.
2. Run `lake init rh-formalization` in this directory to create a project skeleton.
3. Add `mathlib` as a dependency in `lakefile.lean` via `require mathlib from git`.
4. Replace the placeholder files below with the formal statements and proofs.

## Modules
- `entire_order.lean`: statements about entire functions of order $\leqslant1$, Hadamard factorisation, and Phragmén--Lindelöf bounds.
- `functional_eq.lean`: adelic Fourier transform, Poisson summation, and functional symmetry.
- `arch_factor.lean`: Weil index computation and stationary-phase rigidity of $\pi^{-s/2}\Gamma(s/2)$.
- `de_branges.lean`: Hermite--Biehler properties, Hamiltonian positivity, and self-adjointness.
- `positivity.lean`: Weil--Guinand quadratic form and positivity criterion leading to the critical line.

Each file currently contains skeletal declarations to be refined during the
formalisation effort.
