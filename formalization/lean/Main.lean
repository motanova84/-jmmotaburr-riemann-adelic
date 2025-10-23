-- Main entry point for Riemann Adelic Lean formalization
-- Updated to include all formalization modules

-- Core axioms and lemmas
import RiemannAdelic.axioms_to_lemmas

-- Constructive D(s) definition (V5.2+)
import RiemannAdelic.schwartz_adelic
import RiemannAdelic.D_explicit

-- Entire function theory
import RiemannAdelic.entire_order

-- Functional equation and symmetry
import RiemannAdelic.functional_eq
import RiemannAdelic.poisson_radon_symmetry

-- Archimedean factors
import RiemannAdelic.arch_factor

-- de Branges space theory
import RiemannAdelic.de_branges

-- Positivity and trace class operators
import RiemannAdelic.positivity
import RiemannAdelic.doi_positivity

-- Zero localization and uniqueness
import RiemannAdelic.zero_localization
import RiemannAdelic.uniqueness_without_xi

-- Paley-Wiener and derived lengths
import RiemannAdelic.pw_two_lines
import RiemannAdelic.lengths_derived

-- Spectral RH operator H_ε
import RiemannAdelic.spectral_RH_operator

def main : IO Unit := do
  IO.println "╔═══════════════════════════════════════════════════════════╗"
  IO.println "║   Riemann Hypothesis Adelic Proof - Lean 4 Formalization ║"
  IO.println "║   José Manuel Mota Burruezo (V5.2+, unconditional)       ║"
  IO.println "╚═══════════════════════════════════════════════════════════╝"
  IO.println ""
  IO.println "✓ All formalization modules loaded successfully!"
  IO.println ""
  IO.println "Modules included:"
  IO.println "  • Core axioms and lemmas"
  IO.println "  • Schwartz functions on adeles (constructive)"
  IO.println "  • Explicit D(s) construction"
  IO.println "  • Entire function and Hadamard theory"
  IO.println "  • Functional equation and Poisson symmetry"
  IO.println "  • de Branges space framework"
  IO.println "  • Weil-Guinand positivity theory"
  IO.println "  • Zero localization and uniqueness"
  IO.println "  • Paley-Wiener theory"
  IO.println "  • Spectral RH operator H_ε"
  IO.println ""
  IO.println "Status: Constructive formalization in progress"
  IO.println "DOI: 10.5281/zenodo.17116291"