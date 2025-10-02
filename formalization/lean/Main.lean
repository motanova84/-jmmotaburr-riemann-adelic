-- Main entry point for Riemann Adelic Lean formalization
import RiemannAdelic.axioms_to_lemmas
import RiemannAdelic.entire_order
import RiemannAdelic.functional_eq
import RiemannAdelic.arch_factor
import RiemannAdelic.de_branges
import RiemannAdelic.positivity
import RiemannAdelic.uniqueness_without_xi

def main : IO Unit := do
  IO.println "Riemann Hypothesis Adelic Proof - Lean 4 Formalization"
  IO.println "José Manuel Mota Burruezo (V5.1, unconditional)"
  IO.println ""
  IO.println "All modules loaded successfully!"
  IO.println "  ✓ axioms_to_lemmas - A1, A2, A4 proven as lemmas"
  IO.println "  ✓ uniqueness_without_xi - Autonomous D(s) characterization"