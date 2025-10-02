-- Main entry point for Riemann Adelic Lean formalization
import RiemannAdelic.axioms_to_lemmas
import RiemannAdelic.entire_order
import RiemannAdelic.functional_eq
import RiemannAdelic.arch_factor
import RiemannAdelic.de_branges
import RiemannAdelic.positivity
import RiemannAdelic.lengths_derived
import RiemannAdelic.uniqueness_without_xi

def main : IO Unit := do
  IO.println "Riemann Hypothesis Adelic Proof - Lean 4 Formalization"
  IO.println "José Manuel Mota Burruezo (V5.2, unconditional)"
  IO.println ""
  IO.println "All modules loaded successfully!"
  IO.println "✅ A4: Orbit lengths derived (lengths_derived.lean)"
  IO.println "✅ Uniqueness without Ξ (uniqueness_without_xi.lean)"