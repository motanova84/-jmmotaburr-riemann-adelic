import Lake
open Lake DSL

package riemannAdelic {
  -- configura opciones de compilación
  moreLeanArgs := #["-DautoImplicit=false", "-Dlinter=false"]
}

@[default_target]
lean_lib RiemannAdelic where
  globs := #[
    "axioms_to_lemmas",
    "schwartz_adelic",
    "D_explicit",
    "functional_eq",
    "de_branges",
    "entire_order",
    "positivity",
    "RH_final"
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "07a2d4e5c3c9e55bb6e37bbf5132fd47d75b9ce2"

require aesop from git
  "https://github.com/leanprover-community/aesop" @ "main"

require proofwidgets from git
  "https://github.com/leanprover-community/proofwidgets4" @ "main"