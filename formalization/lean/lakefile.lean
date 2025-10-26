import Lake
open Lake DSL

package riemannAdelic

@[default_target]
lean_lib RiemannAdelic

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"