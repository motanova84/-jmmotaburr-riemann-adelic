import Lake
open Lake DSL

package «riemann-adelic-lean» where
  -- add package configuration options here

lean_lib «RiemannAdelic» where
  -- add library configuration options here

@[default_target]
lean_exe «riemann-adelic-lean» where
  root := `Main

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"