import Lake
open Lake DSL

package riemannAdelic

@[default_target]
lean_lib RiemannAdelic
package «riemann-adelic-lean» where
  -- Version and configuration
  version := "5.1"
  -- Require Lean 4.5.0 or higher
  preferReleaseBuild := true

lean_lib «RiemannAdelic» where
  -- Library configuration for the Riemann Adelic proof modules
  globs := #[.submodules `RiemannAdelic]
  roots := #[`RiemannAdelic]

@[default_target]
lean_exe «riemann-adelic-lean» where
  root := `Main
  supportInterpreter := true

-- Require mathlib4 for complete mathematical library support
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master"