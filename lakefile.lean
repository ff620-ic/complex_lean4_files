import Lake
open Lake DSL

package Complex where
  moreLeanArgs := #["-Dtactic.hygienic=false"]
  moreServerArgs := #["-Dtactic.hygienic=false"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib Complex
