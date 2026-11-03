import Lake
open Lake DSL
package «fs_cofinality» where
  leanOptions := #[⟨`autoImplicit, false⟩]
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @
  "c5ea00351c28e24afc9f0f84379aa41082b1188f"
lean_lib Definitions
@[default_target] lean_lib FSCofinalityProof
lean_lib Solutions
