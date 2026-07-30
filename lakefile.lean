import Lake

open Lake DSL

abbrev gameTheoryLeanOptions : Array LeanOption := #[
  ⟨`pp.unicode.fun, true⟩,
  ⟨`warningAsError, true⟩,
  ⟨`relaxedAutoImplicit, false⟩,
  ⟨`maxSynthPendingDepth, .ofNat 3⟩
]

package GameTheory where
  version := v!"0.1.0"
  keywords := #["math", "game-theory"]
  fixedToolchain := true

require "leanprover-community" / "mathlib" @ git "v4.32.0"

/-- Brouwer's and Kakutani's fixed-point theorems, which Mathlib does not carry.
Only the analytic root may import from it; the semantic core and the sequential
layer are kept free of it, and that separation is checked rather than trusted. -/
require «fixed-point-theorems» from git
  "https://github.com/harfe/fixed-point-theorems-lean4" @
    "770940ddf9878cf61952ed53d910b92bca841838"

/-- The public library target. `andSubmodules` makes `lake build` a real phase
gate: examples, architecture tests, and experiments must compile too. -/
@[default_target]
lean_lib GameTheory where
  globs := #[.andSubmodules `GameTheory]
  leanOptions := gameTheoryLeanOptions
