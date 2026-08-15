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

require "leanprover-community" / "mathlib" @ git "v4.32.2"

/-- Brouwer's and Kakutani's fixed-point theorems, which Mathlib does not carry.
Only the analytic root may import from it; the semantic core and the sequential
layer are kept free of it, and that separation is checked rather than trusted. -/
require «fixed-point-theorems» from git
  "https://github.com/elazarg/fixed-point-theorems-lean4" @
    "9571dd7e0ff0af9c9e9becb2738a309cf48387c1"

/-- The public library target. `andSubmodules` makes `lake build` a real phase
gate: examples, architecture tests, and experiments must compile too. -/
@[default_target]
lean_lib GameTheory where
  globs := #[.andSubmodules `GameTheory]
  leanOptions := gameTheoryLeanOptions

/-- Mathematical infrastructure used throughout the library. -/
@[default_target]
lean_lib GameTheory.Math where
  globs := #[.andSubmodules `GameTheory.Math]
  leanOptions := gameTheoryLeanOptions
