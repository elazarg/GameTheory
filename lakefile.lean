import Lake

open Lake DSL

abbrev gameTheoryLeanOptions : Array LeanOption := #[
  ⟨`pp.unicode.fun, true⟩,
  ⟨`relaxedAutoImplicit, false⟩,
  ⟨`maxSynthPendingDepth, .ofNat 3⟩
]

package GameTheory where
  version := v!"0.1.0"
  keywords := #["math", "game-theory"]
  fixedToolchain := true

require "leanprover-community" / "mathlib" @ git "v4.32.0"

/-- The public library target. `andSubmodules` makes `lake build` a real phase
gate: examples, architecture tests, and experiments must compile too. -/
@[default_target]
lean_lib GameTheory where
  globs := #[.andSubmodules `GameTheory]
  leanOptions := gameTheoryLeanOptions
