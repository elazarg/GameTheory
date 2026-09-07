import Lake

open Lake DSL

abbrev gameTheoryLeanOptions : Array LeanOption := #[
  ⟨`pp.unicode.fun, true⟩,
  ⟨`warningAsError, true⟩,
  ⟨`relaxedAutoImplicit, false⟩,
  /- `checkUnivs` cannot express declaration-local exceptions. GameTheory keeps
  several semantic carriers in independent universes, and each affected
  declaration documents that choice locally, so configure the exception once
  for the library. -/
  ⟨`linter.checkUnivs, false⟩,
  ⟨`maxSynthPendingDepth, .ofNat 3⟩
]

package GameTheory where
  version := v!"4.33.1"
  description :=
    "Formalized game theory: static forms, sequential execution protocols, \
    information models, mechanisms, and the standard equilibrium concepts."
  keywords := #["math", "game-theory"]
  homepage := "https://github.com/elazarg/GameTheory"
  license := "Apache-2.0"
  licenseFiles := #["LICENSE", "NOTICE"]
  fixedToolchain := true
  lintDriver := "batteries/runLinter"
  lintDriverArgs := #["GameTheory.LintAll"]

require "leanprover-community" / "mathlib" @ git "v4.33.1"

/-- Brouwer's and Kakutani's fixed-point theorems, which Mathlib does not carry.
Only the analytic root may import from it; the semantic core and the sequential
layer are kept free of it, and that separation is checked rather than trusted. -/
require «fixed-point-theorems» from git
  "https://github.com/elazarg/fixed-point-theorems-lean4" @
    "8506daa06b98520a97e36a90abe7c314d53af626"

/-- The public library target. `andSubmodules` makes `lake build` a real phase
gate: examples, architecture tests, and experiments must compile too. -/
@[default_target]
lean_lib GameTheory where
  globs := #[.andSubmodules `GameTheory]
  leanOptions := gameTheoryLeanOptions

/-- The lint scope. Not a default target: it exists so `lake lint` can see the
whole public library through a single module, and is deliberately outside the
`GameTheory` tree because it imports the analytic root. -/
lean_lib GameTheory.LintAll where
  srcDir := "lint"
  leanOptions := gameTheoryLeanOptions

/-- Mathematical infrastructure used throughout the library. -/
@[default_target]
lean_lib GameTheory.Math where
  globs := #[.andSubmodules `GameTheory.Math]
  leanOptions := gameTheoryLeanOptions
