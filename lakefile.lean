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
  version := v!"4.35.0"
  description :=
    "Formalized game theory: static forms, sequential execution protocols, \
    information models, mechanisms, and the standard equilibrium concepts."
  keywords := #["math", "game-theory"]
  homepage := "https://github.com/elazarg/GameTheory"
  license := "Apache-2.0"
  licenseFiles := #["LICENSE", "NOTICE"]
  fixedToolchain := true
  -- This library retains legacy module visibility when importing Mathlib modules.
  allowNonModules := true
  lintDriver := "batteries/runLinter"
  lintDriverArgs := #["GameTheory.LintAll"]

/-- Brouwer's and Kakutani's fixed-point theorems, which Mathlib does not carry.
Only the analytic root may import from it; the semantic core and the sequential
layer are kept free of it, and that separation is checked rather than trusted. -/
require «fixed-point-theorems» from git
  "https://github.com/elazarg/fixed-point-theorems-lean4" @
    "f06449c5fb1ca49f14ea2b5331ddf71bd2dcd232"

-- Keep Mathlib last so its transitive pins override older dependency manifests.
require "leanprover-community" / "mathlib" @ git "v4.35.0"

/-- Build the public umbrella and its imports. Other modules remain available
by explicit import; the lint and axiom targets build the complete library and
its validation evidence. -/
@[default_target]
lean_lib GameTheory where
  globs := #[.one `GameTheory]
  leanOptions := gameTheoryLeanOptions

/-- The lint scope. Not a default target: it exists so `lake lint` can see the
whole public library through a single module, and is deliberately outside the
`GameTheory` tree because it imports the analytic root. -/
lean_lib GameTheory.LintAll where
  srcDir := "lint"
  leanOptions := gameTheoryLeanOptions

/-- Transitive standard-axiom checks over every authored module. -/
lean_lib GameTheory.AxiomAudit where
  srcDir := "lint"
  leanOptions := gameTheoryLeanOptions

/-- Mathematical infrastructure used throughout the library. -/
@[default_target]
lean_lib GameTheory.Math where
  globs := #[.one `GameTheory.Math]
  leanOptions := gameTheoryLeanOptions
