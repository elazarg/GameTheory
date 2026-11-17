import Lake

open Lake DSL

package GameTheoryComplexity where
  version := v!"0.2.0"
  description := "Opt-in computational complexity certificates for GameTheory"
  fixedToolchain := true
  requiresModuleSystem := true
  license := "Apache-2.0"
  lintDriver := "batteries/runLinter"
  lintDriverArgs := #["GameTheoryComplexity.LintAll"]

/-- Consumers use the pinned base release; repository builds select the local
checkout with `-KgameTheoryPath=../..`. The base package never requires this one. -/
@[package_dep] def GameTheory : Dependency := {
  name := `GameTheory
  scope := ""
  version := .none
  opts := {}
  src? := some <| match get_config? gameTheoryPath with
    | some path => .path path
    | none => .git "https://github.com/elazarg/GameTheory.git"
        (some "c33309b03feae395a9677b2d7156d876ca4fc61d") none
}

/- TEMPORARY: a GameTheory-maintained subset of cslib-frontier holding only the
modules this package imports, adapted to released Lean, Mathlib and CSLib
v4.36.0. It does not track cslib-frontier. Replace it with CSLib itself as the
definitions used here are upstreamed there; do not add unrelated modules. -/
require «cslib-frontier» from git "https://github.com/elazarg/complexitylib-community"
  @ "5c24f2573df209120770cfdd423a2ec9e11bee4c"

require cslib from git "https://github.com/leanprover/cslib.git"
  @ "v4.36.0"

-- Explicitly select the same Mathlib release as the base package. Keep this
-- requirement last so it overrides the pins inherited from dependencies.
require "leanprover-community" / "mathlib" @ git "v4.36.0"

@[default_target]
lean_lib GameTheoryComplexity where
  globs := #[.andSubmodules `GameTheoryComplexity]
  leanOptions := #[⟨`warningAsError, true⟩, ⟨`relaxedAutoImplicit, false⟩,
    ⟨`backward.privateInPublic, true⟩, ⟨`backward.privateInPublic.warn, false⟩,
    ⟨`linter.checkUnivs, false⟩]

lean_lib GameTheoryComplexity.LintAll where
  srcDir := "lint"
  leanOptions := #[⟨`warningAsError, true⟩, ⟨`relaxedAutoImplicit, false⟩,
    ⟨`backward.privateInPublic, true⟩, ⟨`backward.privateInPublic.warn, false⟩,
    ⟨`linter.checkUnivs, false⟩]

lean_lib GameTheoryComplexity.AxiomAudit where
  srcDir := "lint"
  leanOptions := #[⟨`warningAsError, true⟩]
