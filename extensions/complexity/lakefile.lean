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
        (some "c7cd6bed7498b9a16edb22262e9522ceff90648c") none
}

require complexitylib from git "https://github.com/cslib-community/complexitylib"
  @ "054834a4a4e6ac3ec50ed770bacea7fc42eccc7d"

require cslib from git "https://github.com/leanprover/cslib.git"
  @ "254e30e6d4299c51323aaeaf5f51a4763b375d4a"

-- Explicitly select the same Mathlib version as the base package, overriding
-- the inherited snapshot in the selected backend. Only the imported closure
-- is validated against this shared stable release.
require "leanprover-community" / "mathlib" @ git "v4.35.0"

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
