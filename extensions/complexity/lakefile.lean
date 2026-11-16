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

/- TEMPORARY fork: upstream `054834a4` plus one line adapting
`Nat.pow_pred_clog_lt_self` to Mathlib v4.36.0, which upstream (still on
v4.36.0-rc2) has not adopted. Return to `cslib-community/complexitylib` as soon
as upstream builds against released Mathlib v4.36.0; do not extend the fork. -/
require complexitylib from git "https://github.com/elazarg/complexitylib-community"
  @ "481355bbf30f161a600c5761053f42da888e7b0f"

require cslib from git "https://github.com/leanprover/cslib.git"
  @ "254e30e6d4299c51323aaeaf5f51a4763b375d4a"

-- Explicitly select the same Mathlib version as the base package, overriding
-- the inherited snapshot in the selected backend. Only the imported closure
-- is validated against this shared stable release.
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
