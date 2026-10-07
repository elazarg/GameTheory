import Lake

open Lake DSL

package GameTheoryComplexity where
  version := v!"0.1.0"
  description := "Opt-in computational complexity certificates for GameTheory"
  fixedToolchain := true
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
    | none => .git "https://github.com/elazarg/GameTheory"
        (some "3132599983a6baf0d67fa2e41e0da1c8e7521405") none
}

require complexitylib from git "https://github.com/elazarg/complexitylib"
  @ "c5f2acf1a35d5b00db04cd1bd337a8ce57d66a40"

require cslib from git "https://github.com/leanprover/cslib.git"
  @ "94ea80f41a5678fce997a004f0d8d12dbe47cc4b"

-- Explicitly select the same Mathlib version as the base package, overriding
-- the older inherited snapshot in ComplexityLib.
require "leanprover-community" / "mathlib" @ git "v4.34.1"

@[default_target]
lean_lib GameTheoryComplexity where
  globs := #[.andSubmodules `GameTheoryComplexity]
  leanOptions := #[⟨`warningAsError, true⟩, ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.checkUnivs, false⟩]

lean_lib GameTheoryComplexity.LintAll where
  srcDir := "lint"
  leanOptions := #[⟨`warningAsError, true⟩, ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.checkUnivs, false⟩]

lean_lib GameTheoryComplexity.AxiomAudit where
  srcDir := "lint"
  leanOptions := #[⟨`warningAsError, true⟩]
