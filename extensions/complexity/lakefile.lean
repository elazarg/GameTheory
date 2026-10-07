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
        (some "71a6547d9491953f4a4f5a28e18f7eac81e2f8c8") none
}

require complexitylib from git "https://github.com/SamuelSchlesinger/complexitylib"
  @ "257ad90ec5f547894cc20f27bd828839b1bf7bbf"

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
