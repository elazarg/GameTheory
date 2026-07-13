import Lake

open Lake DSL

abbrev gameTheoryLeanOptions : Array LeanOption := #[
  ⟨`pp.unicode.fun, true⟩,
  ⟨`relaxedAutoImplicit, false⟩,
  ⟨`weak.linter.flexible, true⟩,
  ⟨`weak.linter.hashCommand, true⟩,
  ⟨`weak.linter.oldObtain, true⟩,
  ⟨`weak.linter.privateModule, true⟩,
  ⟨`weak.linter.style.cases, true⟩,
  ⟨`weak.linter.style.induction, true⟩,
  ⟨`weak.linter.style.refine, true⟩,
  ⟨`weak.linter.style.cdot, true⟩,
  ⟨`weak.linter.style.docString, true⟩,
  ⟨`weak.linter.style.dollarSyntax, true⟩,
  ⟨`weak.linter.style.emptyLine, true⟩,
  ⟨`weak.linter.style.lambdaSyntax, true⟩,
  ⟨`weak.linter.style.longLine, true⟩,
  ⟨`weak.linter.style.longFile, true⟩,
  ⟨`weak.linter.style.multiGoal, true⟩,
  ⟨`weak.linter.style.nativeDecide, true⟩,
  ⟨`weak.linter.style.openClassical, true⟩,
  ⟨`weak.linter.style.maxHeartbeats, true⟩,
  ⟨`weak.linter.style.missingEnd, true⟩,
  ⟨`weak.linter.style.setOption, true⟩,
  ⟨`weak.linter.style.show, true⟩,
  ⟨`weak.linter.style.whitespace, true⟩,
  ⟨`weak.linter.unusedDecidableInType, true⟩,
  ⟨`weak.linter.unusedFintypeInType, true⟩,
  ⟨`maxSynthPendingDepth, .ofNat 3⟩
]

package GameTheory where
  version := v!"0.1.0"
  keywords := #["math", "game-theory"]
  fixedToolchain := true

require "leanprover-community" / "mathlib" @ git "v4.32.0"
require FixedPointTheorems from "fixed-point-theorems-lean4"

@[default_target]
lean_lib GameTheory where
  leanOptions := gameTheoryLeanOptions

@[default_target]
lean_lib Math where
  srcDir := "."
  leanOptions := gameTheoryLeanOptions

@[default_target]
lean_lib GameTheoryExamples where
  srcDir := "."
  leanOptions := gameTheoryLeanOptions

@[default_target]
lean_lib GameTheoryTest where
  srcDir := "."
  leanOptions := gameTheoryLeanOptions

@[default_target]
lean_lib Semantics where
  srcDir := "."
  leanOptions := gameTheoryLeanOptions
