/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Correlation.CorrelatedEqProperties
import GameTheory.Concepts.Correlation.CorrelationSaturation
import GameTheory.Concepts.ZeroSum.ConstantSumCounterexamples
import GameTheory.Languages.NFG.Examples

/-!
# Correlation Concept Tests

Compilation tests for correlated-equilibrium bridges.
-/

namespace GameTheory.Concepts.Correlation.Tests

open GameTheory.KernelGame
open GameTheory.KernelGame.ThreePlayerZeroSumCoordination
open Math.Probability

noncomputable section

example : game.IsCorrelatedEq (PMF.pure highProfile) :=
  nash_pure_isCorrelatedEq highProfile_isNash

example : game.IsCoarseCorrelatedEq (PMF.pure highProfile) :=
  (nash_pure_isCorrelatedEq highProfile_isNash).toCoarseCorrelatedEq

namespace PrisonersDilemma

open NFG

noncomputable local instance : Finite prisonersDilemma.toKernelGame.Outcome := by
  change Finite (∀ _ : Bool, PDAction)
  infer_instance

/-- Defection is strictly dominant for either player in the compiled
Prisoner's Dilemma. -/
theorem defect_isStrictDominant (i : Bool) :
    prisonersDilemma.toKernelGame.IsStrictDominant i PDAction.defect := by
  intro σ a' hne
  cases i <;> cases a' <;>
    cases htrue : σ true <;> cases hfalse : σ false <;>
    simp_all [KernelGame.eu, NFGGame.toKernelGame, prisonersDilemma,
      Function.update, Math.Probability.expect_pure] <;> norm_num

private theorem all_defect_isStrictDominant :
    ∀ i, prisonersDilemma.toKernelGame.IsStrictDominant i (pd_defect_defect i) := by
  intro i
  simpa [pd_defect_defect] using defect_isStrictDominant i

/-- In Prisoner's Dilemma the all-defect law is the unique CCE. -/
example (μ : PMF (KernelGame.Profile prisonersDilemma.toKernelGame)) :
    prisonersDilemma.toKernelGame.IsCoarseCorrelatedEq μ ↔
      μ = PMF.pure pd_defect_defect :=
  prisonersDilemma.toKernelGame.strictDominant_isCoarseCorrelatedEq_iff
    all_defect_isStrictDominant

/-- Prisoner's Dilemma concretely exercises coarse-correlation saturation. -/
example : prisonersDilemma.toKernelGame.IsCoarseCorrelationSaturated :=
  prisonersDilemma.toKernelGame.strictDominant_isCoarseCorrelationSaturated
    all_defect_isStrictDominant

/-- The coarse result implies ordinary correlation saturation in the same game. -/
example : prisonersDilemma.toKernelGame.IsCorrelationSaturated :=
  prisonersDilemma.toKernelGame.strictDominant_isCorrelationSaturated
    all_defect_isStrictDominant

end PrisonersDilemma

end

end GameTheory.Concepts.Correlation.Tests
