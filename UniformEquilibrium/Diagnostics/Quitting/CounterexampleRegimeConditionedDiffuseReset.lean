/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeConditionedDiffuseFixedOutsider
import UniformEquilibrium.Quitting.Boundary.Repair.FixedTailPositiveAbsorptionRoot

/-!
# Positive-absorption reset targets in the diffuse counterexample branch

A diffuse counterexample seam selects one fixed inactive outsider whose
conditioned payoff is uniformly below its singleton reward at arbitrarily late
dates.  Finite mixed-Nash existence at that exact conditioned target therefore
supplies an endpoint-Nash product root with positive one-stage absorption.

The root is an incoming fixed-target object.  The theorem does not identify
its Bellman predecessor with the conditioned source state, prove that either
endpoint lies above the punishment floor, or concatenate roots into a
chronological word.  Those are the state-matching and viability obligations
for a strategic reset.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {regime : QuittingCounterexampleRegime reward}

namespace QuittingCounterexampleSeamWitness

/-- Arbitrarily late conditioned targets in the diffuse branch admit a
positive-absorption exact endpoint-Nash root.  The selected outsider and the
singleton deficit are uniform across all requested starting dates. -/
theorem exists_cofinal_fixedOutsider_positiveAbsorptionReset_of_diffuse
    (seam : QuittingCounterexampleSeamWitness regime)
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption
      (quittingDynamicDebtTailRoots seam.tail) time)
    (hmesh : Tendsto (quittingTailConditionedAbsorptionWeight
      (quittingDynamicDebtTailRoots seam.tail)) atTop (nhds 0)) :
    ∃ who : ι, ∃ eta : ℝ, 0 < eta ∧ ∀ start, ∃ time root,
      start ≤ time ∧
      quittingDynamicDebtTailRoots seam.tail time who = PMF.pure false ∧
      quittingTailConditionedValue
          (quittingDynamicDebtTailRoots seam.tail)
          (fun date => (seam.tail date).1.1) seam.limit.value time who ≤
        reward (quittingSingletonTerminal who) who - eta ∧
      IsεQuittingRootEndpointNash reward
          (quittingTailConditionedValue
            (quittingDynamicDebtTailRoots seam.tail)
            (fun date => (seam.tail date).1.1) seam.limit.value time)
          0 (quittingRootOfSimplex root) ∧
      0 < quittingRootAbsorptionMass (quittingRootOfSimplex root) := by
  obtain ⟨who, eta, heta, hdates⟩ :=
    seam.exists_fixed_inactive_rescaledQuitDefect_of_diffuse hpositive hmesh
  refine ⟨who, eta, heta, ?_⟩
  intro start
  obtain ⟨time, htime, hinactive, _, hdeficit⟩ := hdates start
  let target : Payoff ι :=
    quittingTailConditionedValue
      (quittingDynamicDebtTailRoots seam.tail)
      (fun date => (seam.tail date).1.1) seam.limit.value time
  have hgap : target who < reward (quittingSingletonTerminal who) who := by
    dsimp only [target]
    linarith
  obtain ⟨root, hnash, habsorption⟩ :=
    exists_isZeroQuittingRootEndpointNash_simplex_with_positive_absorption_of_singleton_gap
      reward target who hgap
  exact ⟨time, root, htime, hinactive, hdeficit, by
    simpa only [target] using hnash, habsorption⟩

end QuittingCounterexampleSeamWitness

end GameTheory
