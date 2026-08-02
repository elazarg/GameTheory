/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.FTVCyclicFiniteHorizon
import GameTheory.Concepts.Stochastic.FTVCyclicMinimality
import GameTheory.Concepts.Stochastic.SplitDomainSemanticCredibilityCharacterization

/-!
# Semantic and finite-packet bridges for the concrete FTV controller

This module connects two previously independent facts about the prescribed
three-cycle:

* the ten-node response architecture is semantically credible from every one
  of its configurations, on the total split domain;
* its three live mixing rows, promises, and cyclic successor are exactly the
  data of `FTVCyclicMinimality.standardPacket`.

The first statement specializes the supplied-architecture semantic
characterization.  The second exposes the concrete `(Q1)--(Q5)` obligations
already carried by `ExactCyclicPacket`.  No converse from arbitrary public
response semantics to an arbitrary-`K` cyclic packet is claimed: such a
statement first needs an explicit arbitrary-`K` controller constructor and a
declared reachability/reduction convention.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace FTVCyclicCredibility

open Math.Probability StochasticGame

/-- The total split domain of the concrete ten-node architecture.  Every
configuration is an entry, a delivery node, and a unilateral node for every
owner. -/
def totalSplitDomain : architecture.SplitResponseDomain where
  entry := fun _ => True
  delivery := fun _ => True
  unilateral := fun _ _ => True
  start_entry := trivial
  entry_delivery := fun _ _ => trivial
  entry_unilateral := fun _ _ _ => trivial
  unilateral_delivery := fun _ _ _ => trivial
  delivery_covered := fun _ _ => ⟨0, trivial⟩
  unilateral_closed := fun _ _ _ _ _ _ => trivial
  delivery_closed := fun _ _ _ _ => trivial

@[simp] theorem totalSplitDomain_entry (z : Config) :
    totalSplitDomain.entry z := trivial

@[simp] theorem totalSplitDomain_delivery (z : Config) :
    totalSplitDomain.delivery z := trivial

@[simp] theorem totalSplitDomain_unilateral (who : Player) (z : Config) :
    totalSplitDomain.unilateral who z := trivial

/-- The concrete criterion produces an exact gain--bias packet on the total
domain.  The prescribed component is the explicit sharp delivery bias;
the unilateral component is synthesized by the finite controlled-Farkas
theorem from `(Ti)` and `(N)`. -/
theorem nonempty_totalSplitDomain_gainBiasPacket :
    Nonempty (totalSplitDomain.GainBiasPacket target) := by
  classical
  choose unilateralBias hunilateralBias using fun who =>
    architecture.exists_deviationPotential
      isUnilateralTargetSuperharmonic isNeutralOccupationNonpositive who
  exact ⟨{
    prescribedBias := fun who z => deliveryBias z who
    unilateralBias := unilateralBias
    prescribedTargetHarmonic := by
      intro who z hz
      exact isPrescribedTargetHarmonic who z
    unilateralTargetSuperharmonic := by
      intro who z hz act
      exact isUnilateralTargetSuperharmonic who z act
    prescribedBias_eq := by
      intro who z hz
      exact prescribed_deliveryBias_equation z who
    unilateralBias_le := by
      intro who z hz act
      exact hunilateralBias who z act
  }⟩

/-- Specialized fixed-architecture characterization: all-start semantic
credibility on the total domain is equivalent to a finite gain--bias packet
on that same domain. -/
theorem totalSplitDomain_isSemanticallyCredible_iff :
    totalSplitDomain.IsSemanticallyCredible target ↔
      Nonempty (totalSplitDomain.GainBiasPacket target) :=
  totalSplitDomain.isSemanticallyCredible_iff_nonempty_gainBiasPacket target

/-- The concrete FTV controller is semantically credible from every live
phase and absorbing child, with one common finite `O(1/T)` remainder for
prescribed delivery and every behavioral unilateral deviation. -/
theorem totalSplitDomain_isSemanticallyCredible :
    totalSplitDomain.IsSemanticallyCredible target :=
  totalSplitDomain_isSemanticallyCredible_iff.mpr
    nonempty_totalSplitDomain_gainBiasPacket

/-! ## Identification with the exact `(Q1)--(Q5)` packet -/

/-- Quit probability read directly from the live mixed action of the
response architecture. -/
def architectureQuitProb (c who : Player) : ℝ :=
  (play (Sum.inl c) who true).toReal

/-- The architecture's live mixed rows are exactly the normalized quitting
matrix used by `FTVCyclicMinimality.standardPacket`. -/
theorem architectureQuitProb_eq_standardQuitProb :
    architectureQuitProb =
      GameTheory.FTVCyclicMinimality.ExactCyclicPacket.standardQuitProb := by
  funext c who
  fin_cases c <;> fin_cases who <;>
    simp [architectureQuitProb, play,
      GameTheory.FTVCyclicMinimality.ExactCyclicPacket.standardQuitProb,
      PMF.uniformOfFintype_apply]

/-- The architecture's three live promises are exactly the normalized
promise word used by `FTVCyclicMinimality.standardPacket`. -/
theorem phaseTarget_eq_standardPromise :
    phaseTarget =
      GameTheory.FTVCyclicMinimality.ExactCyclicPacket.standardPromise := by
  funext c who
  fin_cases c <;> fin_cases who <;> rfl

/-- The architecture and packet use the same cyclic successor. -/
theorem nextPhase_eq_minimality_nextPhase (c : Player) :
    nextPhase c = GameTheory.FTVCyclicMinimality.nextPhase 3 c := by
  rw [GameTheory.FTVCyclicMinimality.ExactCyclicPacket.nextPhase_three]
  fin_cases c <;> rfl

/-- The exact `(Q1)--(Q5)` packet obtained by reading the quitting
probabilities and promises from the concrete response architecture. -/
def architectureExactCyclicPacket :
    GameTheory.FTVCyclicMinimality.ExactCyclicPacket 3 where
  quitProb := architectureQuitProb
  promise := phaseTarget
  probability_mem := by
    simpa [architectureQuitProb_eq_standardQuitProb,
      GameTheory.FTVCyclicMinimality.ExactCyclicPacket.standardPacket] using
      GameTheory.FTVCyclicMinimality.ExactCyclicPacket.standardPacket.probability_mem
  q1 := by
    simpa [architectureQuitProb_eq_standardQuitProb,
      phaseTarget_eq_standardPromise,
      GameTheory.FTVCyclicMinimality.ExactCyclicPacket.standardPacket] using
      GameTheory.FTVCyclicMinimality.ExactCyclicPacket.standardPacket.q1
  q4 := by
    simpa [architectureQuitProb_eq_standardQuitProb,
      phaseTarget_eq_standardPromise,
      GameTheory.FTVCyclicMinimality.ExactCyclicPacket.standardPacket] using
      GameTheory.FTVCyclicMinimality.ExactCyclicPacket.standardPacket.q4
  q5 := by
    simpa [architectureQuitProb_eq_standardQuitProb,
      GameTheory.FTVCyclicMinimality.ExactCyclicPacket.standardPacket] using
      GameTheory.FTVCyclicMinimality.ExactCyclicPacket.standardPacket.q5
  live := by
    simpa [architectureQuitProb_eq_standardQuitProb,
      GameTheory.FTVCyclicMinimality.ExactCyclicPacket.standardPacket] using
      GameTheory.FTVCyclicMinimality.ExactCyclicPacket.standardPacket.live
  initial := by
    simpa [phaseTarget_eq_standardPromise,
      GameTheory.FTVCyclicMinimality.ExactCyclicPacket.standardPacket] using
      GameTheory.FTVCyclicMinimality.ExactCyclicPacket.standardPacket.initial

@[simp] theorem architectureExactCyclicPacket_quitProb :
    architectureExactCyclicPacket.quitProb = architectureQuitProb := rfl

@[simp] theorem architectureExactCyclicPacket_promise :
    architectureExactCyclicPacket.promise = phaseTarget := rfl

/-- Consequently, the packet read from the architecture has exactly the
standard normalized quitting matrix and promise word. -/
theorem architectureExactCyclicPacket_data_eq_standard :
    architectureExactCyclicPacket.quitProb =
        GameTheory.FTVCyclicMinimality.ExactCyclicPacket.standardPacket.quitProb ∧
      architectureExactCyclicPacket.promise =
        GameTheory.FTVCyclicMinimality.ExactCyclicPacket.standardPacket.promise := by
  exact ⟨architectureQuitProb_eq_standardQuitProb,
    phaseTarget_eq_standardPromise⟩

end FTVCyclicCredibility
end GameTheory
