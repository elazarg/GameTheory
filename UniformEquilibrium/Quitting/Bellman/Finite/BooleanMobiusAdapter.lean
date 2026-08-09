/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Cooperative.CoalitionalGame.MultilinearExtension
import UniformEquilibrium.Quitting.Bellman.Finite.HazardRowBridge

/-!
# Boolean Möbius coordinates for a quitting stage

A one-stage quitting payoff is a function on the Boolean cube of quitter
coalitions.  Its value at the empty coalition is the continuation payoff, so
it is affine rather than literally a `CoalGame`, whose empty-coalition value
must be zero.  This file removes that constant, applies the existing
unanimity-basis Möbius transform, and then restores the continuation.

The resulting identities say exactly that independent quitting hazards
evaluate the full coalition cube by its multilinear polynomial, and that a
player's pure-Quit-minus-pure-Continue payoff is the corresponding discrete
coordinate derivative.  These are algebraic identities only; no coefficient
sign or support-pivot conclusion is asserted.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct
open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The quitting-stage cube -/

/-- Payoff of the quitter coalition `S`, with the continuation payoff at the
empty coalition. -/
def quittingStageCoalitionPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (S : Finset ι) : Payoff ι :=
  if h : S.Nonempty then reward ⟨S, h⟩ else continuation

/-- The quitting-stage coalition cube centered at its empty-coalition
continuation value, regarded as a coalitional game for one payoff receiver. -/
def quittingStageCenteredCoalGame
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (who : ι) : CoalGame ι where
  v S := quittingStageCoalitionPayoff reward continuation S who - continuation who
  v_empty := by simp [quittingStageCoalitionPayoff]

/-- Möbius/unanimity coefficient of a receiver's centered quitting-stage
coalition cube. -/
def quittingStageMobiusCoeff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (who : ι) (S : Finset ι) : ℝ :=
  (quittingStageCenteredCoalGame reward continuation who).unanimityCoeff S

omit [Fintype ι] in
@[simp] theorem quittingStageMobiusCoeff_empty
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (who : ι) :
    quittingStageMobiusCoeff reward continuation who ∅ = 0 := by
  simp [quittingStageMobiusCoeff, CoalGame.unanimityCoeff,
    quittingStageCenteredCoalGame, quittingStageCoalitionPayoff]

omit [Fintype ι] in
/-- Pointwise Möbius reconstruction of the full quitting-stage cube, with the
affine continuation constant restored. -/
theorem quittingStageCoalitionPayoff_eq_continuation_add_mobius
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (who : ι) (S : Finset ι) :
    quittingStageCoalitionPayoff reward continuation S who =
      continuation who +
        ∑ T ∈ S.powerset, quittingStageMobiusCoeff reward continuation who T := by
  have h := (quittingStageCenteredCoalGame reward continuation who).unanimity_decomposition S
  change quittingStageCoalitionPayoff reward continuation S who - continuation who =
    ∑ T ∈ S.powerset, quittingStageMobiusCoeff reward continuation who T at h
  linarith

omit [DecidableEq ι] in
/-- A Boolean action and its quitter coalition select the same point of the
full quitting-stage payoff cube. -/
theorem quittingRootPayoff_eq_stageCoalitionPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (action : ι → Bool) :
    quittingRootPayoff reward continuation action =
      quittingStageCoalitionPayoff reward continuation (quittingQuitters action) := by
  funext who
  by_cases h : (quittingQuitters action).Nonempty <;>
    simp [quittingRootPayoff, quittingStageCoalitionPayoff, h]

/-- Product-root expectation written as an exact-coalition average of the
full quitting-stage cube. -/
theorem quittingRootExpectedPayoff_eq_sum_coalitionMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootExpectedPayoff reward continuation root who =
      ∑ S : Finset ι, coalitionMass (hazardOfRoot root) S *
        quittingStageCoalitionPayoff reward continuation S who := by
  have hroot : root = fun i =>
      if i ∈ (Finset.univ : Finset ι) then root i else PMF.pure false := by
    funext i
    simp
  unfold quittingRootExpectedPayoff
  rw [hroot, expect_pmfPi_boolFamily_eq_sum_powerset']
  rw [show (Finset.univ : Finset ι).powerset =
      (Finset.univ : Finset (Finset ι)) by ext S; simp]
  apply Finset.sum_congr rfl
  intro S _
  have hquitters : quittingQuitters
      (fun i => if i ∈ S then true else
        if i ∈ (Finset.univ : Finset ι) then false else false) = S := by
    ext i
    simp [quittingQuitters]
  rw [quittingRootPayoff_eq_stageCoalitionPayoff, hquitters]
  simp only [coalitionMass, hazardOfRoot, Finset.compl_eq_univ_sdiff]
  simp only [Finset.mem_univ, if_true]

/-- **One-stage Boolean Möbius adapter.** A product root evaluates the full
coalition-cube payoff by the multilinear polynomial of its centered
unanimity coefficients, with the empty-coalition continuation restored as
the affine constant. -/
theorem quittingRootExpectedPayoff_eq_continuation_add_multilinearValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootExpectedPayoff reward continuation root who =
      continuation who +
        (quittingStageCenteredCoalGame reward continuation who).multilinearValue
          (hazardOfRoot root) := by
  rw [quittingRootExpectedPayoff_eq_sum_coalitionMass]
  let G := quittingStageCenteredCoalGame reward continuation who
  have hcube : ∀ S : Finset ι,
      quittingStageCoalitionPayoff reward continuation S who = continuation who + G.v S := by
    intro S
    change quittingStageCoalitionPayoff reward continuation S who =
      continuation who +
        (quittingStageCoalitionPayoff reward continuation S who - continuation who)
    ring
  simp_rw [hcube, mul_add, Finset.sum_add_distrib]
  have htotal := sum_coalitionMass_supersets (hazardOfRoot root) (∅ : Finset ι)
  have htotal' : ∑ S : Finset ι, coalitionMass (hazardOfRoot root) S = 1 := by
    simpa using htotal
  rw [← Finset.sum_mul, htotal', one_mul]
  change continuation who +
      ∑ S : Finset ι, coalitionMass (hazardOfRoot root) S * G.v S =
    continuation who + G.multilinearValue (hazardOfRoot root)
  rw [G.sum_coalitionMass_mul_value_eq_multilinearValue]

/-- **Unilateral derivative identity.** Pure Quit minus pure Continue at a
product root is the discrete coordinate derivative of the centered full
coalition cube. -/
theorem quittingRootEndpointDifference_eq_mobiusCoordinateDerivative
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootEndpointDifference reward continuation root who =
      (quittingStageCenteredCoalGame reward continuation who).coordinateDerivative
        (hazardOfRoot root) who := by
  unfold quittingRootEndpointDifference quittingRootQuitPayoff quittingRootContinuePayoff
  rw [quittingRootExpectedPayoff_eq_continuation_add_multilinearValue,
    quittingRootExpectedPayoff_eq_continuation_add_multilinearValue]
  have hquit : hazardOfRoot (Function.update root who (PMF.pure true)) =
      Function.update (hazardOfRoot root) who 1 := by
    funext i
    by_cases hi : i = who
    · subst hi
      simp [hazardOfRoot]
    · simp [hazardOfRoot, hi]
  have hcontinue : hazardOfRoot (Function.update root who (PMF.pure false)) =
      Function.update (hazardOfRoot root) who 0 := by
    funext i
    by_cases hi : i = who
    · subst hi
      simp [hazardOfRoot]
    · simp [hazardOfRoot, hi]
  rw [hquit, hcontinue]
  rw [show continuation who +
          (quittingStageCenteredCoalGame reward continuation who).multilinearValue
            (Function.update (hazardOfRoot root) who 1) -
        (continuation who +
          (quittingStageCenteredCoalGame reward continuation who).multilinearValue
            (Function.update (hazardOfRoot root) who 0)) =
      (quittingStageCenteredCoalGame reward continuation who).multilinearValue
            (Function.update (hazardOfRoot root) who 1) -
        (quittingStageCenteredCoalGame reward continuation who).multilinearValue
            (Function.update (hazardOfRoot root) who 0) by ring]
  exact CoalGame.multilinearValue_update_one_sub_update_zero _ _ _

/-- The unilateral quitting gain, separated into the singleton coefficient,
pair coefficients, and all higher-order coefficients of the quitting-stage
cube.  The equality imposes no sign on any of the three terms. -/
theorem quittingRootEndpointDifference_eq_mobiusCardinalitySplit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootEndpointDifference reward continuation root who =
      (quittingStageCenteredCoalGame reward continuation who).coordinateDerivativeOfCard
          (hazardOfRoot root) who 1 +
        (quittingStageCenteredCoalGame reward continuation who).coordinateDerivativeOfCard
            (hazardOfRoot root) who 2 +
          (quittingStageCenteredCoalGame reward continuation who).higherOrderCoordinateDerivative
            (hazardOfRoot root) who := by
  rw [quittingRootEndpointDifference_eq_mobiusCoordinateDerivative,
    CoalGame.coordinateDerivative_eq_singleton_add_pair_add_higherOrder]

end GameTheory
