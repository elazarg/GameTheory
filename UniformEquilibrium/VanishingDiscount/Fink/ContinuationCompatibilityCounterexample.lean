/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.LinearAlgebra.MixedCompatibilityCharge
import Math.Probability
import Mathlib.Probability.Distributions.Uniform

/-!
# Player-owned flows do not imply continuation compatibility

This file gives a finite Fink-shaped counterexample to a tempting
continuation-gluing step.

There are two states, two players, and two pure transitions.  The baseline
law is uniform; the positive and negative actions lead deterministically to
the corresponding state.  For each player the two transition-difference
columns sum to zero with nonnegative weights, so every player has an exact
owned circulation.

The permitted continuation profiles are coupled diagonally by one scalar
`x ∈ [0,1]`.  Player zero can satisfy all of their inequalities at `x = 1`,
and player one can satisfy all of theirs at `x = 0`, but no common `x`
satisfies both.  The obstruction is the mixed positive circuit consisting
of player zero's lower bound `x ≥ 2/3` and player one's upper bound
`-x ≥ -1/3`.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace FinkContinuationCompatibilityCounterexample

open Math.LinearAlgebra Math.Probability

abbrev Player := Bool
abbrev State := Bool
abbrev Action := Bool
abbrev Facet := Bool

/-- Uniform baseline transition on the two states. -/
def baseline : PMF State :=
  PMF.uniformOfFintype State

/-- The two available actions lead deterministically to their namesake
states. -/
def actionKernel (action : Action) : PMF State :=
  PMF.pure action

/-- The shared one-dimensional continuation profile.  Both players use the
same profile `(-x,x)`, which is the coupling responsible for the mixed
obstruction. -/
def continuationValue (x : ℝ) (state : State) : ℝ :=
  if state then x else -x

/-- Bellman continuation difference of one pure transition relative to the
uniform baseline. -/
def continuationGain (action : Action) (x : ℝ) : ℝ :=
  expect (actionKernel action) (continuationValue x) -
    expect baseline (continuationValue x)

@[simp]
theorem continuationGain_true (x : ℝ) :
    continuationGain true x = x := by
  simp [continuationGain, actionKernel, baseline, continuationValue,
    expect_eq_sum, PMF.uniformOfFintype_apply]

@[simp]
theorem continuationGain_false (x : ℝ) :
    continuationGain false x = -x := by
  simp [continuationGain, actionKernel, baseline, continuationValue,
    expect_eq_sum, PMF.uniformOfFintype_apply]

/-- Transition-difference column of an action relative to the baseline. -/
def transitionDifference
    (action : Action) (destination : State) : ℝ :=
  (actionKernel action destination).toReal -
    (baseline destination).toReal

/-- Each player's two actual transition differences form a nonnegative
owned circulation. -/
theorem sum_transitionDifference_eq_zero
    (destination : State) :
    ∑ action : Action,
      transitionDifference action destination = 0 := by
  cases destination <;>
    simp [transitionDifference, actionKernel, baseline,
      PMF.uniformOfFintype_apply]

/-- Right-hand sides of the two Bellman inequalities owned by each player.

Player zero requires `x ≥ 2/3` and `-x ≥ -1`.
Player one requires `x ≥ 0` and `-x ≥ -1/3`. -/
def playerRhs (who : Player) (action : Action) : ℝ :=
  match who, action with
  | false, true => 2 / 3
  | false, false => -1
  | true, true => 0
  | true, false => -(1 / 3)

/-- Feasibility of one player's inequalities on the compact coupled
continuation segment. -/
def PlayerFeasible (who : Player) (x : ℝ) : Prop :=
  0 ≤ x ∧ x ≤ 1 ∧
    ∀ action, playerRhs who action ≤ continuationGain action x

theorem player_zero_feasible :
    PlayerFeasible false 1 := by
  constructor
  · norm_num
  constructor
  · norm_num
  · intro action
    cases action <;> norm_num [playerRhs]

theorem player_one_feasible :
    PlayerFeasible true 0 := by
  constructor
  · norm_num
  constructor
  · norm_num
  · intro action
    cases action <;> norm_num [playerRhs]

/-- Despite exact owned circulations and separate feasibility, no common
continuation on the coupled segment satisfies both players. -/
theorem no_common_continuation :
    ¬∃ x, PlayerFeasible false x ∧ PlayerFeasible true x := by
  rintro ⟨x, hzero, hone⟩
  have hlower := hzero.2.2 true
  have hupper := hone.2.2 false
  simp only [playerRhs, continuationGain_true] at hlower
  simp only [playerRhs, continuationGain_false] at hupper
  linarith

/-- One-dimensional normal of a common facet of `[0,1]`. -/
def facetNormal (facet : Facet) : Fin 1 → ℝ :=
  fun _ => if facet then -1 else 1

/-- One-dimensional Bellman-difference normal of a pure action. -/
def playerNormal
    (_who : Player) (action : Action) : Fin 1 → ℝ :=
  fun _ => if action then 1 else -1

/-- The mixed Farkas multiplier: player zero's positive action and player
one's negative action both receive mass one. -/
def mixedMultiplier :
    CoupledRow Facet Player (fun _ => Action) → ℝ
  | Sum.inl _ => 0
  | Sum.inr ⟨who, action⟩ =>
      if who = false ∧ action = true then 1
      else if who = true ∧ action = false then 1
      else 0

/-- The mixed multiplier is a nonnegative zero-normal balance. -/
theorem mixedMultiplier_isNonnegativeBalance :
    IsNonnegativeBalance
      (coupledNormal facetNormal playerNormal)
      mixedMultiplier := by
  constructor
  · intro row
    rcases row with facet | ⟨who, action⟩
    · simp [mixedMultiplier]
    · cases who <;> cases action <;> simp [mixedMultiplier]
  · intro coordinate
    fin_cases coordinate
    rw [Fintype.sum_sum_type, Fintype.sum_sigma]
    norm_num [coupledNormal, facetNormal, playerNormal, mixedMultiplier]

/-- Normalize the mixed player mass to one. -/
def normalizedMixedMultiplier :
    CoupledRow Facet Player (fun _ => Action) → ℝ :=
  fun row => mixedMultiplier row / 2

theorem normalizedMixedMultiplier_isNonnegativeBalance :
    IsNonnegativeBalance
      (coupledNormal facetNormal playerNormal)
      normalizedMixedMultiplier := by
  constructor
  · intro row
    exact div_nonneg
      (mixedMultiplier_isNonnegativeBalance.1 row)
      (by norm_num)
  · intro coordinate
    have hbalance :=
      mixedMultiplier_isNonnegativeBalance.2 coordinate
    calc
      (∑ row,
        normalizedMixedMultiplier row *
          coupledNormal facetNormal playerNormal row coordinate) =
          (∑ row,
            mixedMultiplier row *
              coupledNormal
                facetNormal playerNormal row coordinate) / 2 := by
            simp only [normalizedMixedMultiplier, div_mul_eq_mul_div]
            rw [Finset.sum_div]
      _ = 0 := by rw [hbalance, zero_div]

theorem normalizedMixedMultiplier_mass_eq_one :
    coupledRelaxedMultiplierMass normalizedMixedMultiplier = 1 := by
  rw [coupledRelaxedMultiplierMass]
  norm_num [normalizedMixedMultiplier, mixedMultiplier]

/-- The mixed circuit has strictly positive weighted right-hand side:
`2/3 - 1/3 = 1/3`. -/
theorem mixedMultiplier_rhs_eq :
    (∑ row,
      mixedMultiplier row *
        coupledRelaxedRhs
          (fun facet : Facet => if facet then -1 else 0)
          playerRhs 0 row) =
      (1 / 3 : ℝ) := by
  rw [Fintype.sum_sum_type, Fintype.sum_sigma]
  norm_num [mixedMultiplier, coupledRelaxedRhs, playerRhs]

theorem mixedMultiplier_rhs_pos :
    0 <
      ∑ row,
        mixedMultiplier row *
          coupledRelaxedRhs
            (fun facet : Facet => if facet then -1 else 0)
            playerRhs 0 row := by
  rw [mixedMultiplier_rhs_eq]
  norm_num

/-- After normalization the mixed certificate value is `1/6`. -/
theorem normalizedMixedMultiplier_rhs_eq :
    (∑ row,
      normalizedMixedMultiplier row *
        coupledRelaxedRhs
          (fun facet : Facet => if facet then -1 else 0)
          playerRhs 0 row) =
      (1 / 6 : ℝ) := by
  calc
    (∑ row,
      normalizedMixedMultiplier row *
        coupledRelaxedRhs
          (fun facet : Facet => if facet then -1 else 0)
          playerRhs 0 row) =
        (∑ row,
          mixedMultiplier row *
            coupledRelaxedRhs
              (fun facet : Facet => if facet then -1 else 0)
              playerRhs 0 row) / 2 := by
          simp only [normalizedMixedMultiplier, div_mul_eq_mul_div]
          rw [Finset.sum_div]
    _ = 1 / 6 := by rw [mixedMultiplier_rhs_eq]; norm_num

/-- The mixed response-extraction theorem is sharp at the midpoint: its
normalized value is attained by an actual player-owned constraint. -/
theorem normalizedMixedMultiplier_extracts_midpoint_response :
    ∃ who, ∃ action,
      (1 / 6 : ℝ) ≤
        playerRhs who action -
          rowEval (playerNormal who) action
            (fun _ : Fin 1 => (1 / 2 : ℝ)) := by
  have hfacet :
      ∀ facet,
        (if facet then (-1 : ℝ) else 0) ≤
          rowEval facetNormal facet
            (fun _ : Fin 1 => (1 / 2 : ℝ)) := by
    intro facet
    cases facet <;> norm_num [rowEval, facetNormal]
  obtain ⟨who, action, hresponse⟩ :=
    exists_playerConstraintDeficit_ge_coupledWeightedRhs
      facetNormal
      (fun facet : Facet => if facet then -1 else 0)
      playerNormal playerRhs normalizedMixedMultiplier
      normalizedMixedMultiplier_isNonnegativeBalance
      normalizedMixedMultiplier_mass_eq_one
      (fun _ : Fin 1 => (1 / 2 : ℝ)) hfacet
  rw [normalizedMixedMultiplier_rhs_eq] at hresponse
  exact ⟨who, action, hresponse⟩

/-- Uniform relaxation needed by the two conflicting inequalities. -/
def coupledViolation (x : ℝ) : ℝ :=
  max (2 / 3 - x) (x - 1 / 3)

/-- Every continuation point pays at least the normalized mixed-circuit
margin. -/
theorem one_six_le_coupledViolation (x : ℝ) :
    (1 / 6 : ℝ) ≤ coupledViolation x := by
  have hleft : 2 / 3 - x ≤ coupledViolation x :=
    le_max_left _ _
  have hright : x - 1 / 3 ≤ coupledViolation x :=
    le_max_right _ _
  dsimp only [coupledViolation] at hleft hright ⊢
  linarith

/-- The minimum violation is attained at the strict interior midpoint, so
the mixed circuit does not force a proper face of `[0,1]`. -/
theorem coupledViolation_midpoint_eq :
    coupledViolation (1 / 2) = (1 / 6 : ℝ) := by
  norm_num [coupledViolation, max_eq_left, max_eq_right]

theorem midpoint_mem_strictInterior :
    (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < 1 := by
  norm_num

/-- Consequently the global normal cone does not have the playerwise
balance-decomposition property required for continuation gluing. -/
theorem not_hasPlayerwiseBalanceDecomposition :
    ¬HasPlayerwiseBalanceDecomposition facetNormal playerNormal := by
  intro hdecompose
  obtain ⟨v, hvBalance, hvPlayer, hvFacet⟩ :=
    hdecompose mixedMultiplier
      mixedMultiplier_isNonnegativeBalance
  have hcommon :
      ∀ who facet, v who (Sum.inl facet) = 0 := by
    intro who facet
    have hsum := hvFacet facet
    have hnonneg :
        ∀ owner, 0 ≤ v owner (Sum.inl facet) :=
      fun owner => (hvBalance owner).1 (Sum.inl facet)
    have hzero :
        (fun owner => v owner (Sum.inl facet)) = 0 := by
      apply
        (Fintype.sum_eq_zero_iff_of_nonneg hnonneg).mp
      simpa [mixedMultiplier] using hsum
    exact congrFun hzero who
  have hbalance := (hvBalance false).2 (0 : Fin 1)
  have hpositive :
      v false (Sum.inr true) = 1 := by
    simpa [mixedMultiplier] using hvPlayer false true
  have hnegative :
      v false (Sum.inr false) = 0 := by
    simpa [mixedMultiplier] using hvPlayer false false
  simp only [playerSubsystemNormal] at hbalance
  rw [Fintype.sum_sum_type] at hbalance
  simp [hcommon, hpositive, hnegative] at hbalance
  norm_num [playerNormal] at hbalance

/-- All ingredients of the failed implication hold simultaneously. -/
theorem ownedFlows_and_playerwiseFeasible_but_not_coupled :
    (∀ _who : Player, ∀ destination,
      ∑ action : Action,
        transitionDifference action destination = 0) ∧
    (∃ x, PlayerFeasible false x) ∧
    (∃ x, PlayerFeasible true x) ∧
    ¬∃ x, PlayerFeasible false x ∧ PlayerFeasible true x := by
  exact ⟨fun _ => sum_transitionDifference_eq_zero,
    ⟨1, player_zero_feasible⟩,
    ⟨0, player_one_feasible⟩,
    no_common_continuation⟩

end FinkContinuationCompatibilityCounterexample
end StochasticGame
end GameTheory
