/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Examples.Sorin.AbsorbingGame

/-!
# The uniform-payoff separation fence in Sorin's absorbing game

This module formalizes the exact accounting obstruction behind Sorin's game.
For the scalar stage payoff `2 * g₁ + g₂`, every cell has value `2` except the
live `(Bottom, Right)` cell, whose value is `1`.  Consequently every positive
finite horizon satisfies the exact identity

```text
2 * averagePayoff₁ + averagePayoff₂ = 2 - bottomRightOccupation.
```

The strategic assertion is isolated here as
`UniformEquilibriaForceBottomRightOccupationVanishing`: sufficiently accurate
uniform approximate equilibria have asymptotically vanishing live
`(Bottom, Right)` occupation.  From that concrete, target-independent
occupation hypothesis, this file proves that every uniform-equilibrium payoff
lies on `2 * w₁ + w₂ = 2`, and hence excludes the discount-constant endpoint
`(1/2, 2/3)`.

The occupation-vanishing assertion is deliberately a named hypothesis rather
than an axiom or a conclusion-bearing reconstruction record.  Discharging it
is delegated to `SorinOccupationVanishing`, which derives it from the
quantitative stopping theorem.  All accounting, limit passage, and endpoint
arithmetic below are unconditional and contain no formal admissions.
-/

noncomputable section

open scoped BigOperators

namespace GameTheory
namespace StochasticGame
namespace SorinAbsorbingGame

open Math.Probability

/-- Indicator of the unique stage cell at which `2 * g₁ + g₂` is below `2`:
the state is live and the action is `(Bottom, Right)`. -/
def bottomRightIndicator (s : State) (a : game.JointAct) : ℝ :=
  if s = State.live ∧ a false = false ∧ a true = false then 1 else 0

/-- Number of live `(Bottom, Right)` occurrences in a finite history. -/
def bottomRightCount {T : ℕ} (h : game.Hist T) : ℝ :=
  ∑ k, bottomRightIndicator (h.1 k).1 (h.1 k).2

/-- Expected finite-horizon occupation fraction of live `(Bottom, Right)`. -/
def bottomRightOccupation (σ : game.BehaviorProfile) (s₀ : State) (T : ℕ) : ℝ :=
  (T : ℝ)⁻¹ * expect (game.histDist σ s₀ T) bottomRightCount

theorem bottomRightIndicator_nonneg (s : State) (a : game.JointAct) :
    0 ≤ bottomRightIndicator s a := by
  unfold bottomRightIndicator
  split <;> norm_num

theorem bottomRightCount_nonneg {T : ℕ} (h : game.Hist T) :
    0 ≤ bottomRightCount h := by
  exact Finset.sum_nonneg fun k _ => bottomRightIndicator_nonneg _ _

theorem bottomRightOccupation_nonneg (σ : game.BehaviorProfile)
    (s₀ : State) (T : ℕ) : 0 ≤ bottomRightOccupation σ s₀ T := by
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg T))
    (expect_nonneg _ _ bottomRightCount_nonneg)

/-- The cellwise accounting identity. -/
theorem weightedStagePayoff_eq_two_sub_bottomRightIndicator
    (s : State) (a : game.JointAct) :
    2 * game.stagePayoff s a false + game.stagePayoff s a true =
      2 - bottomRightIndicator s a := by
  have hrow := Bool.eq_false_or_eq_true (a false)
  have hcol := Bool.eq_false_or_eq_true (a true)
  cases s <;> rcases hrow with hrow | hrow <;> rcases hcol with hcol | hcol <;>
    norm_num [bottomRightIndicator, payoff, pair, hrow, hcol] <;> simp

/-- The pathwise version of the accounting identity. -/
theorem weightedTotalPayoff_eq_two_mul_sub_bottomRightCount
    {T : ℕ} (h : game.Hist T) :
    2 * game.totalPayoff false h + game.totalPayoff true h =
      2 * T - bottomRightCount h := by
  unfold StochasticGame.totalPayoff bottomRightCount
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  calc
    ∑ k, (2 * game.stagePayoff (h.1 k).1 (h.1 k).2 false +
        game.stagePayoff (h.1 k).1 (h.1 k).2 true) =
        ∑ k, (2 - bottomRightIndicator (h.1 k).1 (h.1 k).2) := by
          exact Finset.sum_congr rfl fun k _ =>
            weightedStagePayoff_eq_two_sub_bottomRightIndicator _ _
    _ = 2 * T - ∑ k, bottomRightIndicator (h.1 k).1 (h.1 k).2 := by
      simp [Finset.sum_sub_distrib]
      ring

/-- **Exact finite-horizon accounting fence.**  At every positive horizon,
the weighted average payoff misses `2` by exactly the live `(Bottom, Right)`
occupation. -/
theorem weightedFiniteAveragePayoff_eq_two_sub_bottomRightOccupation
    (σ : game.BehaviorProfile) (s₀ : State) (T : ℕ) (hT : 0 < T) :
    2 * game.finiteAveragePayoff s₀ T σ false +
        game.finiteAveragePayoff s₀ T σ true =
      2 - bottomRightOccupation σ s₀ T := by
  have hTne : (T : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hT)
  unfold StochasticGame.finiteAveragePayoff bottomRightOccupation
  have hpoint : (fun h : game.Hist T =>
      2 * game.totalPayoff false h + game.totalPayoff true h) =
      (fun h => 2 * T - bottomRightCount h) := by
    funext h
    exact weightedTotalPayoff_eq_two_mul_sub_bottomRightCount h
  calc
    2 * ((T : ℝ)⁻¹ * expect (game.histDist σ s₀ T)
        (fun h => game.totalPayoff false h)) +
        (T : ℝ)⁻¹ * expect (game.histDist σ s₀ T)
          (fun h => game.totalPayoff true h) =
      (T : ℝ)⁻¹ * (2 * expect (game.histDist σ s₀ T)
        (fun h => game.totalPayoff false h) +
          expect (game.histDist σ s₀ T) (fun h => game.totalPayoff true h)) := by ring
    _ = (T : ℝ)⁻¹ * expect (game.histDist σ s₀ T)
        (fun h => 2 * game.totalPayoff false h + game.totalPayoff true h) := by
      rw [expect_add, expect_const_mul]
    _ = (T : ℝ)⁻¹ * expect (game.histDist σ s₀ T)
        (fun h => 2 * T - bottomRightCount h) := by rw [hpoint]
    _ = (T : ℝ)⁻¹ *
        (2 * T - expect (game.histDist σ s₀ T) bottomRightCount) := by
      rw [expect_sub, expect_const]
    _ = 2 - (T : ℝ)⁻¹ * expect (game.histDist σ s₀ T) bottomRightCount := by
      field_simp

/-- Quantitative form of the missing strategic lemma.

For every desired occupation error `δ`, there is an equilibrium accuracy
threshold `εbar` such that every uniform `ε`-equilibrium with
`0 < ε ≤ εbar` eventually has live `(Bottom, Right)` occupation at most `δ`
in absolute value.  This statement mentions neither a candidate payoff nor the
desired separation line. -/
def UniformEquilibriaForceBottomRightOccupationVanishing : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∃ εbar : ℝ, 0 < εbar ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ εbar →
        ∀ σ : game.BehaviorProfile,
          game.IsUniformεEquilibrium State.live ε σ →
            ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T →
              bottomRightOccupation σ State.live T ≤ δ

/-- The substantive occupation lemma implies Sorin's separation line for
every semantic uniform-equilibrium payoff. -/
theorem uniformEquilibriumPayoff_weighted_eq_two_of_bottomRightOccupation_vanishing
    (hvanish : UniformEquilibriaForceBottomRightOccupationVanishing)
    (w : Payoff Player)
    (hw : game.IsUniformEquilibriumPayoff State.live w) :
    2 * w false + w true = 2 := by
  have hclose : ∀ η : ℝ, 0 < η → |2 * w false + w true - 2| < η := by
    intro η hη
    obtain ⟨εbar, hεbar, hvanish'⟩ := hvanish (η / 4) (by linarith)
    let ε : ℝ := min εbar (η / 16)
    have hε : 0 < ε := lt_min hεbar (by linarith)
    have hεbar' : ε ≤ εbar := min_le_left _ _
    have hεη : ε ≤ η / 16 := min_le_right _ _
    obtain ⟨σ, Tpay, hpay⟩ := hw ε hε
    have huniform : game.IsUniformεEquilibrium State.live ε σ :=
      ⟨Tpay, fun T hT => (hpay T hT).1⟩
    obtain ⟨Tocc, hocc⟩ := hvanish' ε hε hεbar' σ huniform
    let T := max (max Tpay Tocc) 1
    have hTpay : Tpay ≤ T := le_trans (le_max_left _ _) (le_max_left _ _)
    have hTocc : Tocc ≤ T := le_trans (le_max_right _ _) (le_max_left _ _)
    have hTpos : 0 < T := lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
    have hid := weightedFiniteAveragePayoff_eq_two_sub_bottomRightOccupation
      σ State.live T hTpos
    have hp₁ := (abs_le.mp ((hpay T hTpay).2 false))
    have hp₂ := (abs_le.mp ((hpay T hTpay).2 true))
    have hoLower := bottomRightOccupation_nonneg σ State.live T
    have hoUpper := hocc T hTocc
    rw [abs_lt]
    constructor <;> linarith
  have hz : 2 * w false + w true - 2 = 0 := by
    by_contra hne
    have habs : 0 < |2 * w false + w true - 2| := abs_pos.mpr hne
    exact (lt_irrefl _ (hclose _ habs))
  linarith

/-- Pure arithmetic: the discounted endpoint is not on Sorin's uniform-payoff
separation line. -/
theorem discountedEndpoint_weighted_ne_two :
    2 * pair (1 / 2) (2 / 3) false + pair (1 / 2) (2 / 3) true ≠ 2 := by
  norm_num

/-- **Conditional endpoint-exclusion fence.**  Once the explicitly isolated
occupation-vanishing lemma is supplied, the discount-constant analytic endpoint
`(1/2, 2/3)` is machine-checked not to be a uniform-equilibrium payoff. -/
theorem discountedEndpoint_not_isUniformEquilibriumPayoff_of_bottomRightOccupation_vanishing
    (hvanish : UniformEquilibriaForceBottomRightOccupationVanishing) :
    ¬ game.IsUniformEquilibriumPayoff State.live (pair (1 / 2) (2 / 3)) := by
  intro hendpoint
  exact discountedEndpoint_weighted_ne_two
    (uniformEquilibriumPayoff_weighted_eq_two_of_bottomRightOccupation_vanishing
      hvanish _ hendpoint)

end SorinAbsorbingGame
end StochasticGame
end GameTheory
