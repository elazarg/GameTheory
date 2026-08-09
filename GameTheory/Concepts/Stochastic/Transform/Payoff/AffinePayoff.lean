/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.ZeroSum.Basic

/-!
# Positive affine transformations of stochastic-game payoffs

This file transports finite-horizon average payoffs and uniform-equilibrium
payoffs across a positive affine change of each player's stage payoff. The
transition law, discount data, histories, and behavior strategies are unchanged.

The additive constant may depend on the player, while the positive scale is
shared. This is the form needed to normalize a finite two-player zero-sum game
without changing its strategic comparisons.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

/-- Apply the positive-affine formula `c * uᵢ + dᵢ` to stage payoffs while
leaving the stochastic protocol unchanged.

This is an `abbrev` so histories and behavior strategies of the transformed
game remain definitionally equal to those of the original game. -/
abbrev affinePayoff (G : StochasticGame ι)
    (c : ℝ) (d : ι → ℝ) : StochasticGame ι where
  State := G.State
  Act := G.Act
  stagePayoff s a who := c * G.stagePayoff s a who + d who
  transition := G.transition
  discount := G.discount
  discount_nonneg := G.discount_nonneg
  discount_lt_one := G.discount_lt_one

@[simp]
theorem affinePayoff_stagePayoff
    (G : StochasticGame ι) (c : ℝ) (d : ι → ℝ)
    (s : G.State) (a : G.JointAct) (who : ι) :
    (G.affinePayoff c d).stagePayoff s a who =
      c * G.stagePayoff s a who + d who :=
  rfl

@[simp]
theorem affinePayoff_histDist
    (G : StochasticGame ι) [Fintype ι]
    (c : ℝ) (d : ι → ℝ)
    (σ : G.BehaviorProfile) (s₀ : G.State) (T : ℕ) :
    (G.affinePayoff c d).histDist σ s₀ T =
      G.histDist σ s₀ T := by
  induction T with
  | zero => rfl
  | succ T ih =>
      rw [histDist_succ, histDist_succ, ih]
      rfl

@[simp]
theorem affinePayoff_totalPayoff
    (G : StochasticGame ι) (c : ℝ) (d : ι → ℝ)
    (who : ι) {T : ℕ} (h : G.Hist T) :
    (G.affinePayoff c d).totalPayoff who h =
      c * G.totalPayoff who h + T * d who := by
  simp only [totalPayoff, Finset.sum_add_distrib, Finset.mul_sum]
  simp

@[simp]
theorem affinePayoff_finiteAveragePayoff
    (G : StochasticGame ι) [Fintype ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (c : ℝ) (d : ι → ℝ)
    (s₀ : G.State) {T : ℕ} (hT : 0 < T)
    (σ : G.BehaviorProfile) (who : ι) :
    (G.affinePayoff c d).finiteAveragePayoff s₀ T σ who =
      c * G.finiteAveragePayoff s₀ T σ who + d who := by
  rw [finiteAveragePayoff, affinePayoff_histDist]
  simp_rw [affinePayoff_totalPayoff]
  rw [Math.Probability.expect_add,
    Math.Probability.expect_const_mul,
    Math.Probability.expect_const]
  rw [finiteAveragePayoff]
  have hTR : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  field_simp

/-- Positive affine changes of stage payoffs preserve uniform-equilibrium
payoffs, with the corresponding affine change of the payoff vector. -/
theorem isUniformEquilibriumPayoff_affinePayoff_iff
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (c : ℝ) (hc : 0 < c) (d : ι → ℝ)
    (s₀ : G.State) (v : Payoff ι) :
    (G.affinePayoff c d).IsUniformEquilibriumPayoff
        s₀ (fun who => c * v who + d who) ↔
      G.IsUniformEquilibriumPayoff s₀ v := by
  constructor
  · intro h ε hε
    obtain ⟨σ, T₀, hσ⟩ := h (c * ε) (mul_pos hc hε)
    refine ⟨σ, max T₀ 1, ?_⟩
    intro T hT
    have hT₀ : T₀ ≤ T := (le_max_left _ _).trans hT
    have hTpos : 0 < T := (le_max_right T₀ 1).trans hT
    obtain ⟨hNash, hpay⟩ := hσ T hT₀
    constructor
    · intro who dev
      have hdev := hNash who dev
      rw [affinePayoff_finiteAveragePayoff G c d s₀ hTpos σ who,
        affinePayoff_finiteAveragePayoff G c d s₀ hTpos
          (Function.update σ who dev) who] at hdev
      have hfac :
          0 ≤ c * (G.finiteAveragePayoff s₀ T σ who + ε -
            G.finiteAveragePayoff s₀ T
              (Function.update σ who dev) who) := by
        calc
          0 ≤
              (c * G.finiteAveragePayoff s₀ T σ who + d who +
                  c * ε) -
                (c * G.finiteAveragePayoff s₀ T
                    (Function.update σ who dev) who + d who) :=
            sub_nonneg.mpr hdev
          _ = c * (G.finiteAveragePayoff s₀ T σ who + ε -
              G.finiteAveragePayoff s₀ T
                (Function.update σ who dev) who) := by ring
      have hinner :
          0 ≤ G.finiteAveragePayoff s₀ T σ who + ε -
            G.finiteAveragePayoff s₀ T
              (Function.update σ who dev) who :=
        (mul_nonneg_iff_of_pos_left hc).mp hfac
      linarith
    · intro who
      have hp := hpay who
      rw [affinePayoff_finiteAveragePayoff G c d s₀ hTpos σ who] at hp
      rw [show
        c * G.finiteAveragePayoff s₀ T σ who + d who -
            (c * v who + d who) =
          c * (G.finiteAveragePayoff s₀ T σ who - v who) by ring,
        abs_mul, abs_of_pos hc] at hp
      exact (mul_le_mul_iff_of_pos_left hc).mp hp
  · intro h ε hε
    obtain ⟨σ, T₀, hσ⟩ := h (ε / c) (div_pos hε hc)
    refine ⟨σ, max T₀ 1, ?_⟩
    intro T hT
    have hT₀ : T₀ ≤ T := (le_max_left _ _).trans hT
    have hTpos : 0 < T := (le_max_right T₀ 1).trans hT
    obtain ⟨hNash, hpay⟩ := hσ T hT₀
    constructor
    · intro who dev
      have hdev := hNash who dev
      rw [affinePayoff_finiteAveragePayoff G c d s₀ hTpos σ who,
        affinePayoff_finiteAveragePayoff G c d s₀ hTpos
          (Function.update σ who dev) who]
      calc
        c * G.finiteAveragePayoff s₀ T
              (Function.update σ who dev) who + d who ≤
            c * (G.finiteAveragePayoff s₀ T σ who + ε / c) +
              d who := by
          simpa [add_comm] using
            add_le_add_right (mul_le_mul_of_nonneg_left hdev hc.le) (d who)
        _ = c * G.finiteAveragePayoff s₀ T σ who + d who + ε := by
          field_simp
          ring
    · intro who
      rw [affinePayoff_finiteAveragePayoff G c d s₀ hTpos σ who]
      rw [show
        c * G.finiteAveragePayoff s₀ T σ who + d who -
            (c * v who + d who) =
          c * (G.finiteAveragePayoff s₀ T σ who - v who) by ring,
        abs_mul, abs_of_pos hc]
      have hp := hpay who
      simpa [mul_comm] using (le_div_iff₀ hc).mp hp

/-- Transport an arbitrary uniform payoff of an affine-transformed game back
to the original payoff coordinates. -/
theorem isUniformEquilibriumPayoff_of_affinePayoff
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (c : ℝ) (hc : 0 < c) (d : ι → ℝ)
    (s₀ : G.State) (u : Payoff ι)
    (hu : (G.affinePayoff c d).IsUniformEquilibriumPayoff s₀ u) :
    G.IsUniformEquilibriumPayoff s₀
      (fun who => (u who - d who) / c) := by
  apply
    (G.isUniformEquilibriumPayoff_affinePayoff_iff c hc d s₀
      (fun who => (u who - d who) / c)).mp
  convert hu using 1
  funext who
  field_simp
  ring

/-! ### Normalization of finite two-player zero-sum games -/

/-- Normalize the row payoff into `[0,1]` using an absolute bound `C`.
The opposite translations for the two players preserve zero-sum structure. -/
abbrev normalizedZeroSumPayoff
    (G : StochasticGame (Fin 2)) (C : ℝ) :
    StochasticGame (Fin 2) :=
  G.affinePayoff (1 / (2 * C + 1))
    (fun who => if who = 0 then C / (2 * C + 1)
      else -C / (2 * C + 1))

theorem normalizedZeroSumPayoff_scale_pos
    {C : ℝ} (hC : 0 ≤ C) :
    0 < 1 / (2 * C + 1) := by
  positivity

theorem normalizedZeroSumPayoff_stagePayoff_zero_nonneg
    (G : StochasticGame (Fin 2)) (C : ℝ)
    (hC : ∀ s a, |G.stagePayoff s a 0| ≤ C)
    (s : G.State) (a : G.JointAct) :
    0 ≤ (G.normalizedZeroSumPayoff C).stagePayoff s a 0 := by
  have hC0 : 0 ≤ C :=
    (abs_nonneg (G.stagePayoff s a 0)).trans (hC s a)
  have hlower : -C ≤ G.stagePayoff s a 0 :=
    (abs_le.mp (hC s a)).1
  change 0 ≤
    1 / (2 * C + 1) * G.stagePayoff s a 0 +
      C / (2 * C + 1)
  have hden : 0 < 2 * C + 1 := by linarith
  rw [one_div, div_eq_mul_inv]
  have hinv : 0 < (2 * C + 1)⁻¹ := inv_pos.mpr hden
  nlinarith

theorem normalizedZeroSumPayoff_stagePayoff_zero_le_one
    (G : StochasticGame (Fin 2)) (C : ℝ)
    (hC : ∀ s a, |G.stagePayoff s a 0| ≤ C)
    (s : G.State) (a : G.JointAct) :
    (G.normalizedZeroSumPayoff C).stagePayoff s a 0 ≤ 1 := by
  have hC0 : 0 ≤ C :=
    (abs_nonneg (G.stagePayoff s a 0)).trans (hC s a)
  have hupper : G.stagePayoff s a 0 ≤ C :=
    (abs_le.mp (hC s a)).2
  change
    1 / (2 * C + 1) * G.stagePayoff s a 0 +
      C / (2 * C + 1) ≤ 1
  have hden : 0 < 2 * C + 1 := by linarith
  rw [one_div, div_eq_mul_inv]
  have hinv : 0 < (2 * C + 1)⁻¹ := inv_pos.mpr hden
  have hmul :
      (G.stagePayoff s a 0 + C) * (2 * C + 1)⁻¹ ≤
        (2 * C + 1) * (2 * C + 1)⁻¹ :=
    mul_le_mul_of_nonneg_right (by linarith) hinv.le
  rw [mul_inv_cancel₀ hden.ne'] at hmul
  nlinarith

theorem normalizedZeroSumPayoff_isZeroSum
    (G : StochasticGame (Fin 2)) (C : ℝ)
    (hzs : G.IsZeroSum) :
    (G.normalizedZeroSumPayoff C).IsZeroSum := by
  intro s a
  simp only [show (1 : Fin 2) ≠ 0 by decide, if_false, if_pos]
  rw [hzs s a]
  ring

/-- Every finite two-player zero-sum stochastic game has a positive affine
normalization whose row stage payoff lies in `[0,1]`. -/
theorem exists_normalizedZeroSumPayoff
    (G : StochasticGame (Fin 2))
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (hzs : G.IsZeroSum) :
    ∃ C : ℝ,
      0 ≤ C ∧
      (∀ s a, |G.stagePayoff s a 0| ≤ C) ∧
      0 < 1 / (2 * C + 1) ∧
      (∀ s a, 0 ≤ (G.normalizedZeroSumPayoff C).stagePayoff s a 0) ∧
      (∀ s a, (G.normalizedZeroSumPayoff C).stagePayoff s a 0 ≤ 1) ∧
      (G.normalizedZeroSumPayoff C).IsZeroSum := by
  obtain ⟨C, hC⟩ := Math.Probability.exists_abs_bound_of_finite
    (fun p : G.State × G.JointAct => G.stagePayoff p.1 p.2 0)
  let C' := max C 0
  have hC' : ∀ s a, |G.stagePayoff s a 0| ≤ C' :=
    fun s a => (hC (s, a)).trans (le_max_left C 0)
  have hC'0 : 0 ≤ C' := le_max_right C 0
  refine ⟨C', hC'0, hC', normalizedZeroSumPayoff_scale_pos hC'0, ?_, ?_,
    G.normalizedZeroSumPayoff_isZeroSum C' hzs⟩
  · intro s a
    exact G.normalizedZeroSumPayoff_stagePayoff_zero_nonneg C' hC' s a
  · intro s a
    exact G.normalizedZeroSumPayoff_stagePayoff_zero_le_one C' hC' s a

end StochasticGame
end GameTheory
