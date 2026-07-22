/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Module
import GameTheory.Concepts.Equilibrium.SolutionConcepts
import GameTheory.Concepts.Repeated.Basic

/-!
# Discounted Repeated Games

Repetition-generic definitions and results for normalized discounted payoffs
in the deterministic profile-history model. This module supplies discounted
continuation values, their Bellman split and comparison principles, and Nash
equilibrium against history-dependent repeated-strategy deviations.
-/

noncomputable section

open scoped BigOperators

namespace GameTheory

namespace KernelGame

variable {ι : Type}

/-- Normalized discounted average payoff in the repeated game.

The definition is total for any real `δ`, as is customary in Lean, but the
mathematical discounted-payoff interpretation and all convergence/Nash lemmas
use the explicit hypotheses `0 ≤ δ` and `δ < 1`. -/
def discountedAveragePayoff (G : KernelGame ι) (δ : ℝ)
    (σ : G.RepeatedProfile) (who : ι) : ℝ :=
  (1 - δ) * ∑' t : ℕ, δ ^ t * G.eu (G.repeatedPlay σ t) who

/-- The strategic-form kernel game whose strategies are history-dependent
repeated strategies and whose utility is normalized discounted average
payoff. -/
noncomputable def discountedRepeatedKernelGame
    (G : KernelGame ι) (δ : ℝ) : KernelGame ι :=
  KernelGame.ofEU G.RepeatedStrategy
    (fun σ i => G.discountedAveragePayoff δ σ i)

@[simp] theorem discountedRepeatedKernelGame_eu
    (G : KernelGame ι) (δ : ℝ) (σ : G.RepeatedProfile) (who : ι) :
    (G.discountedRepeatedKernelGame δ).eu σ who =
      G.discountedAveragePayoff δ σ who := by
  simp [discountedRepeatedKernelGame]

/-- Normalized discounted continuation payoff of an explicit stage-profile
stream, starting at period `start`.

As with `discountedAveragePayoff`, this is intended as a discounted payoff under
the side conditions `0 ≤ δ` and `δ < 1`. -/
def discountedContinuationPayoff (G : KernelGame ι) (δ : ℝ)
    (play : ℕ → Profile G) (start : ℕ) (who : ι) : ℝ :=
  (1 - δ) * ∑' k : ℕ, δ ^ k * G.eu (play (start + k)) who

/-- A repeated profile's discounted average is the zero-start continuation
payoff of its generated stage-profile stream. -/
theorem discountedAveragePayoff_eq_discountedContinuationPayoff_zero
    (G : KernelGame ι) (δ : ℝ) (σ : G.RepeatedProfile) (who : ι) :
    G.discountedAveragePayoff δ σ who =
      G.discountedContinuationPayoff δ (fun t => G.repeatedPlay σ t) 0 who := by
  simp [discountedAveragePayoff, discountedContinuationPayoff]

/-- Discounted stage utilities are summable when stage utilities are uniformly
bounded and `δ ∈ [0,1)`. -/
theorem summable_discounted_stageEU_of_abs_bound (G : KernelGame ι)
    {δ C : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {σ : G.RepeatedProfile}
    (who : ι) (hbd : ∀ ρ : Profile G, |G.eu ρ who| ≤ C) :
    Summable fun t : ℕ => δ ^ t * G.eu (G.repeatedPlay σ t) who := by
  have hgeom : Summable fun t : ℕ => C * δ ^ t :=
    (summable_geometric_of_lt_one hδ0 hδ1).mul_left C
  refine Summable.of_norm_bounded hgeom ?_
  intro t
  rw [Real.norm_eq_abs]
  calc
    |δ ^ t * G.eu (G.repeatedPlay σ t) who| =
        δ ^ t * |G.eu (G.repeatedPlay σ t) who| := by
          rw [abs_mul, abs_of_nonneg (pow_nonneg hδ0 t)]
    _ ≤ δ ^ t * C :=
        mul_le_mul_of_nonneg_left (hbd (G.repeatedPlay σ t))
          (pow_nonneg hδ0 t)
    _ = C * δ ^ t := by ring

/-- Discounted continuation utilities are summable when stage utilities are
uniformly bounded and `δ ∈ [0,1)`. -/
theorem summable_discounted_continuation_stageEU_of_abs_bound
    (G : KernelGame ι) {δ C : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (play : ℕ → Profile G) (start : ℕ) (who : ι)
    (hbd : ∀ ρ : Profile G, |G.eu ρ who| ≤ C) :
    Summable fun k : ℕ => δ ^ k * G.eu (play (start + k)) who := by
  have hgeom : Summable fun k : ℕ => C * δ ^ k :=
    (summable_geometric_of_lt_one hδ0 hδ1).mul_left C
  refine Summable.of_norm_bounded hgeom ?_
  intro k
  rw [Real.norm_eq_abs]
  calc
    |δ ^ k * G.eu (play (start + k)) who| =
        δ ^ k * |G.eu (play (start + k)) who| := by
          rw [abs_mul, abs_of_nonneg (pow_nonneg hδ0 k)]
    _ ≤ δ ^ k * C :=
        mul_le_mul_of_nonneg_left (hbd (play (start + k))) (pow_nonneg hδ0 k)
    _ = C * δ ^ k := by ring

/-- If every future stage payoff is at most `b`, then the normalized
continuation payoff is at most `b`. -/
theorem discountedContinuationPayoff_le_const_of_forall_stageEU_le
    (G : KernelGame ι) {δ C b : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (play : ℕ → Profile G) (start : ℕ) (who : ι)
    (hbd : ∀ ρ : Profile G, |G.eu ρ who| ≤ C)
    (hle : ∀ k : ℕ, G.eu (play (start + k)) who ≤ b) :
    G.discountedContinuationPayoff δ play start who ≤ b := by
  have hs := G.summable_discounted_continuation_stageEU_of_abs_bound
    hδ0 hδ1 play start who hbd
  have hconst : Summable fun k : ℕ => δ ^ k * b :=
    (summable_geometric_of_lt_one hδ0 hδ1).mul_right b
  have hsum :
      (∑' k : ℕ, δ ^ k * G.eu (play (start + k)) who) ≤
        ∑' k : ℕ, δ ^ k * b := by
    exact hs.tsum_le_tsum
      (fun k => mul_le_mul_of_nonneg_left (hle k) (pow_nonneg hδ0 k)) hconst
  have hone : 1 - δ ≠ 0 := by linarith
  calc
    G.discountedContinuationPayoff δ play start who ≤
        (1 - δ) * (∑' k : ℕ, δ ^ k * b) := by
      exact mul_le_mul_of_nonneg_left hsum (sub_nonneg.mpr hδ1.le)
    _ = b := by
      rw [tsum_mul_right, tsum_geometric_of_lt_one hδ0 hδ1]
      field_simp [hone]

/-- Bellman split for normalized discounted continuation payoffs. -/
theorem discountedContinuationPayoff_eq_head_add
    (G : KernelGame ι) {δ C : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (play : ℕ → Profile G) (start : ℕ) (who : ι)
    (hbd : ∀ ρ : Profile G, |G.eu ρ who| ≤ C) :
    G.discountedContinuationPayoff δ play start who =
      (1 - δ) * G.eu (play start) who +
        δ * G.discountedContinuationPayoff δ play (start + 1) who := by
  let f : ℕ → ℝ := fun k => δ ^ k * G.eu (play (start + k)) who
  have hs : Summable f := by
    simpa [f] using G.summable_discounted_continuation_stageEU_of_abs_bound
      hδ0 hδ1 play start who hbd
  have hsplit : f 0 + (∑' k : ℕ, f (k + 1)) = ∑' k : ℕ, f k := by
    simpa using hs.sum_add_tsum_nat_add 1
  have htail : (∑' k : ℕ, f (k + 1)) =
      δ * ∑' k : ℕ, δ ^ k * G.eu (play (start + 1 + k)) who := by
    calc
      (∑' k : ℕ, f (k + 1)) =
          ∑' k : ℕ, δ * (δ ^ k * G.eu (play (start + 1 + k)) who) := by
        apply tsum_congr
        intro k
        have hnat : start + (k + 1) = start + 1 + k := by omega
        dsimp [f]
        rw [pow_succ, hnat]
        ring
      _ = δ * ∑' k : ℕ, δ ^ k * G.eu (play (start + 1 + k)) who := by
        rw [tsum_mul_left]
  calc
    G.discountedContinuationPayoff δ play start who =
        (1 - δ) * ∑' k : ℕ, f k := by
      rfl
    _ = (1 - δ) * (f 0 + ∑' k : ℕ, f (k + 1)) := by
      rw [hsplit]
    _ = (1 - δ) * G.eu (play start) who +
        δ * G.discountedContinuationPayoff δ play (start + 1) who := by
      rw [htail]
      simp [discountedContinuationPayoff, f]
      ring

/-- Prefix comparison for continuation payoffs. If two streams agree for `q`
periods from `start`, and the first stream's continuation at `start + q` is no
larger, then its continuation at `start` is no larger. -/
theorem discountedContinuationPayoff_le_of_prefix_eq_of_tail_le
    (G : KernelGame ι) {δ C : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (play₁ play₂ : ℕ → Profile G) (start q : ℕ) (who : ι)
    (hbd : ∀ ρ : Profile G, |G.eu ρ who| ≤ C)
    (hpref : ∀ k < q, play₁ (start + k) = play₂ (start + k))
    (htail : G.discountedContinuationPayoff δ play₁ (start + q) who ≤
      G.discountedContinuationPayoff δ play₂ (start + q) who) :
    G.discountedContinuationPayoff δ play₁ start who ≤
      G.discountedContinuationPayoff δ play₂ start who := by
  revert start
  induction q with
  | zero =>
      intro start _hpref htail
      simpa using htail
  | succ q ih =>
      intro start hpref htail
      have hhead : play₁ start = play₂ start := by
        simpa using hpref 0 (Nat.succ_pos q)
      have htail' :
          G.discountedContinuationPayoff δ play₁ (start + 1 + q) who ≤
            G.discountedContinuationPayoff δ play₂ (start + 1 + q) who := by
        have htail_start : start + (q + 1) = start + 1 + q := by omega
        simpa [htail_start] using htail
      have hpref' : ∀ k < q, play₁ (start + 1 + k) = play₂ (start + 1 + k) := by
        intro k hk
        have hk' : k + 1 < q + 1 := Nat.succ_lt_succ hk
        have hnat : start + (k + 1) = start + 1 + k := by omega
        simpa [hnat] using hpref (k + 1) hk'
      have htail_from_next := ih (start + 1) hpref' htail'
      rw [G.discountedContinuationPayoff_eq_head_add hδ0 hδ1 play₁ start who hbd]
      rw [G.discountedContinuationPayoff_eq_head_add hδ0 hδ1 play₂ start who hbd]
      rw [hhead]
      exact add_le_add_right (mul_le_mul_of_nonneg_left htail_from_next hδ0) _

/-- Pointwise dominance of every realized stage payoff implies dominance of
normalized discounted payoffs. -/
theorem discountedAveragePayoff_le_of_forall_stageEU_le (G : KernelGame ι)
    {δ C : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    {σ τ : G.RepeatedProfile} (who : ι)
    (hbd : ∀ ρ : Profile G, |G.eu ρ who| ≤ C)
    (hle : ∀ t : ℕ,
      G.eu (G.repeatedPlay σ t) who ≤
        G.eu (G.repeatedPlay τ t) who) :
    G.discountedAveragePayoff δ σ who ≤ G.discountedAveragePayoff δ τ who := by
  have hsσ := G.summable_discounted_stageEU_of_abs_bound hδ0 hδ1 who hbd (σ := σ)
  have hsτ := G.summable_discounted_stageEU_of_abs_bound hδ0 hδ1 who hbd (σ := τ)
  have hsum :
      (∑' t : ℕ, δ ^ t * G.eu (G.repeatedPlay σ t) who) ≤
        ∑' t : ℕ, δ ^ t * G.eu (G.repeatedPlay τ t) who := by
    exact hsσ.tsum_le_tsum
      (fun t => mul_le_mul_of_nonneg_left (hle t) (pow_nonneg hδ0 t)) hsτ
  exact mul_le_mul_of_nonneg_left hsum (sub_nonneg.mpr hδ1.le)

/-- Normalized discounted payoff of a stationary repeated profile is the stage
payoff, for discount factors in `[0, 1)`. -/
theorem discountedAveragePayoff_stationaryRepeatedProfile
    (G : KernelGame ι) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (σ : Profile G) (who : ι) :
    G.discountedAveragePayoff δ (G.stationaryRepeatedProfile σ) who =
      G.eu σ who := by
  have hne : 1 - δ ≠ 0 := by linarith
  simp [discountedAveragePayoff, tsum_mul_right,
    tsum_geometric_of_lt_one hδ0 hδ1, hne]

/-- Nash equilibrium of the normalized discounted repeated game.

The equilibrium concept allows a unilateral deviation in the repeated-strategy
space: a player may replace their whole history-dependent repeated strategy.
Results using this predicate supply the discount-factor assumptions needed for
the payoff comparison. -/
def IsDiscountedRepeatedNash (G : KernelGame ι) [DecidableEq ι] (δ : ℝ)
    (σ : G.RepeatedProfile) : Prop :=
  ∀ who (dev : G.RepeatedStrategy who),
    G.discountedAveragePayoff δ σ who ≥
      G.discountedAveragePayoff δ (Function.update σ who dev) who

/-- Discounted repeated Nash is ordinary Nash in the packaged repeated
strategic-form kernel game. -/
theorem isDiscountedRepeatedNash_iff_discountedRepeatedKernelGame_isNash
    (G : KernelGame ι) [DecidableEq ι] (δ : ℝ) (σ : G.RepeatedProfile) :
    G.IsDiscountedRepeatedNash δ σ ↔
      (G.discountedRepeatedKernelGame δ).IsNash σ := by
  simp only [IsDiscountedRepeatedNash, KernelGame.IsNash,
    discountedRepeatedKernelGame, KernelGame.eu_ofEU,
    KernelGame.ofEU_Strategy]

/-- Repeating a stage-game Nash profile stationarily is a Nash equilibrium of
the discounted repeated game whenever stage expected payoffs are bounded. -/
theorem stationaryRepeatedProfile_isDiscountedRepeatedNash_of_isNash_of_bounded
    (G : KernelGame ι) [DecidableEq ι]
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    {σ : Profile G} (hN : G.IsNash σ)
    (hbd : ∀ who : ι, ∃ C : ℝ,
      ∀ ρ : Profile G, |G.eu ρ who| ≤ C) :
    G.IsDiscountedRepeatedNash δ (G.stationaryRepeatedProfile σ) := by
  intro who dev
  obtain ⟨C, hC⟩ := hbd who
  exact G.discountedAveragePayoff_le_of_forall_stageEU_le
    (σ := Function.update (G.stationaryRepeatedProfile σ) who dev)
    (τ := G.stationaryRepeatedProfile σ)
    hδ0 hδ1 who hC (fun t => by
      rw [G.repeatedPlay_update_stationaryRepeatedProfile σ who dev t]
      rw [G.repeatedPlay_stationaryRepeatedProfile σ t]
      exact hN who _)

/-- Finite-outcome convenience form of stationary discounted repeated Nash
equilibrium. -/
theorem stationaryRepeatedProfile_isDiscountedRepeatedNash_of_isNash
    (G : KernelGame ι) [DecidableEq ι] [Finite G.Outcome]
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    {σ : Profile G} (hN : G.IsNash σ) :
    G.IsDiscountedRepeatedNash δ (G.stationaryRepeatedProfile σ) := by
  apply G.stationaryRepeatedProfile_isDiscountedRepeatedNash_of_isNash_of_bounded
    hδ0 hδ1 hN
  exact fun who => G.exists_eu_abs_bound_of_finite_outcome who

end KernelGame

end GameTheory
