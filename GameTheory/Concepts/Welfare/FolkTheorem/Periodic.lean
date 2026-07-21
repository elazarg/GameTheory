/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SumOverResidueClass
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Math.SimplexApproximation
import GameTheory.Concepts.Mixed.MixedExtension
import GameTheory.Concepts.ZeroSum.SecurityStrategy
import GameTheory.Concepts.Welfare.FolkTheorem.Discounting

noncomputable section

open scoped BigOperators

namespace GameTheory

namespace KernelGame

variable {ι : Type}

/-- Equivalence between residues modulo a positive natural and `Fin n`, using
the canonical representative value. -/
def zmodFinEquiv (n : ℕ) [NeZero n] : ZMod n ≃ Fin n where
  toFun j := ⟨j.val, j.val_lt⟩
  invFun k := (k.val : ZMod n)
  left_inv j := by
    apply ZMod.val_injective n
    simp
  right_inv k := by
    ext
    simp [Nat.mod_eq_of_lt k.isLt]

/-- Adding a fixed offset modulo `n` is injective on `Fin n`. -/
theorem fin_rotate_injective (n : ℕ) [NeZero n] (start : ℕ) :
    Function.Injective (fun j : Fin n => Fin.ofNat n (start + j)) := by
  intro j k h
  apply Fin.ext
  have hval : (start + (j : ℕ)) % n = (start + (k : ℕ)) % n := by
    simpa [Fin.ofNat] using congrArg Fin.val h
  have hz : ((j : ℕ) : ZMod n) = ((k : ℕ) : ZMod n) := by
    have hzk : ((start + (j : ℕ) : ℕ) : ZMod n) =
        ((start + (k : ℕ) : ℕ) : ZMod n) := by
      rw [ZMod.natCast_eq_natCast_iff']
      exact hval
    have hzk' : ((start : ZMod n) + ((j : ℕ) : ZMod n)) =
        ((start : ZMod n) + ((k : ℕ) : ZMod n)) := by
      simpa using hzk
    exact add_left_cancel hzk'
  have hmod : (j : ℕ) % n = (k : ℕ) % n := by
    rw [← ZMod.natCast_eq_natCast_iff']
    exact hz
  simpa [Nat.mod_eq_of_lt j.isLt, Nat.mod_eq_of_lt k.isLt] using hmod

/-- The permutation of cycle phases induced by adding `start` modulo `n`. -/
def finRotateEquiv (n : ℕ) [NeZero n] (start : ℕ) : Fin n ≃ Fin n :=
  Equiv.ofBijective (fun j : Fin n => Fin.ofNat n (start + j))
    ⟨fin_rotate_injective n start,
      (Finite.injective_iff_surjective.mp (fin_rotate_injective n start))⟩

@[simp] theorem finRotateEquiv_apply (n : ℕ) [NeZero n] (start : ℕ) (j : Fin n) :
    finRotateEquiv n start j = Fin.ofNat n (start + j) :=
  rfl

/-- Rotating a finite cycle does not change its finite sum. -/
theorem sum_fin_rotate {n : ℕ} [NeZero n] (start : ℕ) (f : Fin n → ℝ) :
    (∑ j : Fin n, f (Fin.ofNat n (start + j))) = ∑ j : Fin n, f j := by
  exact Fintype.sum_equiv (finRotateEquiv n start)
    (fun j : Fin n => f (Fin.ofNat n (start + j))) f (fun j => by simp)

/-- Exact normalized discounted payoff of a periodic repeated profile.  The
discounted weights over the cycle phases are proportional to `δ ^ phase`. -/
theorem discountedAveragePayoff_periodicRepeatedProfile_eq
    (G : KernelGame ι) [Finite G.Outcome] {n : ℕ} [NeZero n]
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (cycle : Fin n → Profile G) (who : ι) :
    G.discountedAveragePayoff δ (G.periodicRepeatedProfile cycle) who =
      (∑ j : Fin n, δ ^ (j : ℕ) * G.eu (cycle j) who) /
        (∑ j : Fin n, δ ^ (j : ℕ)) := by
  obtain ⟨C, hC⟩ := G.exists_stageEU_abs_bound_of_finite_outcome who
  let σ : G.RepeatedProfile := G.periodicRepeatedProfile cycle
  have hs : Summable fun t : ℕ => δ ^ t * G.eu (G.repeatedPlay σ t) who :=
    G.summable_discounted_stageEU_of_abs_bound hδ0 hδ1 who hC (σ := σ)
  have hpow : δ ^ n < 1 := pow_lt_one₀ hδ0 hδ1 (NeZero.ne n)
  have hden_pos : 0 < ∑ j : Fin n, δ ^ (j : ℕ) := by
    have hle : (1 : ℝ) ≤ ∑ j : Fin n, δ ^ (j : ℕ) := by
      have hsingle := Finset.single_le_sum
        (s := (Finset.univ : Finset (Fin n)))
        (f := fun j : Fin n => δ ^ (j : ℕ))
        (fun j _ => pow_nonneg hδ0 (j : ℕ)) (Finset.mem_univ (0 : Fin n))
      simpa using hsingle
    exact zero_lt_one.trans_le hle
  have hden_ne : (∑ j : Fin n, δ ^ (j : ℕ)) ≠ 0 := ne_of_gt hden_pos
  have hgeom : (∑ j : Fin n, δ ^ (j : ℕ)) * (1 - δ) = 1 - δ ^ n := by
    simpa [Finset.sum_range] using (geom_sum_mul_of_le_one hδ1.le n)
  have hone : 1 - δ ≠ 0 := by linarith
  have hsplit :
      (∑' t : ℕ, δ ^ t * G.eu (G.repeatedPlay σ t) who) =
        ∑ j : ZMod n, ∑' m : ℕ,
          δ ^ (j.val + n * m) * G.eu (cycle ⟨j.val, j.val_lt⟩) who := by
    rw [Nat.sumByResidueClasses hs n]
    refine Finset.sum_congr rfl ?_
    intro j _hj
    apply tsum_congr
    intro m
    subst σ
    rw [G.repeatedPlay_periodicRepeatedProfile]
    congr 2
    ext
    simp [Fin.ofNat, Nat.mod_eq_of_lt j.val_lt]
  have hinner : ∀ j : ZMod n,
      (∑' m : ℕ, δ ^ (j.val + n * m) * G.eu (cycle ⟨j.val, j.val_lt⟩) who) =
        (δ ^ j.val * G.eu (cycle ⟨j.val, j.val_lt⟩) who) * (1 - δ ^ n)⁻¹ := by
    intro j
    calc
      (∑' m : ℕ, δ ^ (j.val + n * m) * G.eu (cycle ⟨j.val, j.val_lt⟩) who) =
          ∑' m : ℕ,
            (δ ^ j.val * G.eu (cycle ⟨j.val, j.val_lt⟩) who) * (δ ^ n) ^ m := by
        apply tsum_congr
        intro m
        rw [pow_add, pow_mul]
        ring
      _ = (δ ^ j.val * G.eu (cycle ⟨j.val, j.val_lt⟩) who) *
          (∑' m : ℕ, (δ ^ n) ^ m) := by
        rw [tsum_mul_left]
      _ = (δ ^ j.val * G.eu (cycle ⟨j.val, j.val_lt⟩) who) *
          (1 - δ ^ n)⁻¹ := by
        rw [tsum_geometric_of_lt_one (pow_nonneg hδ0 n) hpow]
  have hzsum :
      (∑ j : ZMod n, δ ^ j.val * G.eu (cycle ⟨j.val, j.val_lt⟩) who) =
        ∑ j : Fin n, δ ^ (j : ℕ) * G.eu (cycle j) who := by
    exact Fintype.sum_equiv (zmodFinEquiv n)
      (fun j : ZMod n => δ ^ j.val * G.eu (cycle ⟨j.val, j.val_lt⟩) who)
      (fun j : Fin n => δ ^ (j : ℕ) * G.eu (cycle j) who)
      (fun j => rfl)
  calc
    G.discountedAveragePayoff δ (G.periodicRepeatedProfile cycle) who =
        (1 - δ) * (∑ j : ZMod n,
          (δ ^ j.val * G.eu (cycle ⟨j.val, j.val_lt⟩) who) * (1 - δ ^ n)⁻¹) := by
      simp only [discountedAveragePayoff]
      rw [show (G.periodicRepeatedProfile cycle) = σ from rfl]
      rw [hsplit]
      congr 1
      exact Finset.sum_congr rfl (fun j _ => hinner j)
    _ = (1 - δ) * ((∑ j : ZMod n,
          δ ^ j.val * G.eu (cycle ⟨j.val, j.val_lt⟩) who) * (1 - δ ^ n)⁻¹) := by
      rw [Finset.sum_mul]
    _ = (∑ j : Fin n, δ ^ (j : ℕ) * G.eu (cycle j) who) /
        (∑ j : Fin n, δ ^ (j : ℕ)) := by
      rw [hzsum]
      rw [← hgeom]
      field_simp [hden_ne, hone]

/-- Discounted continuation of a periodic path from any start period is the
discounted average of the corresponding phase-rotated cycle. -/
theorem discountedContinuationPayoff_periodicPath_eq
    (G : KernelGame ι) [Finite G.Outcome] {n : ℕ} [NeZero n]
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (cycle : Fin n → Profile G) (start : ℕ) (who : ι) :
    G.discountedContinuationPayoff δ (fun t => cycle (Fin.ofNat n t)) start who =
      (∑ j : Fin n, δ ^ (j : ℕ) *
          G.eu (cycle (Fin.ofNat n (start + j))) who) /
        (∑ j : Fin n, δ ^ (j : ℕ)) := by
  let rotated : Fin n → Profile G := fun j => cycle (Fin.ofNat n (start + j))
  have hcont_avg :
      G.discountedContinuationPayoff δ (fun t => cycle (Fin.ofNat n t)) start who =
        G.discountedAveragePayoff δ (G.periodicRepeatedProfile rotated) who := by
    simp only [discountedContinuationPayoff, discountedAveragePayoff]
    congr 1
    apply tsum_congr
    intro k
    congr 2
    unfold rotated
    ext
    simp [Fin.ofNat, Nat.add_mod]
  rw [hcont_avg]
  rw [G.discountedAveragePayoff_periodicRepeatedProfile_eq hδ0 hδ1 rotated who]

/-- Finite discounted phase weights converge to uniform cycle weights as
`δ → 1` from below. -/
theorem exists_discountFactor_threshold_weighted_cycle_average
    {n : ℕ} [NeZero n] (a : Fin n → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 ≤ δ₀ ∧ δ₀ < 1 ∧
      ∀ δ : ℝ, δ₀ < δ → δ < 1 →
        |(∑ j : Fin n, δ ^ (j : ℕ) * a j) / (∑ j : Fin n, δ ^ (j : ℕ)) -
          (n : ℝ)⁻¹ * ∑ j : Fin n, a j| < ε := by
  let F : ℝ → ℝ := fun δ =>
    (∑ j : Fin n, δ ^ (j : ℕ) * a j) / (∑ j : Fin n, δ ^ (j : ℕ))
  have hden1 : (∑ j : Fin n, (1 : ℝ) ^ (j : ℕ)) ≠ 0 := by
    simp [NeZero.ne n]
  have hcont : ContinuousAt F 1 := by
    dsimp [F]
    apply ContinuousAt.div
    · exact (continuous_finsetSum (Finset.univ : Finset (Fin n)) (fun j _ =>
        (continuous_id.pow (j : ℕ)).mul continuous_const)).continuousAt
    · exact (continuous_finsetSum (Finset.univ : Finset (Fin n)) (fun j _ =>
        continuous_id.pow (j : ℕ))).continuousAt
    · exact hden1
  have hF1 : F 1 = (n : ℝ)⁻¹ * ∑ j : Fin n, a j := by
    dsimp [F]
    simp [Finset.sum_const, nsmul_eq_mul]
    field_simp [Nat.cast_ne_zero.mpr (NeZero.ne n)]
  rcases (Metric.tendsto_nhds_nhds.1 hcont) ε hε with ⟨d, hdpos, hd⟩
  let r : ℝ := min d 1
  have hrpos : 0 < r := lt_min hdpos zero_lt_one
  have hrle_d : r ≤ d := min_le_left d 1
  have hrle_one : r ≤ 1 := min_le_right d 1
  refine ⟨1 - r / 2, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · intro δ hδ0 hδ1
    have hdist : dist δ 1 < d := by
      rw [Real.dist_eq]
      have hδle : δ ≤ 1 := hδ1.le
      rw [abs_of_nonpos (sub_nonpos.mpr hδle)]
      nlinarith
    have hclose := hd hdist
    rw [Real.dist_eq] at hclose
    simpa [F, hF1] using hclose

/-- Combine finitely many lower-bound discount thresholds into one common
threshold. -/
theorem exists_common_discountFactor_threshold_of_finite
    {α : Type} [Finite α] {P : α → ℝ → Prop}
    (hP : ∀ a : α, ∃ δ₀ : ℝ, 0 ≤ δ₀ ∧ δ₀ < 1 ∧
      ∀ δ : ℝ, δ₀ < δ → δ < 1 → P a δ) :
    ∃ δ₀ : ℝ, 0 ≤ δ₀ ∧ δ₀ < 1 ∧
      ∀ δ : ℝ, δ₀ < δ → δ < 1 → ∀ a : α, P a δ := by
  classical
  letI : Fintype α := Fintype.ofFinite α
  choose d hd0 hd1 hdP using hP
  by_cases hne : (Finset.univ : Finset α).Nonempty
  · let δ₀ : ℝ := (Finset.univ : Finset α).sup' hne d
    refine ⟨δ₀, ?_, ?_, ?_⟩
    · rcases hne with ⟨a0, ha0⟩
      exact (hd0 a0).trans (Finset.le_sup' d ha0)
    · rw [Finset.sup'_lt_iff]
      intro a _ha
      exact hd1 a
    · intro δ hδ hδ1 a
      exact hdP a δ ((Finset.le_sup' d (Finset.mem_univ a)).trans_lt hδ) hδ1
  · refine ⟨0, le_rfl, zero_lt_one, ?_⟩
    intro _δ _hδ _hδ1 a
    exact False.elim (hne ⟨a, Finset.mem_univ a⟩)

/-- For any fixed cycle and start phase, the discounted continuation payoff of
the periodic path is close to the cycle average when `δ` is close enough to
one from below. -/
theorem exists_discountFactor_threshold_periodic_continuation_close_cycleAverage
    (G : KernelGame ι) [Finite G.Outcome] {n : ℕ} [NeZero n]
    (cycle : Fin n → Profile G) (start : ℕ) (who : ι)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 ≤ δ₀ ∧ δ₀ < 1 ∧
      ∀ δ : ℝ, δ₀ < δ → δ < 1 →
        |G.discountedContinuationPayoff δ (fun t => cycle (Fin.ofNat n t)) start who -
          G.cycleAveragePayoff cycle who| < ε := by
  obtain ⟨δ₀, hδ₀0, hδ₀1, hδ₀⟩ :=
    exists_discountFactor_threshold_weighted_cycle_average
      (fun j : Fin n => G.eu (cycle (Fin.ofNat n (start + j))) who) hε
  refine ⟨δ₀, hδ₀0, hδ₀1, ?_⟩
  intro δ hδgt hδlt
  have hδnonneg : 0 ≤ δ := le_of_lt (hδ₀0.trans_lt hδgt)
  have hclose := hδ₀ δ hδgt hδlt
  have hsumrot :
      (∑ j : Fin n, G.eu (cycle (Fin.ofNat n (start + j))) who) =
        ∑ j : Fin n, G.eu (cycle j) who :=
    sum_fin_rotate start (fun j : Fin n => G.eu (cycle j) who)
  rw [hsumrot] at hclose
  rw [G.discountedContinuationPayoff_periodicPath_eq hδnonneg hδlt]
  simpa [cycleAveragePayoff] using hclose

/-- The periodic continuation closeness threshold can be chosen uniformly over
all players and all start periods. -/
theorem exists_discountFactor_threshold_periodic_all_continuations_close_cycleAverage
    (G : KernelGame ι) [Finite ι] [Finite G.Outcome] {n : ℕ} [NeZero n]
    (cycle : Fin n → Profile G) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 ≤ δ₀ ∧ δ₀ < 1 ∧
      ∀ δ : ℝ, δ₀ < δ → δ < 1 → ∀ (who : ι) (start : ℕ),
        |G.discountedContinuationPayoff δ (fun t => cycle (Fin.ofNat n t)) start who -
          G.cycleAveragePayoff cycle who| < ε := by
  let α := ι × Fin n
  have hα : ∀ a : α, ∃ δ₀ : ℝ, 0 ≤ δ₀ ∧ δ₀ < 1 ∧
      ∀ δ : ℝ, δ₀ < δ → δ < 1 →
        |G.discountedContinuationPayoff δ (fun t => cycle (Fin.ofNat n t)) (a.2 : ℕ) a.1 -
          G.cycleAveragePayoff cycle a.1| < ε := by
    intro a
    exact G.exists_discountFactor_threshold_periodic_continuation_close_cycleAverage
      cycle (a.2 : ℕ) a.1 hε
  obtain ⟨δ₀, hδ₀0, hδ₀1, hδ₀⟩ :=
    exists_common_discountFactor_threshold_of_finite hα
  refine ⟨δ₀, hδ₀0, hδ₀1, ?_⟩
  intro δ hδgt hδlt who start
  have hphase := hδ₀ δ hδgt hδlt (who, Fin.ofNat n start)
  have hstart :
      G.discountedContinuationPayoff δ (fun t => cycle (Fin.ofNat n t)) start who =
        G.discountedContinuationPayoff δ
          (fun t => cycle (Fin.ofNat n t)) ((Fin.ofNat n start).val) who := by
    simp only [discountedContinuationPayoff]
    congr 1
    apply tsum_congr
    intro k
    congr 2
    ext
    simp [Fin.ofNat, Nat.add_mod]
  rw [hstart]
  exact hphase


end KernelGame

end GameTheory
