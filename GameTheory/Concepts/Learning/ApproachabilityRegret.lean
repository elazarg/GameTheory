/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Learning.Approachability
import Mathlib.Analysis.InnerProductSpace.PiL2
import Math.Probability

/-!
# Approachability ⇒ no external regret (the nonpositive orthant)

The loop-closer between Blackwell approachability (`Approachability`) and the no-regret learning of
Tier A: external-regret minimization is exactly approachability of the **nonpositive orthant** in
`ℝ^ι`. A learner's average regret vector approaches the orthant iff its external regret against
every fixed action vanishes.

## Main results

* `orthantProj` / `infDist_eq_norm_sub_orthantProj` — the orthant projection (clamp at `0`) and the
  fact that it realises the distance to the orthant, with displacement `(x)₊`.
* `regretPayoff` / `regretMatch` — the external-regret vector and the regret-matching strategy
  (play `∝ (x)₊`).
* `regretMatch_steering` — the orthant is a **B-set** for the regret payoff (the steering inner
  product vanishes).
* `regretMatch_approaches` — regret matching drives the average external-regret vector to the
  orthant against any environment sequence: no external regret, obtained geometrically.
-/

namespace Math.Approachability

variable {ι : Type*}

/-- The nonpositive orthant `{x : ‖x i ≤ 0 for all i}` in `ℝ^ι`. Approaching it is exactly having
    nonpositive external regret against every coordinate. -/
def nonposOrthant : Set (EuclideanSpace ℝ ι) := {x | ∀ i, x.ofLp i ≤ 0}

theorem mem_nonposOrthant {x : EuclideanSpace ℝ ι} :
    x ∈ nonposOrthant ↔ ∀ i, x.ofLp i ≤ 0 := Iff.rfl

theorem nonposOrthant_nonempty : (nonposOrthant (ι := ι)).Nonempty :=
  ⟨0, fun i => by simp⟩

theorem isClosed_nonposOrthant : IsClosed (nonposOrthant (ι := ι)) := by
  have hset : (nonposOrthant (ι := ι)) = ⋂ i, {x : EuclideanSpace ℝ ι | x.ofLp i ≤ 0} := by
    ext x; simp [nonposOrthant, Set.mem_iInter]
  rw [hset]
  refine isClosed_iInter (fun i => ?_)
  have hc : Continuous (fun x : EuclideanSpace ℝ ι => x.ofLp i) := by
    simpa [EuclideanSpace.coe_proj] using (EuclideanSpace.proj (𝕜 := ℝ) i).continuous
  exact isClosed_le hc continuous_const

/-! ### The orthant projection -/

/-- Projection onto the nonpositive orthant: clamp each coordinate at `0`. -/
noncomputable def orthantProj (x : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => min (x.ofLp i) 0)

@[simp] theorem orthantProj_ofLp (x : EuclideanSpace ℝ ι) (i : ι) :
    (orthantProj x).ofLp i = min (x.ofLp i) 0 := rfl

theorem orthantProj_mem (x : EuclideanSpace ℝ ι) : orthantProj x ∈ nonposOrthant :=
  fun i => by rw [orthantProj_ofLp]; exact min_le_right _ _

/-- The displacement from the projection is the coordinatewise positive part `(x)₊`. -/
theorem sub_orthantProj_ofLp (x : EuclideanSpace ℝ ι) (i : ι) :
    (x - orthantProj x).ofLp i = max (x.ofLp i) 0 := by
  rw [WithLp.ofLp_sub, Pi.sub_apply, orthantProj_ofLp]
  rcases le_total (x.ofLp i) 0 with h | h
  · rw [min_eq_left h, max_eq_right h, sub_self]
  · rw [min_eq_right h, max_eq_left h, sub_zero]

variable [Fintype ι]

/-- The squared Euclidean norm as a coordinate sum. -/
theorem norm_sq_eq_sum (z : EuclideanSpace ℝ ι) : ‖z‖ ^ 2 = ∑ i, (z.ofLp i) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  simp [Real.norm_eq_abs, sq_abs]

/-- `orthantProj x` is the nearest point of the orthant to `x`: the distance to the orthant is
    realised by clamping at `0`. -/
theorem infDist_eq_norm_sub_orthantProj (x : EuclideanSpace ℝ ι) :
    Metric.infDist x nonposOrthant = ‖x - orthantProj x‖ := by
  refine le_antisymm ?_ ?_
  · rw [← dist_eq_norm]
    exact Metric.infDist_le_dist_of_mem (orthantProj_mem x)
  · rw [Metric.le_infDist nonposOrthant_nonempty]
    intro y hy
    rw [dist_eq_norm]
    have hsq : ‖x - orthantProj x‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
      rw [norm_sq_eq_sum, norm_sq_eq_sum]
      refine Finset.sum_le_sum (fun i _ => ?_)
      have hyi : y.ofLp i ≤ 0 := hy i
      rw [sub_orthantProj_ofLp, WithLp.ofLp_sub, Pi.sub_apply]
      rcases le_total (x.ofLp i) 0 with h | h
      · rw [max_eq_right h]; nlinarith [sq_nonneg (x.ofLp i - y.ofLp i)]
      · rw [max_eq_left h]; nlinarith [hyi, h]
    nlinarith [hsq, norm_nonneg (x - orthantProj x), norm_nonneg (x - y)]

/-- Clamping at `0` is nonexpansive: `‖orthantProj z‖ ≤ ‖z‖`. -/
theorem norm_orthantProj_le (z : EuclideanSpace ℝ ι) : ‖orthantProj z‖ ≤ ‖z‖ := by
  have h : ‖orthantProj z‖ ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [norm_sq_eq_sum, norm_sq_eq_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [orthantProj_ofLp]
    rcases le_total (z.ofLp i) 0 with h | h
    · simp [min_eq_left h]
    · rw [min_eq_right h]; nlinarith [sq_nonneg (z.ofLp i)]
  nlinarith [h, norm_nonneg (orthantProj z), norm_nonneg z]

/-! ### The regret payoff and regret-matching witness -/

open Math.Probability

variable {Q : Type*}

/-- The (mixed) external-regret payoff vector against environment action `q`: coordinate `i` is the
    regret `u i q − 𝔼_{a∼p}[u a q]` of not having committed to action `i`. -/
noncomputable def regretPayoff (u : ι → Q → ℝ) (p : PMF ι) (q : Q) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => u i q - expect p (fun a => u a q))

omit [Fintype ι] in
@[simp] theorem regretPayoff_ofLp (u : ι → Q → ℝ) (p : PMF ι) (q : Q) (i : ι) :
    (regretPayoff u p q).ofLp i = u i q - expect p (fun a => u a q) := rfl

open Classical in
/-- **Regret matching** (Hart–Mas-Colell): play proportionally to the positive part `(x)₊` of the
    cumulative-regret vector `x`. On the orthant (`(x)₊ = 0`) the value is irrelevant — the steering
    inner product is taken against `(x)₊` — so it falls back to an arbitrary action. -/
noncomputable def regretMatch [Nonempty ι] (x : EuclideanSpace ℝ ι) : PMF ι :=
  if h : 0 < ∑ i, max (x.ofLp i) 0 then
    PMF.ofFintype (fun i => ENNReal.ofReal (max (x.ofLp i) 0 / ∑ j, max (x.ofLp j) 0))
      (by
        have hnn : ∀ i, (0 : ℝ) ≤ max (x.ofLp i) 0 / ∑ j, max (x.ofLp j) 0 :=
          fun i => div_nonneg (le_max_right _ _) (Finset.sum_nonneg fun j _ => le_max_right _ _)
        rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hnn i), ← Finset.sum_div, div_self h.ne',
          ENNReal.ofReal_one])
  else PMF.pure (Classical.arbitrary ι)

/-- Under regret matching with a positive cumulative regret, the expected utility is the
    `(x)₊`-weighted average of the per-action utilities. -/
theorem expect_regretMatch_pos [Nonempty ι] {x : EuclideanSpace ℝ ι}
    (h : 0 < ∑ i, max (x.ofLp i) 0) (g : ι → ℝ) :
    expect (regretMatch x) g = (∑ i, max (x.ofLp i) 0 * g i) / ∑ i, max (x.ofLp i) 0 := by
  rw [expect_eq_sum, regretMatch, dif_pos h, Finset.sum_div]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [PMF.ofFintype_apply, ENNReal.toReal_ofReal
    (div_nonneg (le_max_right _ _) (Finset.sum_nonneg fun j _ => le_max_right _ _))]
  ring

/-- **The nonpositive orthant is a B-set for the regret payoff.** Regret matching keeps the expected
    regret vector on the far side of the supporting hyperplane through the projection: the steering
    inner product vanishes. This is the Blackwell condition that makes external regret vanish. -/
theorem regretMatch_steering [Nonempty ι] (u : ι → Q → ℝ) (x : EuclideanSpace ℝ ι) (q : Q) :
    inner ℝ (regretPayoff u (regretMatch x) q - orthantProj x) (x - orthantProj x) ≤ 0 := by
  have hmaxmin : ∀ i, max (x.ofLp i) 0 * min (x.ofLp i) 0 = 0 := fun i => by
    rcases le_total (x.ofLp i) 0 with h | h
    · rw [max_eq_right h, zero_mul]
    · rw [min_eq_right h, mul_zero]
  have key : inner ℝ (regretPayoff u (regretMatch x) q - orthantProj x) (x - orthantProj x)
      = (∑ i, max (x.ofLp i) 0 * u i q)
        - expect (regretMatch x) (fun a => u a q) * (∑ i, max (x.ofLp i) 0) := by
    rw [PiLp.inner_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, WithLp.ofLp_sub, Pi.sub_apply,
      regretPayoff_ofLp, orthantProj_ofLp, sub_orthantProj_ofLp]
    linear_combination -(hmaxmin i)
  rw [key]
  rcases eq_or_lt_of_le (Finset.sum_nonneg fun i _ => le_max_right (x.ofLp i) 0) with hz | hz
  · -- ∑ (x)₊ = 0: every positive part is zero, both terms vanish
    have hall : ∀ i, max (x.ofLp i) 0 = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg fun j _ => le_max_right _ _).1 hz.symm i (Finset.mem_univ i)
    have hsq : (∑ i, max (x.ofLp i) 0 * u i q) = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [hall i, zero_mul]
    rw [hsq, ← hz]; simp
  · -- ∑ (x)₊ > 0: regret matching makes the average regret exactly zero
    rw [expect_regretMatch_pos hz, div_mul_cancel₀ _ hz.ne']
    simp

/-! ### No external regret via approachability -/

open Filter in
/-- **Regret matching achieves no external regret.** Playing regret matching against any sequence of
    environment actions drives the average external-regret vector to the nonpositive orthant: the
    realised average regret against every fixed action vanishes. This is the loop-closer — the
    learning guarantee of Tier A obtained from Blackwell approachability (`regretMatch_steering` is
    the B-set condition; `infDist_avg_tendsto_zero` turns it into convergence). The payoff bound `M`
    is finite since `regretPayoff` is bounded whenever the utilities are. -/
theorem regretMatch_approaches [Nonempty ι] (u : ι → Q → ℝ) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ p q, ‖regretPayoff u p q‖ ≤ M) (qseq : ℕ → Q) :
    Tendsto (fun t => Metric.infDist (avgVec (regretPayoff u) regretMatch qseq t) nonposOrthant)
      atTop (nhds 0) := by
  refine infDist_avg_tendsto_zero (C := 2 * M) (avgVec_succ (regretPayoff u) regretMatch qseq)
    (fun t => ?_)
  refine ⟨orthantProj (avgVec (regretPayoff u) regretMatch qseq t), orthantProj_mem _,
    (infDist_eq_norm_sub_orthantProj _).symm, regretMatch_steering u _ (qseq t), ?_⟩
  set z := avgVec (regretPayoff u) regretMatch qseq t with hz_def
  have hz : ‖z‖ ≤ M := avgVec_norm_le (regretPayoff u) regretMatch qseq hM0 hM t
  calc ‖regretPayoff u (regretMatch z) (qseq t) - orthantProj z‖
      ≤ ‖regretPayoff u (regretMatch z) (qseq t)‖ + ‖orthantProj z‖ := norm_sub_le _ _
    _ ≤ M + ‖z‖ := add_le_add (hM _ _) (norm_orthantProj_le z)
    _ ≤ 2 * M := by linarith

end Math.Approachability
