/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Blackwell approachability — the squared-distance core

The analytic heart of Blackwell's approachability theorem, stated game-free in a real inner
product space. Given a sequence of payoff vectors `g` whose running averages `avg` satisfy the
**steering condition** at each step — the new payoff lies on the far side of the supporting
hyperplane through the nearest point of the current average in the target set `S` — the average
approaches `S` at rate `O(1/√t)`.

This is the engine of `B-set ⇒ approachable`: a game strategy realizing the Blackwell condition
supplies the steering hypothesis, and this lemma converts it into convergence to `S`.

## Main results

* `Math.Approachability.sq_infDist_avg_le` — `t² · d(avg t, S)² ≤ t · C²` (telescoped potential)
* `Math.Approachability.infDist_avg_tendsto_zero` — hence `d(avg t, S) → 0`
-/

namespace Math.Approachability

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Squared-distance potential bound.** If the running averages `avg` satisfy the Cesàro recursion
    `(t+1) • avg (t+1) = t • avg t + g t` and, at each step `t`, the steering condition against a
    nearest point `π` of `avg t` in `S` (`⟪g t − π, avg t − π⟫ ≤ 0`) with the residual bounded
    (`‖g t − π‖ ≤ C`), then `t² · d(avg t, S)² ≤ t · C²`. -/
theorem sq_infDist_avg_le {S : Set E} {g avg : ℕ → E} {C : ℝ}
    (havg : ∀ t : ℕ, ((t : ℝ) + 1) • avg (t + 1) = (t : ℝ) • avg t + g t)
    (hπ : ∀ t : ℕ, ∃ π ∈ S, ‖avg t - π‖ = Metric.infDist (avg t) S ∧
            inner ℝ (g t - π) (avg t - π) ≤ 0 ∧ ‖g t - π‖ ≤ C) :
    ∀ t : ℕ, ((t : ℝ)) ^ 2 * (Metric.infDist (avg t) S) ^ 2 ≤ (t : ℝ) * C ^ 2 := by
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
    obtain ⟨π, hπS, hπeq, hsteer, hbnd⟩ := hπ t
    -- rewrite the deviation of the new average from π via the recursion
    have hrec : ((t : ℝ) + 1) • (avg (t + 1) - π) = (t : ℝ) • (avg t - π) + (g t - π) := by
      have h := havg t
      rw [smul_sub, smul_sub, h, add_smul, one_smul]
      abel
    -- expand the squared norm
    have hexp : ((t : ℝ) + 1) ^ 2 * ‖avg (t + 1) - π‖ ^ 2
        = (t : ℝ) ^ 2 * ‖avg t - π‖ ^ 2
          + 2 * (t : ℝ) * inner ℝ (avg t - π) (g t - π) + ‖g t - π‖ ^ 2 := by
      have hl : ‖((t : ℝ) + 1) • (avg (t + 1) - π)‖ ^ 2
          = ((t : ℝ) + 1) ^ 2 * ‖avg (t + 1) - π‖ ^ 2 := by
        rw [norm_smul, mul_pow, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [← hl, hrec, norm_add_sq_real, norm_smul, mul_pow, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ (t : ℝ)), real_inner_smul_left]
      ring
    -- the cross term is nonpositive and the residual is bounded by C
    have hsteer' : inner ℝ (avg t - π) (g t - π) ≤ 0 := by
      rw [real_inner_comm]; exact hsteer
    have hgC : ‖g t - π‖ ^ 2 ≤ C ^ 2 := by
      have : (0:ℝ) ≤ ‖g t - π‖ := norm_nonneg _
      nlinarith [hbnd, this]
    -- distance to S at the new average is ≤ ‖avg (t+1) - π‖
    have hinf : Metric.infDist (avg (t + 1)) S ≤ ‖avg (t + 1) - π‖ := by
      rw [← dist_eq_norm]; exact Metric.infDist_le_dist_of_mem hπS
    have hinf0 : (0:ℝ) ≤ Metric.infDist (avg (t + 1)) S := Metric.infDist_nonneg
    have hsqinf : (Metric.infDist (avg (t + 1)) S) ^ 2 ≤ ‖avg (t + 1) - π‖ ^ 2 := by
      nlinarith [hinf, hinf0, norm_nonneg (avg (t + 1) - π)]
    -- φ t = ↑t² ‖avg t - π‖²
    rw [← hπeq] at ih
    -- assemble: φ(t+1) ≤ φ t + C² ≤ ↑t C² + C² = ↑(t+1) C²
    have hcross : 2 * (t : ℝ) * inner ℝ (avg t - π) (g t - π) ≤ 0 := by
      have h2t : (0 : ℝ) ≤ 2 * (t : ℝ) := by positivity
      nlinarith [h2t, hsteer']
    push_cast
    nlinarith [hexp, hgC, hsqinf, ih, hcross, sq_nonneg ((t : ℝ) + 1)]

open Filter in
/-- **Approachability.** Under the same steering and bound hypotheses, the average payoff converges
    to the target set: `d(avg t, S) → 0`. (Immediate from `sq_infDist_avg_le`, since
    `d(avg t, S)² ≤ C²/t → 0`.) -/
theorem infDist_avg_tendsto_zero {S : Set E} {g avg : ℕ → E} {C : ℝ}
    (havg : ∀ t : ℕ, ((t : ℝ) + 1) • avg (t + 1) = (t : ℝ) • avg t + g t)
    (hπ : ∀ t : ℕ, ∃ π ∈ S, ‖avg t - π‖ = Metric.infDist (avg t) S ∧
            inner ℝ (g t - π) (avg t - π) ≤ 0 ∧ ‖g t - π‖ ≤ C) :
    Tendsto (fun t => Metric.infDist (avg t) S) atTop (nhds 0) := by
  have hbd := sq_infDist_avg_le havg hπ
  -- the squared distance is squeezed between 0 and C²/t → 0
  have hsq : Tendsto (fun n : ℕ => (Metric.infDist (avg n) S) ^ 2) atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (tendsto_const_div_atTop_nhds_zero_nat (C ^ 2)) ?_ ?_
    · exact Eventually.of_forall (fun n => sq_nonneg _)
    · filter_upwards [eventually_gt_atTop 0] with n hn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      rw [le_div_iff₀ hnpos]
      nlinarith [hbd n, hnpos]
  -- d(avg t, S) = √(d² ) → √0 = 0
  have hs := hsq.sqrt
  rw [Real.sqrt_zero] at hs
  refine hs.congr (fun n => ?_)
  exact Real.sqrt_sq Metric.infDist_nonneg

/-! ### The reactive-strategy average -/

variable {P Q : Type*}

/-- The running average of the payoffs produced when the approacher reacts to the current average
    via the (stationary) response map `br` and the opponent plays the sequence `qseq`. -/
noncomputable def avgVec (payoff : P → Q → E) (br : E → P) (qseq : ℕ → Q) : ℕ → E
  | 0 => 0
  | (n + 1) => ((n : ℝ) / ((n : ℝ) + 1)) • avgVec payoff br qseq n
      + (1 / ((n : ℝ) + 1)) • payoff (br (avgVec payoff br qseq n)) (qseq n)

/-- The reactive average satisfies the Cesàro recursion required by `sq_infDist_avg_le`. -/
theorem avgVec_succ (payoff : P → Q → E) (br : E → P) (qseq : ℕ → Q) (n : ℕ) :
    ((n : ℝ) + 1) • avgVec payoff br qseq (n + 1)
      = (n : ℝ) • avgVec payoff br qseq n + payoff (br (avgVec payoff br qseq n)) (qseq n) := by
  have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
  have c1 : ((n : ℝ) + 1) * ((n : ℝ) / ((n : ℝ) + 1)) = (n : ℝ) := by field_simp
  have c2 : ((n : ℝ) + 1) * (1 / ((n : ℝ) + 1)) = 1 := by field_simp
  simp only [avgVec]
  rw [smul_add, smul_smul, smul_smul, c1, c2, one_smul]

/-- The reactive average stays inside the payoff ball: `‖avg t‖ ≤ M`. -/
theorem avgVec_norm_le (payoff : P → Q → E) (br : E → P) (qseq : ℕ → Q) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ p q, ‖payoff p q‖ ≤ M) : ∀ t, ‖avgVec payoff br qseq t‖ ≤ M := by
  intro t
  induction t with
  | zero => simpa [avgVec] using hM0
  | succ n ih =>
    have hc1 : (0 : ℝ) ≤ (n : ℝ) / ((n : ℝ) + 1) := by positivity
    have hc2 : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
    have hsum : (n : ℝ) / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) = 1 := by field_simp
    have hb := norm_add_le (((n : ℝ) / ((n : ℝ) + 1)) • avgVec payoff br qseq n)
      ((1 / ((n : ℝ) + 1)) • payoff (br (avgVec payoff br qseq n)) (qseq n))
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hc1,
      abs_of_nonneg hc2] at hb
    have key : ‖avgVec payoff br qseq (n + 1)‖
        ≤ (n : ℝ) / ((n : ℝ) + 1) * M + 1 / ((n : ℝ) + 1) * M := by
      rw [avgVec]
      refine le_trans hb ?_
      gcongr
      all_goals first | exact ih | exact hM _ _
    nlinarith [key, hsum, hM0]

open Filter in
/-- **Blackwell's approachability theorem (B-set ⇒ approachable).** In a proper inner product space,
    if `S` is closed and nonempty, payoffs are bounded by `M`, and `S` is a **B-set** — for every
    `x` and nearest point `π` of `x` in `S` the approacher has an action `p` keeping
    `⟪payoff p q − π, x − π⟫ ≤ 0` against every opponent action `q` — then the approacher has a
    (stationary, average-dependent) strategy `br` whose induced average payoff converges to `S`
    against *any* opponent sequence. The witness for the steering hypothesis is read off the B-set
    condition each round; the residual is bounded using `‖avg t‖ ≤ M`. -/
theorem blackwell_approaches [ProperSpace E] (payoff : P → Q → E) (S : Set E)
    (hScl : IsClosed S) (hSne : S.Nonempty) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ p q, ‖payoff p q‖ ≤ M)
    (hBset : ∀ x : E, ∀ π ∈ S, ‖x - π‖ = Metric.infDist x S →
        ∃ p : P, ∀ q : Q, inner ℝ (payoff p q - π) (x - π) ≤ 0)
    (qseq : ℕ → Q) :
    ∃ br : E → P, Tendsto (fun t => Metric.infDist (avgVec payoff br qseq t) S) atTop (nhds 0) := by
  obtain ⟨s₀, hs₀⟩ := hSne
  choose npt hnptS hnptDist using fun x => hScl.exists_infDist_eq_dist ⟨s₀, hs₀⟩ x
  have hdist : ∀ x, ‖x - npt x‖ = Metric.infDist x S := fun x => by
    rw [← dist_eq_norm]; exact (hnptDist x).symm
  choose br hbr using fun x => hBset x (npt x) (hnptS x) (hdist x)
  refine ⟨br, infDist_avg_tendsto_zero (C := 3 * M + ‖s₀‖) (avgVec_succ payoff br qseq)
    (fun t => ?_)⟩
  refine ⟨npt (avgVec payoff br qseq t), hnptS _, hdist _, hbr _ (qseq t), ?_⟩
  -- residual bound: ‖payoff − π‖ ≤ 3M + ‖s₀‖, uniform in t
  set x := avgVec payoff br qseq t with hx_def
  have hx : ‖x‖ ≤ M := avgVec_norm_le payoff br qseq hM0 hM t
  have hnpt_le : ‖npt x‖ ≤ 2 * M + ‖s₀‖ := by
    have hd : Metric.infDist x S ≤ ‖x‖ + ‖s₀‖ :=
      calc Metric.infDist x S ≤ dist x s₀ := Metric.infDist_le_dist_of_mem hs₀
        _ = ‖x - s₀‖ := dist_eq_norm _ _
        _ ≤ ‖x‖ + ‖s₀‖ := norm_sub_le _ _
    have h2 : ‖npt x‖ ≤ ‖x‖ + ‖x - npt x‖ :=
      calc ‖npt x‖ = ‖x - (x - npt x)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖x‖ + ‖x - npt x‖ := norm_sub_le _ _
    rw [hdist x] at h2
    linarith
  calc ‖payoff (br x) (qseq t) - npt x‖
      ≤ ‖payoff (br x) (qseq t)‖ + ‖npt x‖ := norm_sub_le _ _
    _ ≤ M + (2 * M + ‖s₀‖) := add_le_add (hM _ _) hnpt_le
    _ = 3 * M + ‖s₀‖ := by ring

end Math.Approachability
