/-
# Blackwell approachability

The squared-distance argument behind Blackwell approachability, stated from
steering and bounded-residual hypotheses.

Primary reference: D. Blackwell, “An Analog of the Minimax Theorem for Vector
Payoffs,” *Pacific Journal of Mathematics* 6 (1956).
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Topology.MetricSpace.HausdorffDistance

namespace GameTheory.Math.Approachability

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A Cesàro recursion with a nearest-point steering condition has the usual
quadratic distance bound. -/
theorem sq_infDist_avg_le {S : Set E} {g avg : ℕ → E} {C : ℝ}
    (havg : ∀ t : ℕ, ((t : ℝ) + 1) • avg (t + 1) = (t : ℝ) • avg t + g t)
    (hπ : ∀ t : ℕ, ∃ π ∈ S, ‖avg t - π‖ = Metric.infDist (avg t) S ∧
      inner ℝ (g t - π) (avg t - π) ≤ 0 ∧ ‖g t - π‖ ≤ C) :
    ∀ t : ℕ, (t : ℝ) ^ 2 * Metric.infDist (avg t) S ^ 2 ≤ (t : ℝ) * C ^ 2 := by
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
    obtain ⟨π, hπS, hπeq, hsteer, hbnd⟩ := hπ t
    have hrec : ((t : ℝ) + 1) • (avg (t + 1) - π) =
        (t : ℝ) • (avg t - π) + (g t - π) := by
      have h := havg t
      rw [smul_sub, smul_sub, h, add_smul, one_smul]
      abel
    have hexp : ((t : ℝ) + 1) ^ 2 * ‖avg (t + 1) - π‖ ^ 2 =
        (t : ℝ) ^ 2 * ‖avg t - π‖ ^ 2
          + 2 * (t : ℝ) * inner ℝ (avg t - π) (g t - π) + ‖g t - π‖ ^ 2 := by
      have hl : ‖((t : ℝ) + 1) • (avg (t + 1) - π)‖ ^ 2 =
          ((t : ℝ) + 1) ^ 2 * ‖avg (t + 1) - π‖ ^ 2 := by
        rw [norm_smul, mul_pow, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [← hl, hrec, norm_add_sq_real, norm_smul, mul_pow, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (t : ℝ)), real_inner_smul_left]
      ring
    have hsteer' : inner ℝ (avg t - π) (g t - π) ≤ 0 := by
      rw [real_inner_comm]
      exact hsteer
    have hgC : ‖g t - π‖ ^ 2 ≤ C ^ 2 := by
      have hnonneg : (0 : ℝ) ≤ ‖g t - π‖ := norm_nonneg _
      nlinarith [hbnd, hnonneg]
    have hinf : Metric.infDist (avg (t + 1)) S ≤ ‖avg (t + 1) - π‖ := by
      rw [← dist_eq_norm]
      exact Metric.infDist_le_dist_of_mem hπS
    have hinf0 : (0 : ℝ) ≤ Metric.infDist (avg (t + 1)) S := Metric.infDist_nonneg
    have hsqinf : Metric.infDist (avg (t + 1)) S ^ 2 ≤ ‖avg (t + 1) - π‖ ^ 2 := by
      nlinarith [hinf, hinf0, norm_nonneg (avg (t + 1) - π)]
    rw [← hπeq] at ih
    have hcross : 2 * (t : ℝ) * inner ℝ (avg t - π) (g t - π) ≤ 0 := by
      have h2t : (0 : ℝ) ≤ 2 * (t : ℝ) := by positivity
      nlinarith [h2t, hsteer']
    push_cast
    nlinarith [hexp, hgC, hsqinf, ih, hcross, sq_nonneg ((t : ℝ) + 1)]

open Filter in
/-- The squared-distance estimate implies convergence to the target set. -/
theorem infDist_avg_tendsto_zero {S : Set E} {g avg : ℕ → E} {C : ℝ}
    (havg : ∀ t : ℕ, ((t : ℝ) + 1) • avg (t + 1) = (t : ℝ) • avg t + g t)
    (hπ : ∀ t : ℕ, ∃ π ∈ S, ‖avg t - π‖ = Metric.infDist (avg t) S ∧
      inner ℝ (g t - π) (avg t - π) ≤ 0 ∧ ‖g t - π‖ ≤ C) :
    Tendsto (fun t => Metric.infDist (avg t) S) atTop (nhds 0) := by
  have hbd := sq_infDist_avg_le havg hπ
  have hsq : Tendsto (fun n : ℕ => Metric.infDist (avg n) S ^ 2) atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (tendsto_const_div_atTop_nhds_zero_nat (C ^ 2)) ?_ ?_
    · exact Eventually.of_forall fun _ => sq_nonneg _
    · filter_upwards [eventually_gt_atTop 0] with n hn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      rw [le_div_iff₀ hnpos]
      nlinarith [hbd n, hnpos]
  have hs := hsq.sqrt
  rw [Real.sqrt_zero] at hs
  refine hs.congr fun n => ?_
  exact Real.sqrt_sq Metric.infDist_nonneg

variable {P Q : Type*}

/-- Running average when the approacher reacts to the current average. -/
noncomputable def avgVec (payoff : P → Q → E) (br : E → P) (qseq : ℕ → Q) : ℕ → E
  | 0 => 0
  | n + 1 => ((n : ℝ) / ((n : ℝ) + 1)) • avgVec payoff br qseq n
      + (1 / ((n : ℝ) + 1)) • payoff (br (avgVec payoff br qseq n)) (qseq n)

/-- The reactive average satisfies the Cesàro recursion. -/
theorem avgVec_succ (payoff : P → Q → E) (br : E → P) (qseq : ℕ → Q) (n : ℕ) :
    ((n : ℝ) + 1) • avgVec payoff br qseq (n + 1) =
      (n : ℝ) • avgVec payoff br qseq n + payoff (br (avgVec payoff br qseq n)) (qseq n) := by
  have c1 : ((n : ℝ) + 1) * ((n : ℝ) / ((n : ℝ) + 1)) = (n : ℝ) := by field_simp
  have c2 : ((n : ℝ) + 1) * (1 / ((n : ℝ) + 1)) = 1 := by field_simp
  simp only [avgVec]
  rw [smul_add, smul_smul, smul_smul, c1, c2, one_smul]

/-- The reactive Cesaro recurrence is exactly the uniform average of the
payoffs it generated.  This is the bridge from one-step regret vectors to a
cumulative regret statement. -/
theorem avgVec_smul_eq_sum (payoff : P → Q → E) (br : E → P)
    (qseq : ℕ → Q) (t : ℕ) :
    (t : ℝ) • avgVec payoff br qseq t =
      ∑ n ∈ Finset.range t,
        payoff (br (avgVec payoff br qseq n)) (qseq n) := by
  induction t with
  | zero => simp [avgVec]
  | succ n ih =>
      rw [Finset.sum_range_succ, ← ih]
      simpa only [Nat.cast_add, Nat.cast_one] using
        avgVec_succ payoff br qseq n

/-- A reactive average of uniformly bounded payoffs remains in the same ball. -/
theorem avgVec_norm_le (payoff : P → Q → E) (br : E → P) (qseq : ℕ → Q)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ p q, ‖payoff p q‖ ≤ M) :
    ∀ t, ‖avgVec payoff br qseq t‖ ≤ M := by
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
    have key : ‖avgVec payoff br qseq (n + 1)‖ ≤
        (n : ℝ) / ((n : ℝ) + 1) * M + 1 / ((n : ℝ) + 1) * M := by
      rw [avgVec]
      refine le_trans hb ?_
      gcongr
      all_goals first | exact ih | exact hM _ _
    nlinarith [key, hsum, hM0]

/-! ## Blackwell responses -/

/-- Blackwell's B-set condition yields one average-dependent response whose
nearest-point witnesses satisfy the steering and residual bounds for every
opponent sequence. -/
theorem exists_blackwell_response [ProperSpace E]
    (payoff : P → Q → E) (S : Set E) (s₀ : E) (hs₀ : s₀ ∈ S)
    (hScl : IsClosed S) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ p q, ‖payoff p q‖ ≤ M)
    (hBset : ∀ x : E, ∀ π ∈ S, ‖x - π‖ = Metric.infDist x S →
      ∃ p : P, ∀ q : Q, inner ℝ (payoff p q - π) (x - π) ≤ 0) :
    ∃ br : E → P, ∀ qseq : ℕ → Q, ∀ t : ℕ,
      ∃ π ∈ S,
        ‖avgVec payoff br qseq t - π‖ =
          Metric.infDist (avgVec payoff br qseq t) S ∧
        inner ℝ (payoff (br (avgVec payoff br qseq t)) (qseq t) - π)
          (avgVec payoff br qseq t - π) ≤ 0 ∧
        ‖payoff (br (avgVec payoff br qseq t)) (qseq t) - π‖ ≤
          3 * M + ‖s₀‖ := by
  choose npt hnptS hnptDist using fun x => hScl.exists_infDist_eq_dist ⟨s₀, hs₀⟩ x
  have hdist : ∀ x, ‖x - npt x‖ = Metric.infDist x S := fun x => by
    rw [← dist_eq_norm]
    exact (hnptDist x).symm
  choose br hbr using fun x => hBset x (npt x) (hnptS x) (hdist x)
  refine ⟨br, fun qseq t => ?_⟩
  refine ⟨npt (avgVec payoff br qseq t), hnptS _, hdist _, hbr _ (qseq t), ?_⟩
  set x := avgVec payoff br qseq t with hx_def
  have hx : ‖x‖ ≤ M := avgVec_norm_le payoff br qseq hM0 hM t
  have hnpt_le : ‖npt x‖ ≤ 2 * M + ‖s₀‖ := by
    have hd : Metric.infDist x S ≤ ‖x‖ + ‖s₀‖ :=
      calc
        Metric.infDist x S ≤ dist x s₀ := Metric.infDist_le_dist_of_mem hs₀
        _ = ‖x - s₀‖ := dist_eq_norm _ _
        _ ≤ ‖x‖ + ‖s₀‖ := norm_sub_le _ _
    have h2 : ‖npt x‖ ≤ ‖x‖ + ‖x - npt x‖ :=
      calc
        ‖npt x‖ = ‖x - (x - npt x)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖x‖ + ‖x - npt x‖ := norm_sub_le _ _
    rw [hdist x] at h2
    linarith
  calc
    ‖payoff (br x) (qseq t) - npt x‖ ≤ ‖payoff (br x) (qseq t)‖ + ‖npt x‖ :=
      norm_sub_le _ _
    _ ≤ M + (2 * M + ‖s₀‖) := add_le_add (hM _ _) hnpt_le
    _ = 3 * M + ‖s₀‖ := by ring

/-- Finite-time squared-distance bound for the stationary response selected by
Blackwell's B-set condition. -/
theorem blackwell_sq_infDist_avg_le [ProperSpace E]
    (payoff : P → Q → E) (S : Set E) (s₀ : E) (hs₀ : s₀ ∈ S)
    (hScl : IsClosed S) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ p q, ‖payoff p q‖ ≤ M)
    (hBset : ∀ x : E, ∀ π ∈ S, ‖x - π‖ = Metric.infDist x S →
      ∃ p : P, ∀ q : Q, inner ℝ (payoff p q - π) (x - π) ≤ 0) :
    ∃ br : E → P, ∀ qseq : ℕ → Q, ∀ t : ℕ,
      (t : ℝ) ^ 2 * Metric.infDist (avgVec payoff br qseq t) S ^ 2 ≤
        (t : ℝ) * (3 * M + ‖s₀‖) ^ 2 := by
  obtain ⟨br, hbr⟩ := exists_blackwell_response payoff S s₀ hs₀ hScl hM0 hM hBset
  refine ⟨br, fun qseq => ?_⟩
  exact sq_infDist_avg_le (avgVec_succ payoff br qseq) (hbr qseq)

open Filter in
/-- Blackwell's B-set condition yields one stationary average-dependent
response whose payoff average approaches the closed target against every
opponent sequence. -/
theorem blackwell_approaches [ProperSpace E] (payoff : P → Q → E) (S : Set E)
    (hScl : IsClosed S) (hSne : S.Nonempty) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ p q, ‖payoff p q‖ ≤ M)
    (hBset : ∀ x : E, ∀ π ∈ S, ‖x - π‖ = Metric.infDist x S →
      ∃ p : P, ∀ q : Q, inner ℝ (payoff p q - π) (x - π) ≤ 0) :
    ∃ br : E → P, ∀ qseq : ℕ → Q,
      Tendsto (fun t => Metric.infDist (avgVec payoff br qseq t) S)
        atTop (nhds 0) := by
  obtain ⟨s₀, hs₀⟩ := hSne
  obtain ⟨br, hbr⟩ := exists_blackwell_response payoff S s₀ hs₀ hScl hM0 hM hBset
  refine ⟨br, fun qseq => ?_⟩
  exact infDist_avg_tendsto_zero (avgVec_succ payoff br qseq) (hbr qseq)

end GameTheory.Math.Approachability
