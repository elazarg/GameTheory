/-
# External-regret matching through Blackwell approachability

This analytic bridge packages the expectation-level deterministic geometry
behind the Hart--Mas-Colell external-regret rule with the library's canonical
finite law.  The coordinates are unconditional (Hannan) regrets against fixed
actions, not action-pair conditional regrets, so this module makes no
correlated-equilibrium claim.  It also does not claim almost-sure convergence
of sampled realized regrets.  The Euclidean and Blackwell arguments remain
game-independent in `GameTheoryMath.Approachability`.

Primary reference: S. Hart and A. Mas-Colell, “A General Class of Adaptive
Strategies,” *Journal of Economic Theory* 98 (2001), 26--54.
-/

import GameTheory.Probability.FinDist
import GameTheoryMath.OrthantProjection

noncomputable section

namespace GameTheory.Analysis.Approachability

open Filter GameTheory.Probability GameTheoryMath.Approachability
  GameTheoryMath.OrthantProjection

variable {ι Q : Type*}

/-- External-regret vector against an environment action.  Coordinate `i` is
the payoff from committing to `i` minus the current law's expected payoff. -/
def regretPayoff (u : ι → Q → ℝ) (p : FinDist ι) (q : Q) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 fun i => u i q - p.expect fun a => u a q

@[simp]
theorem regretPayoff_ofLp (u : ι → Q → ℝ) (p : FinDist ι) (q : Q) (i : ι) :
    (regretPayoff u p q).ofLp i = u i q - p.expect (fun a => u a q) := rfl

variable [Fintype ι]

/-- External-regret matching: play in proportion to positive cumulative
Hannan regret, with an arbitrary pure fallback when every coordinate is
nonpositive.  This is proof semantics, not an executable selector. -/
def regretMatch [Nonempty ι] (x : EuclideanSpace ℝ ι) : FinDist ι :=
  if h : 0 < ∑ i, max (x.ofLp i) 0 then
    FinDist.ofWeights
      (fun i => max (x.ofLp i) 0 / ∑ j, max (x.ofLp j) 0)
      (fun i => div_nonneg (le_max_right _ _)
        (Finset.sum_nonneg fun j _ => le_max_right _ _))
      (by
        rw [← Finset.sum_div]
        exact div_self h.ne')
  else
    FinDist.pure (Classical.choice inferInstance)

/-- With positive total regret, regret matching takes the positive-regret
weighted average of an observable. -/
theorem expect_regretMatch_pos [Nonempty ι] {x : EuclideanSpace ℝ ι}
    (h : 0 < ∑ i, max (x.ofLp i) 0) (g : ι → ℝ) :
    (regretMatch x).expect g =
      (∑ i, max (x.ofLp i) 0 * g i) / ∑ i, max (x.ofLp i) 0 := by
  rw [FinDist.expect_eq_sum, regretMatch, dif_pos h, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [FinDist.prob_ofWeights]
  ring

/-- The nonpositive orthant is a B-set for the regret payoff: regret matching
makes the supporting-hyperplane inner product nonpositive. -/
theorem regretMatch_steering [Nonempty ι] (u : ι → Q → ℝ)
    (x : EuclideanSpace ℝ ι) (q : Q) :
    inner ℝ (regretPayoff u (regretMatch x) q - orthantProj x)
      (x - orthantProj x) ≤ 0 := by
  have hmaxmin : ∀ i, max (x.ofLp i) 0 * min (x.ofLp i) 0 = 0 := fun i => by
    rcases le_total (x.ofLp i) 0 with h | h
    · rw [max_eq_right h, zero_mul]
    · rw [min_eq_right h, mul_zero]
  have key : inner ℝ (regretPayoff u (regretMatch x) q - orthantProj x)
      (x - orthantProj x) =
      (∑ i, max (x.ofLp i) 0 * u i q) -
        (regretMatch x).expect (fun a => u a q) *
          ∑ i, max (x.ofLp i) 0 := by
    rw [PiLp.inner_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, WithLp.ofLp_sub,
      Pi.sub_apply, regretPayoff_ofLp, orthantProj_ofLp, sub_orthantProj_ofLp]
    linear_combination -(hmaxmin i)
  rw [key]
  rcases eq_or_lt_of_le (Finset.sum_nonneg fun i _ => le_max_right (x.ofLp i) 0) with hz | hz
  · have hall : ∀ i, max (x.ofLp i) 0 = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg fun j _ => le_max_right _ _).1 hz.symm
        i (Finset.mem_univ i)
    have hsum : (∑ i, max (x.ofLp i) 0 * u i q) = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [hall i, zero_mul]
    rw [hsum, ← hz]
    simp
  · rw [expect_regretMatch_pos hz, div_mul_cancel₀ _ hz.ne']
    simp

/-- Finite-time regret-matching estimate. The average regret vector has
squared distance at most `(2M)^2 / t` from the nonpositive orthant. -/
theorem regretMatch_sq_infDist_avg_le [Nonempty ι] (u : ι → Q → ℝ)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ p q, ‖regretPayoff u p q‖ ≤ M)
    (qseq : ℕ → Q) (t : ℕ) :
    Metric.infDist
        (avgVec (regretPayoff u) regretMatch qseq t) nonposOrthant ^ 2 *
      (t : ℝ) ≤ (2 * M) ^ 2 := by
  have hraw := sq_infDist_avg_le (S := nonposOrthant) (C := 2 * M)
    (avgVec_succ (regretPayoff u) regretMatch qseq) (fun n => by
      refine ⟨orthantProj (avgVec (regretPayoff u) regretMatch qseq n),
        orthantProj_mem _, (infDist_eq_norm_sub_orthantProj _).symm,
        regretMatch_steering u _ (qseq n), ?_⟩
      set current := avgVec (regretPayoff u) regretMatch qseq n
      have hcurrent : ‖current‖ ≤ M :=
        avgVec_norm_le (regretPayoff u) regretMatch qseq hM0 hM n
      calc
        ‖regretPayoff u (regretMatch current) (qseq n) -
            orthantProj current‖ ≤
          ‖regretPayoff u (regretMatch current) (qseq n)‖ +
            ‖orthantProj current‖ := norm_sub_le _ _
        _ ≤ M + ‖current‖ :=
          add_le_add (hM _ _) (norm_orthantProj_le current)
        _ ≤ 2 * M := by linarith) t
  by_cases ht : t = 0
  · subst t
    simp [sq_nonneg]
  · have htpos : (0 : ℝ) < t := by exact_mod_cast Nat.pos_of_ne_zero ht
    nlinarith [sq_nonneg
      (Metric.infDist (avgVec (regretPayoff u) regretMatch qseq t)
        nonposOrthant)]

/-- Regret matching drives the average external-regret vector to the
nonpositive orthant against every environment sequence. -/
theorem regretMatch_approaches [Nonempty ι] (u : ι → Q → ℝ)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ p q, ‖regretPayoff u p q‖ ≤ M)
    (qseq : ℕ → Q) :
    Tendsto
      (fun t => Metric.infDist
        (avgVec (regretPayoff u) regretMatch qseq t) nonposOrthant)
      atTop (nhds 0) := by
  refine infDist_avg_tendsto_zero (C := 2 * M)
    (avgVec_succ (regretPayoff u) regretMatch qseq) (fun t => ?_)
  refine ⟨orthantProj (avgVec (regretPayoff u) regretMatch qseq t),
    orthantProj_mem _, (infDist_eq_norm_sub_orthantProj _).symm,
    regretMatch_steering u _ (qseq t), ?_⟩
  set z := avgVec (regretPayoff u) regretMatch qseq t with hz_def
  have hz : ‖z‖ ≤ M := avgVec_norm_le (regretPayoff u) regretMatch qseq hM0 hM t
  calc
    ‖regretPayoff u (regretMatch z) (qseq t) - orthantProj z‖ ≤
        ‖regretPayoff u (regretMatch z) (qseq t)‖ + ‖orthantProj z‖ :=
      norm_sub_le _ _
    _ ≤ M + ‖z‖ := add_le_add (hM _ _) (norm_orthantProj_le z)
    _ ≤ 2 * M := by linarith

end GameTheory.Analysis.Approachability
