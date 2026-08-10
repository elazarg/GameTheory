/-
# Hostile regret-matching fixture

Two actions face an alternating environment.  The score vector produces a
genuinely nonuniform law, and the two environment states induce different
regret vectors before the general approachability theorem is specialized.
-/

import GameTheory.Analysis.Approachability

noncomputable section

namespace GameTheory.Analysis.ApproachabilityTest

open Filter GameTheory.Probability GameTheory.Analysis.Approachability
open GameTheoryMath.Approachability

/-- Action zero is better in the first environment state; action one is better
in the second. -/
def utility (action : Fin 2) (environment : Bool) : ℝ :=
  if environment then
    if action = 0 then 0 else 2
  else
    if action = 0 then 1 else 0

/-- Positive regret weights one and three force a nonuniform mixed action. -/
def score : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 fun action => if action = 0 then 1 else 3

private theorem score_positive :
    0 < ∑ action, max (score.ofLp action) 0 := by
  rw [Fin.sum_univ_two]
  norm_num [score]

theorem regretMatch_score_prob_zero :
    (regretMatch score).prob 0 = 1 / 4 := by
  rw [regretMatch, dif_pos score_positive, FinDist.prob_ofWeights]
  rw [Fin.sum_univ_two]
  norm_num [score]

theorem regretMatch_score_prob_one :
    (regretMatch score).prob 1 = 3 / 4 := by
  rw [regretMatch, dif_pos score_positive, FinDist.prob_ofWeights]
  rw [Fin.sum_univ_two]
  norm_num [score]

theorem regretPayoff_false_zero :
    (regretPayoff utility (regretMatch score) false).ofLp 0 = 3 / 4 := by
  rw [regretPayoff_ofLp, FinDist.expect_eq_sum, Fin.sum_univ_two]
  rw [regretMatch_score_prob_zero, regretMatch_score_prob_one]
  norm_num [utility]

theorem regretPayoff_true_one :
    (regretPayoff utility (regretMatch score) true).ofLp 1 = 1 / 2 := by
  rw [regretPayoff_ofLp, FinDist.expect_eq_sum, Fin.sum_univ_two]
  rw [regretMatch_score_prob_zero, regretMatch_score_prob_one]
  norm_num [utility]

theorem score_steers (environment : Bool) :
    inner ℝ
      (regretPayoff utility (regretMatch score) environment - orthantProj score)
      (score - orthantProj score) ≤ 0 :=
  regretMatch_steering utility score environment

theorem regretPayoff_norm_le (p : FinDist (Fin 2)) (environment : Bool) :
    ‖regretPayoff utility p environment‖ ≤ 6 := by
  have hexpect : |p.expect fun action => utility action environment| ≤ 2 :=
    p.abs_expect_le_of_abs_bound (fun action => utility action environment) fun action _ => by
      fin_cases action <;> cases environment <;> norm_num [utility]
  have hcoord : ∀ action, |(regretPayoff utility p environment).ofLp action| ≤ 4 := by
    intro action
    rw [regretPayoff_ofLp]
    have hutility : |utility action environment| ≤ 2 := by
      fin_cases action <;> cases environment <;> norm_num [utility]
    exact (abs_sub _ _).trans (by linarith)
  have hsq : ‖regretPayoff utility p environment‖ ^ 2 ≤ 32 := by
    rw [norm_sq_eq_sum, Fin.sum_univ_two]
    have hzero := hcoord 0
    have hone := hcoord 1
    rw [abs_le] at hzero hone
    nlinarith [sq_nonneg ((regretPayoff utility p environment).ofLp 0),
      sq_nonneg ((regretPayoff utility p environment).ofLp 1)]
  nlinarith [hsq, norm_nonneg (regretPayoff utility p environment)]

/-- A changing environment, so the convergence consumer is not a stationary
or point-mass special case. -/
def alternatingEnvironment (t : ℕ) : Bool := t % 2 == 0

theorem alternating_regretMatch_approaches :
    Tendsto
      (fun t => Metric.infDist
        (avgVec (regretPayoff utility) regretMatch alternatingEnvironment t)
        (nonposOrthant (ι := Fin 2)))
      atTop (nhds 0) :=
  regretMatch_approaches utility (M := 6) (by norm_num) regretPayoff_norm_le
    alternatingEnvironment

/-! A falsifying fixture: boundedness alone does not make an arbitrary
response approach an arbitrary closed target. -/

def constantPayoff (_ : Unit) (_ : Unit) : ℝ := 1

def constantResponse (_ : ℝ) : Unit := ()

@[simp]
theorem constantPayoff_avg_succ (n : ℕ) :
    avgVec constantPayoff constantResponse (fun _ => ()) (n + 1) = 1 := by
  induction n with
  | zero => simp [avgVec, constantPayoff]
  | succ n ih =>
      rw [avgVec]
      rw [ih]
      simp [constantPayoff]
      field_simp

/-- The constant-payoff response stays a unit distance from the singleton
target, so it supplies a concrete negative convergence check. -/
theorem constantPayoff_does_not_approach_zero :
    ¬ Tendsto
      (fun t => Metric.infDist
        (avgVec constantPayoff constantResponse (fun _ => ()) t) ({0} : Set ℝ))
      atTop (nhds 0) := by
  intro hzero
  have hone :
      Tendsto
        (fun t => Metric.infDist
          (avgVec constantPayoff constantResponse (fun _ => ()) t) ({0} : Set ℝ))
        atTop (nhds 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with t ht
    cases t with
    | zero => omega
    | succ n => simp [Metric.infDist_singleton, constantPayoff_avg_succ]
  have : (1 : ℝ) = 0 := tendsto_nhds_unique hone hzero
  norm_num at this

end GameTheory.Analysis.ApproachabilityTest
