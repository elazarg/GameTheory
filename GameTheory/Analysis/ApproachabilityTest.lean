/-
# Hostile regret-matching fixture

Two actions face an alternating environment.  The score vector produces a
genuinely nonuniform law, and the two environment states induce different
regret vectors before the general approachability theorem is specialized.
-/

import GameTheory.Analysis.Approachability

noncomputable section

namespace GameTheory.Analysis.ApproachabilityTest

open Filter GameTheory.Math.Probability GameTheory.Analysis.Approachability
open GameTheory.Math.Approachability GameTheory.Math.OrthantProjection

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
    expect (regretMatch score) (fun action => if action = 0 then 1 else 0)
      (payoffIntegrable_of_finite _ _) = 1 / 4 := by
  rw [expect_regretMatch_pos score_positive]
  rw [Fin.sum_univ_two]
  norm_num [score]

theorem regretMatch_score_prob_one :
    expect (regretMatch score) (fun action => if action = 1 then 1 else 0)
      (payoffIntegrable_of_finite _ _) = 3 / 4 := by
  rw [expect_regretMatch_pos score_positive]
  rw [Fin.sum_univ_two]
  norm_num [score]

theorem regretPayoff_false_zero :
    (regretPayoff utility (regretMatch score) false
      (payoffIntegrable_of_finite _ _)).ofLp 0 = 3 / 4 := by
  rw [regretPayoff_ofLp, expect_regretMatch_pos score_positive,
    Fin.sum_univ_two]
  norm_num [utility, score]

theorem regretPayoff_true_one :
    (regretPayoff utility (regretMatch score) true
      (payoffIntegrable_of_finite _ _)).ofLp 1 = 1 / 2 := by
  rw [regretPayoff_ofLp, expect_regretMatch_pos score_positive,
    Fin.sum_univ_two]
  norm_num [utility, score]

theorem score_steers (environment : Bool) :
    inner ℝ
      (regretPayoff utility (regretMatch score) environment
        (payoffIntegrable_of_finite _ _) - orthantProj score)
      (score - orthantProj score) ≤ 0 :=
  regretMatch_steering utility score environment

theorem regretPayoff_norm_le (p : PMF (Fin 2)) (environment : Bool) :
    ‖regretPayoff utility p environment
      (payoffIntegrable_of_finite p _)‖ ≤ 6 := by
  have hrange (action : Fin 2) (q : Bool) :
      utility action q ∈ Set.Icc (0 : ℝ) 2 := by
    fin_cases action <;> cases q <;> norm_num [utility]
  have h := regretPayoff_norm_le_card_mul_width utility hrange p environment
  norm_num at h ⊢
  linarith

/-- A changing environment, so the convergence consumer is not a stationary
or point-mass special case. -/
def alternatingEnvironment (t : ℕ) : Bool := t % 2 == 0

theorem alternating_regretMatch_approaches :
    Tendsto
      (fun t => Metric.infDist
        (avgVec (fun p q => regretPayoff utility p q
          (payoffIntegrable_of_finite p _)) regretMatch
          alternatingEnvironment t)
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
