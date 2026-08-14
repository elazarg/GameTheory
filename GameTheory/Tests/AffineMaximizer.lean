/-
Hostile affine-maximizer fixture.

The mechanism has two players, unequal positive weights, a nonzero alternative
bias, report-sensitive allocation, and nonconstant Clarke payments.  Truth is
strictly better for both types of the active player, so DSIC cannot pass through
a constant objective, choice, transfer, or utility.
-/

import GameTheory.Mechanism.AffineMaximizer

noncomputable section

namespace GameTheory.Tests.AffineMaximizer

open Mechanism

@[reducible]
def affine : Mechanism.AffineMaximizer Bool Bool where
  Ty _ := Bool
  value who ownType alternative :=
    if who = false ∧ alternative = ownType then 2 else 0
  weight who := if who = false then 2 else 1
  bias alternative := if alternative then 1 / 2 else 0

def falseReports : affine.ReportProfile := fun _ => false

def trueFirstReports : affine.ReportProfile :=
  Profile.update falseReports false true

abbrev mechanism := affine.toQuasiLinearMechanism

theorem false_report_objectives :
    affine.objective falseReports false = 4 ∧
      affine.objective falseReports true = 1 / 2 := by
  norm_num [Mechanism.AffineMaximizer.objective, affine, falseReports]

theorem true_report_objectives :
    affine.objective trueFirstReports false = 0 ∧
      affine.objective trueFirstReports true = 9 / 2 := by
  norm_num [Mechanism.AffineMaximizer.objective, affine,
    trueFirstReports, falseReports]

theorem choose_falseReports : affine.choose falseReports = false := by
  have h := affine.objective_le_choose falseReports false
  cases hchoice : affine.choose falseReports
  · rfl
  · rw [hchoice] at h
    norm_num [Mechanism.AffineMaximizer.objective, affine,
      falseReports] at h

theorem choose_trueFirstReports : affine.choose trueFirstReports = true := by
  have h := affine.objective_le_choose trueFirstReports true
  cases hchoice : affine.choose trueFirstReports
  · rw [hchoice] at h
    norm_num [Mechanism.AffineMaximizer.objective, affine,
      trueFirstReports, falseReports] at h
  · rfl

theorem pivot_falseReports :
    affine.pivotObjective falseReports false = 1 / 2 := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro alternative _
    cases alternative <;>
      norm_num [Mechanism.AffineMaximizer.othersObjective, affine,
        falseReports]
  · have h := Finset.le_sup'
      (affine.othersObjective falseReports false) (Finset.mem_univ true)
    have hvalue : affine.othersObjective falseReports false true = 1 / 2 := by
      norm_num [Mechanism.AffineMaximizer.othersObjective, affine,
        falseReports]
    rw [hvalue] at h
    exact h

theorem pivot_trueFirstReports :
    affine.pivotObjective trueFirstReports false = 1 / 2 := by
  rw [show trueFirstReports = Profile.update falseReports false true from rfl,
    affine.pivotObjective_update, pivot_falseReports]

theorem payment_responds_to_report :
    mechanism.payment falseReports false = 1 / 4 ∧
      mechanism.payment trueFirstReports false = 0 := by
  simp only [mechanism, Mechanism.AffineMaximizer.toQuasiLinearMechanism]
  rw [pivot_falseReports, pivot_trueFirstReports,
    choose_falseReports, choose_trueFirstReports]
  norm_num [Mechanism.AffineMaximizer.othersObjective, affine,
    falseReports, trueFirstReports]

theorem truth_strictly_beats_deviation :
    mechanism.trueUtility falseReports false false = 7 / 4 ∧
      mechanism.trueUtility trueFirstReports false false = 0 ∧
      mechanism.trueUtility trueFirstReports false true = 2 ∧
      mechanism.trueUtility falseReports false true = -(1 / 4) := by
  have hchooseFalse : mechanism.choose falseReports = false :=
    choose_falseReports
  have hchooseTrue : mechanism.choose trueFirstReports = true :=
    choose_trueFirstReports
  simp only [Mechanism.QuasiLinearMechanism.trueUtility]
  rw [hchooseFalse, hchooseTrue,
    payment_responds_to_report.1, payment_responds_to_report.2]
  dsimp only [mechanism, Mechanism.AffineMaximizer.toQuasiLinearMechanism]
  norm_num [affine]

theorem payment_is_nonnegative : 0 ≤ mechanism.payment falseReports false :=
  affine.payment_nonneg falseReports false (by norm_num [affine])

theorem mechanism_isDSIC : mechanism.IsDSIC :=
  affine.toQuasiLinearMechanism_isDSIC (by
    intro who
    cases who <;> norm_num [affine])

theorem mechanism_isWeaklyMonotone : mechanism.IsWeaklyMonotone :=
  mechanism.weaklyMonotone_of_isDSIC mechanism_isDSIC

theorem vcg_specialization_isDSIC :
    (Mechanism.AffineMaximizer.vcgMechanism affine.Ty affine.value).IsDSIC :=
  Mechanism.AffineMaximizer.vcgMechanism_isDSIC affine.Ty affine.value

end GameTheory.Tests.AffineMaximizer
