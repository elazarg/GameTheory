module

/-
# A nonempty undersubscribed hospital across distinct stable outcomes

Two unit-capacity hospitals exchange their doctors between stable outcomes.
A third hospital has two places but employs only doctor two in both outcomes;
doctor three prefers remaining unmatched and is rejected by every hospital.
An unstable assignment with equal hospital headcounts has a different cohort,
so headcount comparisons alone cannot establish the full rural-hospitals claim.
-/

public import GameTheory.Experimental.Exp168.Capacitated
public import GameTheory.Cooperative.GaleShapley
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace GameTheory.Experimental.Exp168.Controls

open GameTheory.MatchingMarket (Matching)
open Capacitated Capacitated.Market

abbrev Doctor := Fin 4
abbrev Hospital := Fin 3

private def doctorScore (doctor : Doctor) : Option Hospital → ℕ
  | none => if doctor = 3 then 4 else if doctor = 2 then 3 else 2
  | some hospital => match doctor.val, hospital.val with
    | 0, 0 => 4
    | 0, 1 => 3
    | 0, _ => 1
    | 1, 0 => 3
    | 1, 1 => 4
    | 1, _ => 1
    | 2, 0 => 2
    | 2, 1 => 1
    | 2, _ => 4
    | _, 0 => 3
    | _, 1 => 2
    | _, _ => 1

private def hospitalScore (hospital : Hospital) : Option Doctor → ℕ
  | none => if hospital = 2 then 3 else 2
  | some doctor => match hospital.val, doctor.val with
    | 0, 0 => 4
    | 0, 1 => 5
    | 0, 2 => 1
    | 0, _ => 0
    | 1, 0 => 5
    | 1, 1 => 4
    | 1, 2 => 1
    | 1, _ => 0
    | _, 0 => 2
    | _, 1 => 1
    | _, 2 => 4
    | _, _ => 0

/-- Strict individual rankings; doctors two and three are excluded from the
first two hospitals' acceptable cohorts. -/
def rankings : MatchingMarket Doctor Hospital := by
  exact {
    prefersLeft doctor first second := doctorScore doctor second ≤ doctorScore doctor first
    prefersRight hospital first second :=
      hospitalScore hospital second ≤ hospitalScore hospital first }

private theorem linear_of_score {α : Type*} (score : α → ℕ)
    (injective : Function.Injective score) :
    Rank.Linear (fun first second => score second ≤ score first) :=
  ⟨fun _ => le_rfl, fun _ _ _ first second => second.trans first,
    fun _ _ => le_total _ _, fun _ _ first second => injective (le_antisymm second first)⟩

theorem rankings_linear : rankings.HasLinearPreferences := by
  constructor
  · intro doctor
    apply linear_of_score
    intro first second equal
    fin_cases doctor <;> fin_cases first <;> fin_cases second <;> simp_all [doctorScore]
  · intro hospital
    apply linear_of_score
    intro first second equal
    fin_cases hospital <;> fin_cases first <;> fin_cases second <;> simp_all [hospitalScore]

/-- Two unit quotas and one genuine two-place hospital. -/
def market : Capacitated.Market Doctor Hospital where
  rankings := rankings
  capacity hospital := if hospital = 2 then 2 else 1

def diagonal : Matching Doctor Hospital := fun doctor => match doctor.val with
  | 0 => some 0
  | 1 => some 1
  | 2 => some 2
  | _ => none

def crossed : Matching Doctor Hospital := fun doctor => match doctor.val with
  | 0 => some 1
  | 1 => some 0
  | 2 => some 2
  | _ => none

theorem diagonal_cohorts :
    cohort diagonal 0 = {0} ∧ cohort diagonal 1 = {1} ∧ cohort diagonal 2 = {2} := by
  constructor
  · ext doctor
    fin_cases doctor <;> norm_num [cohort, diagonal]
  · constructor <;> ext doctor <;> fin_cases doctor <;> norm_num [cohort, diagonal]

theorem crossed_cohorts :
    cohort crossed 0 = {1} ∧ cohort crossed 1 = {0} ∧ cohort crossed 2 = {2} := by
  constructor
  · ext doctor
    fin_cases doctor <;> norm_num [cohort, crossed]
  · constructor <;> ext doctor <;> fin_cases doctor <;> norm_num [cohort, crossed]

theorem diagonal_feasible : market.IsFeasible diagonal := by
  intro hospital
  fin_cases hospital <;>
    norm_num [market, diagonal_cohorts.1, diagonal_cohorts.2.1, diagonal_cohorts.2.2]

theorem crossed_feasible : market.IsFeasible crossed := by
  intro hospital
  fin_cases hospital <;>
    norm_num [market, crossed_cohorts.1, crossed_cohorts.2.1, crossed_cohorts.2.2]

theorem diagonal_stable : market.IsStable diagonal := by
  refine ⟨diagonal_feasible, ?_, ?_⟩
  · intro doctor hospital paired
    fin_cases doctor <;> fin_cases hospital <;>
      norm_num [diagonal] at paired <;> norm_num [market, rankings, doctorScore, hospitalScore]
  · rintro ⟨doctor, hospital, blocks⟩
    have reverse := blocks.1.2
    fin_cases doctor <;> fin_cases hospital <;>
      norm_num [market, rankings, diagonal, doctorScore] at reverse

theorem crossed_stable : market.IsStable crossed := by
  refine ⟨crossed_feasible, ?_, ?_⟩
  · intro doctor hospital paired
    fin_cases doctor <;> fin_cases hospital <;>
      norm_num [crossed] at paired <;> norm_num [market, rankings, doctorScore, hospitalScore]
  · rintro ⟨doctor, hospital, blocks⟩
    fin_cases doctor <;> fin_cases hospital <;>
      norm_num [Capacitated.Market.IsBlockingPair, Preference.strict, Rank.strict,
        market, rankings, crossed, doctorScore, hospitalScore,
        crossed_cohorts.1, crossed_cohorts.2.1, crossed_cohorts.2.2] at blocks

theorem stable_outcomes_distinct : diagonal ≠ crossed := by
  intro equal
  have value := congrFun equal 0
  norm_num [diagonal, crossed] at value

theorem unmatched_doctor_in_both : diagonal 3 = none ∧ crossed 3 = none := ⟨rfl, rfl⟩

/-- Both doctors in the changing component strictly prefer the diagonal. -/
theorem first_doctors_prefer_diagonal :
    Preference.strict rankings.prefersLeft 0 (diagonal 0) (crossed 0) ∧
      Preference.strict rankings.prefersLeft 1 (diagonal 1) (crossed 1) := by
  norm_num [Preference.strict, Rank.strict, rankings, doctorScore, diagonal, crossed]

/-- Both hospitals in the changing component strictly prefer the crossed cohort. -/
theorem first_hospitals_prefer_crossed :
    Preference.strict rankings.prefersRight 0 (some 1) (some 0) ∧
      Preference.strict rankings.prefersRight 1 (some 0) (some 1) := by
  norm_num [Preference.strict, Rank.strict, rankings, hospitalScore]

/-- The unmatched doctor prefers the outside option, and every hospital
strictly rejects that doctor. -/
theorem unmatched_doctor_unacceptable (hospital : Hospital) :
    Preference.strict rankings.prefersLeft 3 none (some hospital) ∧
      Preference.strict rankings.prefersRight hospital none (some 3) := by
  fin_cases hospital <;>
    norm_num [Preference.strict, Rank.strict, rankings, doctorScore, hospitalScore]

/-- The undersubscribed hospital employs the same nonempty exact cohort. -/
theorem underfilled_exact_cohort :
    cohort diagonal 2 = ({2} : Set Doctor) ∧ cohort crossed 2 = ({2} : Set Doctor) ∧
      (cohort diagonal 2).Nonempty ∧
      (cohort diagonal 2).encard < (market.capacity 2 : ℕ∞) ∧
      (cohort crossed 2).encard < (market.capacity 2 : ℕ∞) := by
  norm_num [diagonal_cohorts.2.2, crossed_cohorts.2.2, market]

/-- An assignment with the same hospital headcounts but the wrong third doctor. -/
def wrongCohort : Matching Doctor Hospital := fun doctor => match doctor.val with
  | 0 => some 0
  | 1 => some 1
  | 2 => none
  | _ => some 2

theorem wrong_cohorts :
    cohort wrongCohort 0 = {0} ∧ cohort wrongCohort 1 = {1} ∧
      cohort wrongCohort 2 = {3} := by
  constructor
  · ext doctor
    fin_cases doctor <;> norm_num [cohort, wrongCohort]
  · constructor <;> ext doctor <;> fin_cases doctor <;> norm_num [cohort, wrongCohort]

/-- Equal headcounts do not identify a hospital's cohort without stability. -/
theorem equal_counts_different_cohort :
    (∀ hospital, (cohort diagonal hospital).encard = (cohort wrongCohort hospital).encard) ∧
      cohort diagonal 2 ≠ cohort wrongCohort 2 := by
  constructor
  · intro hospital
    fin_cases hospital <;>
      norm_num [diagonal_cohorts.1, diagonal_cohorts.2.1, diagonal_cohorts.2.2,
        wrong_cohorts.1, wrong_cohorts.2.1, wrong_cohorts.2.2]
  · rw [diagonal_cohorts.2.2, wrong_cohorts.2.2]
    intro equal
    have member : (2 : Doctor) ∈ ({3} : Set Doctor) := by
      rw [← equal]
      exact Set.mem_singleton _
    norm_num at member

/-- The equal-headcount control violates individual rationality. -/
theorem wrong_cohort_not_stable : ¬ market.IsStable wrongCohort := by
  intro stable
  have rational := stable.2.1 3 2 rfl
  norm_num [market, rankings, doctorScore, hospitalScore] at rational

end GameTheory.Experimental.Exp168.Controls
