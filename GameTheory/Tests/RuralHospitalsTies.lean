module

/-
# Ties invalidate the rural hospitals conclusions under weak stability

One doctor is indifferent between two acceptable hospitals. Hospital rankings
are strict, and no agent is indifferent between a partner and the outside
option. Two feasible assignments are stable under the existing blocking rule,
which requires strict improvement on both sides. Nevertheless their unmatched
doctors, hospital headcounts, and the cohort of an undersubscribed hospital
differ. These are weakly stable outcomes; no strong or super stability claim
is made.
-/

public import GameTheory.Cooperative.Matching.Capacitated
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace GameTheory.Tests.RuralHospitalsTies

open MatchingMarket

private def doctorScore (doctor : Bool) : Option Bool → ℕ
  | none => if doctor then 2 else 1
  | some hospital => if doctor then (if hospital then 1 else 3) else 2

private def hospitalScore (hospital : Bool) : Option Bool → ℕ
  | none => if hospital then 2 else 1
  | some doctor => if doctor then (if hospital then 1 else 2) else 3

/-- Only doctor false ties its two acceptable partners; all quotas are one. -/
def market : CapacitatedMarket Bool Bool where
  rankings :=
    { prefersLeft doctor first second := doctorScore doctor second ≤ doctorScore doctor first
      prefersRight hospital first second :=
        hospitalScore hospital second ≤ hospitalScore hospital first }
  capacity _ := 1

theorem doctor_rankings_reflexive : Preference.Reflexive market.rankings.prefersLeft := by
  intro doctor alternative
  exact le_rfl

theorem doctor_rankings_transitive : Preference.Transitive market.rankings.prefersLeft := by
  intro doctor first middle last firstMiddle middleLast
  exact middleLast.trans firstMiddle

theorem doctor_rankings_total : Preference.Total market.rankings.prefersLeft := by
  intro doctor first second
  exact le_total _ _

/-- The other doctor has a strict linear ranking. -/
theorem doctor_true_linear : Rank.Linear (market.rankings.prefersLeft true) := by
  refine ⟨doctor_rankings_reflexive true, doctor_rankings_transitive true,
    doctor_rankings_total true, ?_⟩
  intro first second forward reverse
  have equal := le_antisymm reverse forward
  fin_cases first <;> fin_cases second <;> simp_all [market, doctorScore]

/-- Every hospital has a strict linear ranking, including its outside option. -/
theorem hospital_rankings_linear : Preference.Linear market.rankings.prefersRight := by
  intro hospital
  refine ⟨fun _ => le_rfl, fun _ _ _ first second => second.trans first,
    fun _ _ => le_total _ _, ?_⟩
  intro first second forward reverse
  have equal := le_antisymm reverse forward
  cases hospital <;> fin_cases first <;> fin_cases second <;>
    simp_all [market, hospitalScore]

theorem doctor_false_indifferent :
    Rank.Indifferent (market.rankings.prefersLeft false) (some false) (some true) := by
  norm_num [Rank.Indifferent, market, doctorScore]

/-- The missing order law is antisymmetry, rather than transitivity or totality. -/
theorem doctor_rankings_not_antisymmetric :
    ¬ Preference.Antisymmetric market.rankings.prefersLeft := by
  intro antisymmetric
  have equal := antisymmetric false (some false) (some true)
    doctor_false_indifferent.1 doctor_false_indifferent.2
  cases equal

/-- No doctor or hospital is indifferent between a partner and remaining unmatched. -/
theorem no_ties_with_outside_option (doctor hospital : Bool) :
    ¬ Rank.Indifferent (market.rankings.prefersLeft doctor) (some hospital) none ∧
      ¬ Rank.Indifferent (market.rankings.prefersRight hospital) (some doctor) none := by
  cases doctor <;> cases hospital <;>
    norm_num [Rank.Indifferent, market, doctorScore, hospitalScore]

def small : Matching Bool Bool := fun doctor => if doctor then none else some false

def large : Matching Bool Bool := fun doctor => if doctor then some false else some true

theorem small_cohorts : cohort small false = {false} ∧ cohort small true = ∅ := by
  constructor <;> ext doctor <;> cases doctor <;> simp [cohort, small]

theorem large_cohorts : cohort large false = {true} ∧ cohort large true = {false} := by
  constructor <;> ext doctor <;> cases doctor <;> simp [cohort, large]

theorem small_feasible : market.IsFeasible small := by
  intro hospital
  cases hospital <;> norm_num [market, small_cohorts.1, small_cohorts.2]

theorem large_feasible : market.IsFeasible large := by
  intro hospital
  cases hospital <;> norm_num [market, large_cohorts.1, large_cohorts.2]

theorem small_valid : IsMatching small :=
  (market.isFeasible_iff_isMatching_of_unitCapacity (fun _ => rfl) small).mp small_feasible

theorem large_valid : IsMatching large :=
  (market.isFeasible_iff_isMatching_of_unitCapacity (fun _ => rfl) large).mp large_feasible

/-- Every pair in the smaller outcome strictly prefers matching to being unmatched. -/
theorem small_assigned_pairs_strictly_acceptable (doctor hospital : Bool)
    (paired : small doctor = some hospital) :
    Preference.strict market.rankings.prefersLeft doctor (some hospital) none ∧
      Preference.strict market.rankings.prefersRight hospital (some doctor) none := by
  cases doctor <;> cases hospital <;> simp [small] at paired;
    norm_num [Preference.strict, Rank.strict, market, doctorScore, hospitalScore]

/-- Every pair in the larger outcome also has strict acceptability on both sides. -/
theorem large_assigned_pairs_strictly_acceptable (doctor hospital : Bool)
    (paired : large doctor = some hospital) :
    Preference.strict market.rankings.prefersLeft doctor (some hospital) none ∧
      Preference.strict market.rankings.prefersRight hospital (some doctor) none := by
  cases doctor <;> cases hospital <;> simp [large] at paired <;>
    norm_num [Preference.strict, Rank.strict, market, doctorScore, hospitalScore]

/-- The tied partners both strictly outrank this doctor's outside option. -/
theorem doctor_false_both_acceptable :
    Preference.strict market.rankings.prefersLeft false (some false) none ∧
      Preference.strict market.rankings.prefersLeft false (some true) none :=
  ⟨(small_assigned_pairs_strictly_acceptable false false rfl).1,
    (large_assigned_pairs_strictly_acceptable false true rfl).1⟩

theorem small_individuallyRational : market.rankings.IsIndividuallyRational small := by
  intro doctor hospital paired
  have acceptable := small_assigned_pairs_strictly_acceptable doctor hospital paired
  exact ⟨acceptable.1.1, acceptable.2.1⟩

theorem large_individuallyRational : market.rankings.IsIndividuallyRational large := by
  intro doctor hospital paired
  have acceptable := large_assigned_pairs_strictly_acceptable doctor hospital paired
  exact ⟨acceptable.1.1, acceptable.2.1⟩

/-- The smaller outcome has no pair that strictly improves on both sides. -/
theorem small_stable : market.IsStable small := by
  refine ⟨small_feasible, small_individuallyRational, ?_⟩
  rintro ⟨doctor, hospital, blocks⟩
  cases doctor <;> cases hospital <;>
    norm_num [CapacitatedMarket.IsBlockingPair, Preference.strict, Rank.strict,
      market, small, doctorScore, hospitalScore, small_cohorts.1, small_cohorts.2] at blocks

/-- The larger outcome satisfies the same canonical weak-stability predicate. -/
theorem large_stable : market.IsStable large := by
  refine ⟨large_feasible, large_individuallyRational, ?_⟩
  rintro ⟨doctor, hospital, blocks⟩
  have reverse := blocks.1.2
  cases doctor <;> cases hospital <;> norm_num [market, large, doctorScore] at reverse

theorem doctor_true_unmatched_only_in_small : small true = none ∧ large true = some false :=
  ⟨rfl, rfl⟩

/-- The unmatched-doctor conclusion fails for these two stable outcomes. -/
theorem unmatched_doctor_invariance_fails :
    ¬ (∀ doctor, small doctor = none ↔ large doctor = none) := by
  intro invariant
  have impossible := (invariant true).mp rfl
  simp [large] at impossible

theorem hospital_true_headcounts :
    (cohort small true).encard = 0 ∧ (cohort large true).encard = 1 := by
  simp [small_cohorts.2, large_cohorts.2]

/-- Even individual hospital headcounts change across the stable outcomes. -/
theorem hospital_headcount_invariance_fails :
    ¬ (∀ hospital, (cohort small hospital).encard = (cohort large hospital).encard) := by
  intro invariant
  have impossible := invariant true
  simp [small_cohorts.2, large_cohorts.2] at impossible

/-- The underfilled hospital's cohort changes from empty to a singleton. -/
theorem underfilled_cohort_differs :
    (cohort small true).encard < (market.capacity true : ℕ∞) ∧
      cohort small true = ∅ ∧ cohort large true = {false} ∧
      cohort small true ≠ cohort large true := by
  simp [small_cohorts.2, large_cohorts.2, market]

/-- The exact-cohort conclusion fails as well, despite undersubscription. -/
theorem underfilled_cohort_invariance_fails :
    ¬ (∀ hospital, (cohort small hospital).encard < (market.capacity hospital : ℕ∞) →
      cohort small hospital = cohort large hospital) := by
  intro invariant
  exact underfilled_cohort_differs.2.2.2 (invariant true underfilled_cohort_differs.1)

end GameTheory.Tests.RuralHospitalsTies
