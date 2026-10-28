module

/-
# Equal headcounts with a genuine blocking pair

Two feasible, individually rational assignments employ one doctor at each
hospital. One is stable; the other changes the nonempty cohort of a hospital
with two places. A doctor and that hospital block through its vacancy, so the
failure is stability rather than capacity or individual rationality.
-/

public import GameTheory.Cooperative.Matching.RuralHospitals
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace GameTheory.Tests.RuralHospitalsBlocking

open GameTheory.MatchingMarket

private def score (favorite : Bool) : Option Bool → ℕ
  | none => 0
  | some partner => if partner = favorite then 2 else 1

/-- Each agent prefers its namesake partner; every partner is acceptable. -/
def rankings : MatchingMarket Bool Bool where
  prefersLeft doctor first second := score doctor second ≤ score doctor first
  prefersRight hospital first second := score hospital second ≤ score hospital first

private theorem score_linear (favorite : Bool) :
    Rank.Linear (fun first second => score favorite second ≤ score favorite first) := by
  refine ⟨fun _ => le_rfl, fun _ _ _ first second => second.trans first,
    fun _ _ => le_total _ _, ?_⟩
  intro first second forward reverse
  cases favorite <;> fin_cases first <;> fin_cases second <;> simp_all [score]

theorem rankings_linear : rankings.HasLinearPreferences :=
  ⟨score_linear, score_linear⟩

/-- Hospital `false` has a genuine spare place in both assignments. -/
def market : CapacitatedMarket Bool Bool where
  rankings := rankings
  capacity hospital := if hospital then 1 else 2

def correct : Matching Bool Bool := some

def swapped : Matching Bool Bool := fun doctor => some (!doctor)

theorem correct_cohorts (hospital : Bool) : cohort correct hospital = {hospital} := by
  ext doctor
  simp [cohort, correct]

theorem swapped_cohorts (hospital : Bool) : cohort swapped hospital = {!hospital} := by
  ext doctor
  cases doctor <;> cases hospital <;> simp [cohort, swapped]

theorem correct_feasible : market.IsFeasible correct := by
  intro hospital
  cases hospital <;> norm_num [correct_cohorts, market]

theorem swapped_feasible : market.IsFeasible swapped := by
  intro hospital
  cases hospital <;> norm_num [swapped_cohorts, market]

theorem correct_rational : rankings.IsIndividuallyRational correct := by
  intro doctor hospital _
  cases doctor <;> cases hospital <;> norm_num [rankings, score]

theorem swapped_rational : rankings.IsIndividuallyRational swapped := by
  intro doctor hospital _
  cases doctor <;> cases hospital <;> norm_num [rankings, score]

theorem correct_stable : market.IsStable correct := by
  refine ⟨correct_feasible, correct_rational, ?_⟩
  rintro ⟨doctor, hospital, blocks⟩
  have reverse := blocks.1.2
  cases doctor <;> cases hospital <;> norm_num [market, rankings, correct, score] at reverse

/-- The wrong assignment has the very same hospital headcounts. -/
theorem equal_headcounts (hospital : Bool) :
    (cohort correct hospital).encard = (cohort swapped hospital).encard := by
  simp [correct_cohorts, swapped_cohorts]

/-- Nevertheless, its nonempty, undersubscribed hospital employs a different doctor. -/
theorem nonempty_underfilled_different_cohorts :
    (cohort correct false).Nonempty ∧ (cohort swapped false).Nonempty ∧
      (cohort correct false).encard < (market.capacity false : ℕ∞) ∧
      (cohort swapped false).encard < (market.capacity false : ℕ∞) ∧
      cohort correct false ≠ cohort swapped false := by
  norm_num [correct_cohorts, swapped_cohorts, market]

/-- Doctor `false` wants its favorite hospital, which accepts it into the
vacant second place. No rejection of an unacceptable incumbent is involved. -/
theorem swapped_has_blocking_pair : market.IsBlockingPair swapped false false := by
  refine ⟨?_, Or.inl ⟨?_, ?_⟩⟩
  · norm_num [Preference.strict, Rank.strict, market, rankings, swapped, score]
  · norm_num [swapped_cohorts, market]
  · norm_num [Preference.strict, Rank.strict, market, rankings, score]

theorem swapped_not_stable : ¬ market.IsStable swapped :=
  fun stable => stable.not_isBlockingPair false false swapped_has_blocking_pair

/-- The rural hospitals theorem pins down this nonempty exact cohort for
every stable assignment, so equal counts alone cannot replace stability. -/
theorem every_stable_cohort {assignment : Matching Bool Bool}
    (stable : market.IsStable assignment) : cohort assignment false = {false} := by
  rw [← market.stable_underfilled_cohort_eq rankings_linear correct_stable stable false
    nonempty_underfilled_different_cohorts.2.2.1]
  exact correct_cohorts false

end GameTheory.Tests.RuralHospitalsBlocking
