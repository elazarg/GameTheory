module

/-
# The rural hospitals theorem

Finite responsive markets have a doctor-optimal stable assignment obtained
from deferred acceptance on hospital slots. Stable slot lifts transfer the
one-to-one unmatched-agent theorem to doctors and hospital headcounts.
At an undersubscribed hospital, every doctor assigned there in the optimal
outcome would block a vacancy if absent from another stable outcome. Equal
finite headcounts therefore give equality of the entire doctor cohorts.
-/

public import GameTheory.Cooperative.Matching.SortedLift
public import GameTheory.Cooperative.GaleShapley.Unmatched

@[expose] public section

noncomputable section

namespace GameTheory.CapacitatedMarket

open MatchingMarket

universe uDoctor uHospital

variable {Doctor : Type uDoctor} {Hospital : Type uHospital}
    [Fintype Doctor] [Fintype Hospital] (market : CapacitatedMarket Doctor Hospital)

/-- Left-proposing deferred acceptance on ordered hospital positions,
projected to the native optional-hospital assignment. -/
def deferredAcceptance (linear : market.rankings.HasLinearPreferences) : Matching Doctor Hospital :=
  market.collapse (market.slotMarket.deferredAcceptance (market.slotMarket_linear linear))

/-- The native deferred-acceptance assignment is stable and respects quotas. -/
theorem deferredAcceptance_isStable (linear : market.rankings.HasLinearPreferences) :
    market.IsStable (market.deferredAcceptance linear) :=
  market.slot_stable_collapse
    (market.slotMarket.deferredAcceptance_isStable (market.slotMarket_linear linear))

/-- Every doctor weakly prefers native deferred acceptance to every other
stable assignment. Artificial priorities between slots disappear on projection. -/
theorem deferredAcceptance_doctorOptimal (linear : market.rankings.HasLinearPreferences)
    {assignment : Matching Doctor Hospital} (stable : market.IsStable assignment)
    (doctor : Doctor) :
    market.rankings.prefersLeft doctor (market.deferredAcceptance linear doctor)
      (assignment doctor) := by
  obtain ⟨lift, liftStable, collapses⟩ := market.exists_stable_slot_lift linear stable
  have optimal := market.slotMarket.deferredAcceptance_proposerOptimal
    (market.slotMarket_linear linear) liftStable doctor
  have projected := optimal.1
  change market.rankings.prefersLeft doctor (market.deferredAcceptance linear doctor)
    (market.collapse lift doctor) at projected
  rwa [collapses] at projected

/-- Exactly the same doctors remain unmatched in every stable assignment,
without balancedness or complete-acceptability assumptions. -/
theorem stable_unmatched_doctor_iff (linear : market.rankings.HasLinearPreferences)
    {first second : Matching Doctor Hospital}
    (stableFirst : market.IsStable first) (stableSecond : market.IsStable second)
    (doctor : Doctor) :
    first doctor = none ↔ second doctor = none := by
  obtain ⟨firstLift, firstStable, firstCollapse⟩ :=
    market.exists_stable_slot_lift linear stableFirst
  obtain ⟨secondLift, secondStable, secondCollapse⟩ :=
    market.exists_stable_slot_lift linear stableSecond
  rw [← firstCollapse, ← secondCollapse, collapse_none_iff, collapse_none_iff]
  exact market.slotMarket.stable_unmatched_left_iff (market.slotMarket_linear linear)
    firstStable secondStable doctor

/-- Every hospital employs the same number of doctors in all stable outcomes. -/
theorem stable_cohort_encard_eq (linear : market.rankings.HasLinearPreferences)
    {first second : Matching Doctor Hospital}
    (stableFirst : market.IsStable first) (stableSecond : market.IsStable second)
    (hospital : Hospital) : (cohort first hospital).encard = (cohort second hospital).encard := by
  obtain ⟨firstLift, firstStable, firstCollapse⟩ :=
    market.exists_stable_slot_lift linear stableFirst
  obtain ⟨secondLift, secondStable, secondCollapse⟩ :=
    market.exists_stable_slot_lift linear stableSecond
  have occupiedEqual :
      market.occupied firstLift hospital = market.occupied secondLift hospital := by
    ext index
    have unmatched := market.slotMarket.stable_unmatched_right_iff
      (market.slotMarket_linear linear) firstStable secondStable ⟨hospital, index⟩
    simpa only [occupied, Set.mem_ofPred_eq, not_forall, not_not] using not_congr unmatched
  rw [← firstCollapse, ← secondCollapse,
    market.cohort_encard_eq_occupied firstStable.isMatching hospital,
    market.cohort_encard_eq_occupied secondStable.isMatching hospital, occupiedEqual]

private theorem optimal_cohort_eq_of_underfilled
    (linear : market.rankings.HasLinearPreferences)
    {assignment : Matching Doctor Hospital} (stable : market.IsStable assignment)
    (hospital : Hospital)
    (vacancy : (cohort assignment hospital).encard < (market.capacity hospital : ℕ∞)) :
    cohort (market.deferredAcceptance linear) hospital = cohort assignment hospital := by
  have optimalStable := market.deferredAcceptance_isStable linear
  have subset :
      cohort (market.deferredAcceptance linear) hospital ⊆ cohort assignment hospital := by
    intro doctor assigned
    by_contra absent
    have weak := market.deferredAcceptance_doctorOptimal linear stable doctor
    change market.deferredAcceptance linear doctor = some hospital at assigned
    rw [assigned] at weak
    have doctorStrict : Preference.strict market.rankings.prefersLeft doctor
        (some hospital) (assignment doctor) :=
      Rank.strict_of_le_of_ne (linear.left doctor).2.2.2 weak (by
        intro same
        exact absent same.symm)
    have rational := optimalStable.2.1 doctor hospital assigned
    have acceptable : Preference.strict market.rankings.prefersRight hospital (some doctor) none :=
      Rank.strict_of_le_of_ne (linear.right hospital).2.2.2 rational.2 (by simp)
    exact stable.2.2 ⟨doctor, hospital, doctorStrict, Or.inl ⟨vacancy, acceptable⟩⟩
  have counts := market.stable_cohort_encard_eq linear optimalStable stable hospital
  exact (optimalStable.1.finite_cohort hospital).eq_of_subset_of_encard_le subset counts.symm.le

/-- A hospital below quota has exactly the same doctor cohort in every stable
assignment. This is equality of sets, rather than only equality of headcounts. -/
theorem stable_underfilled_cohort_eq (linear : market.rankings.HasLinearPreferences)
    {first second : Matching Doctor Hospital}
    (stableFirst : market.IsStable first) (stableSecond : market.IsStable second)
    (hospital : Hospital)
    (vacancy : (cohort first hospital).encard < (market.capacity hospital : ℕ∞)) :
    cohort first hospital = cohort second hospital := by
  have secondVacancy : (cohort second hospital).encard < (market.capacity hospital : ℕ∞) := by
    rw [← market.stable_cohort_encard_eq linear stableFirst stableSecond hospital]
    exact vacancy
  exact (market.optimal_cohort_eq_of_underfilled linear stableFirst hospital vacancy).symm.trans
    (market.optimal_cohort_eq_of_underfilled linear stableSecond hospital secondVacancy)

/-- The full finite rural hospitals theorem for strict individual rankings and
responsive hospital behavior: unmatched doctors, hospital headcounts, and the
exact cohorts of undersubscribed hospitals are invariant across stable outcomes. -/
theorem ruralHospitals (linear : market.rankings.HasLinearPreferences)
    {first second : Matching Doctor Hospital}
    (stableFirst : market.IsStable first) (stableSecond : market.IsStable second) :
    (∀ doctor, first doctor = none ↔ second doctor = none) ∧
      (∀ hospital, (cohort first hospital).encard = (cohort second hospital).encard) ∧
      (∀ hospital, (cohort first hospital).encard < (market.capacity hospital : ℕ∞) →
        cohort first hospital = cohort second hospital) :=
  ⟨market.stable_unmatched_doctor_iff linear stableFirst stableSecond,
    market.stable_cohort_encard_eq linear stableFirst stableSecond,
    market.stable_underfilled_cohort_eq linear stableFirst stableSecond⟩

/-- Unit quotas make projected hospital-slot DA equal ordinary one-to-one DA.
Both assignments are stable and doctor-optimal, so antisymmetry fixes every
doctor's optional partner without any slot relabeling in the statement. -/
theorem deferredAcceptance_eq_oneToOne (linear : market.rankings.HasLinearPreferences)
    (unitCapacity : ∀ hospital, market.capacity hospital = 1) :
    market.deferredAcceptance linear = market.rankings.deferredAcceptance linear := by
  cases market with
  | mk rankings capacity =>
      have same : capacity = fun _ => 1 := funext unitCapacity
      subst capacity
      funext doctor
      exact (linear.left doctor).2.2.2 _ _
        ((rankings.withCapacities (fun _ => 1)).deferredAcceptance_doctorOptimal linear
          (rankings.deferredAcceptance_isStable linear) doctor)
        (rankings.deferredAcceptance_proposerOptimal linear
          ((rankings.withCapacities (fun _ => 1)).deferredAcceptance_isStable linear) doctor)

end GameTheory.CapacitatedMarket
