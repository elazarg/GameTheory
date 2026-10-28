module

/-
# Direct capacitated matching candidate

Doctors receive optional hospitals, while a hospital receives the fiber of
that assignment. Finite quotas bound extended cardinalities, so an infinite
cohort cannot satisfy a finite quota. Responsive blocking compares an
acceptable newcomer with a vacant place or with one incumbent.
-/

public import GameTheory.Cooperative.Matching
public import Mathlib.Data.Set.Card

@[expose] public section

namespace GameTheory.Experimental.Exp168.Capacitated

universe uDoctor uHospital

/-- Individual ordinal rankings and hospital quotas, without finiteness or
order-law assumptions stored in the market. -/
structure Market (Doctor : Type uDoctor) (Hospital : Type uHospital) where
  rankings : MatchingMarket Doctor Hospital
  capacity : Hospital → ℕ

namespace Market

variable {Doctor : Type uDoctor} {Hospital : Type uHospital}

/-- The doctors assigned to a hospital. -/
def cohort (assignment : MatchingMarket.Matching Doctor Hospital) (hospital : Hospital) :
    Set Doctor :=
  {doctor | assignment doctor = some hospital}

@[simp]
theorem mem_cohort (assignment : MatchingMarket.Matching Doctor Hospital)
    (doctor : Doctor) (hospital : Hospital) :
    doctor ∈ cohort assignment hospital ↔ assignment doctor = some hospital := Iff.rfl

/-- Every hospital's fiber fits its finite quota. -/
def IsFeasible (market : Market Doctor Hospital)
    (assignment : MatchingMarket.Matching Doctor Hospital) : Prop :=
  ∀ hospital, (cohort assignment hospital).encard ≤ (market.capacity hospital : ℕ∞)

/-- A doctor and an accepting hospital can improve by filling a vacant place
or replacing a less preferred incumbent. -/
def IsBlockingPair (market : Market Doctor Hospital)
    (assignment : MatchingMarket.Matching Doctor Hospital)
    (doctor : Doctor) (hospital : Hospital) : Prop :=
  Preference.strict market.rankings.prefersLeft doctor (some hospital) (assignment doctor) ∧
    Preference.strict market.rankings.prefersRight hospital (some doctor) none ∧
    ((cohort assignment hospital).encard < (market.capacity hospital : ℕ∞) ∨
      ∃ incumbent ∈ cohort assignment hospital,
        Preference.strict market.rankings.prefersRight hospital (some doctor) (some incumbent))

/-- Capacity feasibility, individual rationality, and no responsive blocking pair. -/
def IsStable (market : Market Doctor Hospital)
    (assignment : MatchingMarket.Matching Doctor Hospital) : Prop :=
  market.IsFeasible assignment ∧ market.rankings.IsIndividuallyRational assignment ∧
    ¬ ∃ doctor hospital, market.IsBlockingPair assignment doctor hospital

/-- Finite quotas force finite cohorts even when the doctor type is infinite. -/
theorem IsFeasible.finite_cohort {market : Market Doctor Hospital}
    {assignment : MatchingMarket.Matching Doctor Hospital}
    (feasible : market.IsFeasible assignment) (hospital : Hospital) :
    (cohort assignment hospital).Finite :=
  Set.finite_of_encard_le_coe (feasible hospital)

/-- A zero-quota hospital cannot be assigned any doctor. -/
theorem IsFeasible.not_assigned_of_capacity_zero {market : Market Doctor Hospital}
    {assignment : MatchingMarket.Matching Doctor Hospital}
    (feasible : market.IsFeasible assignment) {hospital : Hospital}
    (zero : market.capacity hospital = 0) (doctor : Doctor) :
    assignment doctor ≠ some hospital := by
  have empty : cohort assignment hospital = ∅ := by
    have bound := feasible hospital
    simpa only [zero, Nat.cast_zero, nonpos_iff_eq_zero, Set.encard_eq_zero] using bound
  intro assigned
  have member : doctor ∈ cohort assignment hospital := assigned
  rw [empty] at member
  exact member

/-- Quota-one feasibility is exactly the canonical one-to-one invariant. -/
theorem isFeasible_iff_isMatching_of_unitCapacity (market : Market Doctor Hospital)
    (unitCapacity : ∀ hospital, market.capacity hospital = 1)
    (assignment : MatchingMarket.Matching Doctor Hospital) :
    market.IsFeasible assignment ↔ MatchingMarket.IsMatching assignment := by
  simp only [IsFeasible, unitCapacity, Nat.cast_one, Set.encard_le_one_iff, mem_cohort]
  constructor
  · intro feasible first second hospital firstAssigned secondAssigned
    exact feasible hospital first second firstAssigned secondAssigned
  · intro matching hospital first second firstAssigned secondAssigned
    exact matching first second hospital firstAssigned secondAssigned

/-- At quota one, responsive and one-to-one blocking agree on individually
rational matchings. Hospital transitivity makes a preferable replacement
acceptable whenever its incumbent is acceptable. -/
theorem isBlockingPair_iff_of_unitCapacity (market : Market Doctor Hospital)
    (unitCapacity : ∀ hospital, market.capacity hospital = 1)
    (hospitalTransitive : Preference.Transitive market.rankings.prefersRight)
    {assignment : MatchingMarket.Matching Doctor Hospital}
    (matching : MatchingMarket.IsMatching assignment)
    (rational : market.rankings.IsIndividuallyRational assignment)
    (doctor : Doctor) (hospital : Hospital) :
    market.IsBlockingPair assignment doctor hospital ↔
      market.rankings.IsBlockingPair assignment doctor hospital := by
  rw [market.rankings.isBlockingPair_iff_pairwise matching doctor hospital]
  have vacant : (cohort assignment hospital).encard < (market.capacity hospital : ℕ∞) ↔
      ∀ incumbent, assignment incumbent ≠ some hospital := by
    simp only [unitCapacity, Nat.cast_one, Set.encard_lt_one,
      Set.eq_empty_iff_forall_notMem, mem_cohort]
  constructor
  · intro blocks
    refine ⟨blocks.1, ?_, fun _ => blocks.2.1⟩
    intro incumbent assigned
    rcases blocks.2.2 with spare | ⟨replacement, replaced, preference⟩
    · exact False.elim ((vacant.mp spare incumbent) assigned)
    · have equal := matching replacement incumbent hospital replaced assigned
      simpa only [equal] using preference
  · intro blocks
    classical
    by_cases occupied : ∃ incumbent, assignment incumbent = some hospital
    · obtain ⟨incumbent, assigned⟩ := occupied
      refine ⟨blocks.1, ?_, Or.inr ⟨incumbent, assigned, blocks.2.1 incumbent assigned⟩⟩
      exact Rank.strict_trans (hospitalTransitive hospital) (blocks.2.1 incumbent assigned)
        (rational incumbent hospital assigned).2
    · have noAssigned : ∀ incumbent, assignment incumbent ≠ some hospital := by
        intro incumbent assigned
        exact occupied ⟨incumbent, assigned⟩
      exact ⟨blocks.1, blocks.2.2 noAssigned, Or.inl (vacant.mpr noAssigned)⟩

/-- Unit quotas recover canonical one-to-one stability. Only hospital
transitivity is needed; linear rankings satisfy this weaker hypothesis. -/
theorem isStable_iff_of_unitCapacity (market : Market Doctor Hospital)
    (unitCapacity : ∀ hospital, market.capacity hospital = 1)
    (hospitalTransitive : Preference.Transitive market.rankings.prefersRight)
    (assignment : MatchingMarket.Matching Doctor Hospital) :
    market.IsStable assignment ↔ market.rankings.IsStable assignment := by
  constructor
  · rintro ⟨feasible, rational, unblocked⟩
    have matching :=
      (market.isFeasible_iff_isMatching_of_unitCapacity unitCapacity assignment).mp feasible
    apply (market.rankings.isStable_iff _).mpr
    refine ⟨matching, rational, ?_⟩
    rintro ⟨doctor, hospital, blocks⟩
    exact unblocked ⟨doctor, hospital,
      (market.isBlockingPair_iff_of_unitCapacity unitCapacity hospitalTransitive matching
        rational doctor hospital).mpr blocks⟩
  · intro stable
    obtain ⟨matching, rational, unblocked⟩ := (market.rankings.isStable_iff _).mp stable
    refine ⟨(market.isFeasible_iff_isMatching_of_unitCapacity unitCapacity assignment).mpr matching,
      rational, ?_⟩
    rintro ⟨doctor, hospital, blocks⟩
    exact unblocked ⟨doctor, hospital,
      (market.isBlockingPair_iff_of_unitCapacity unitCapacity hospitalTransitive matching
        rational doctor hospital).mp blocks⟩

/-- Extended cardinality rejects infinitely many doctors assigned to a
finite-quota hospital instead of silently counting them as zero. -/
theorem infinite_constant_assignment_not_feasible (rankings : MatchingMarket ℕ Unit) :
    ¬ (Market.mk rankings (fun _ => 1)).IsFeasible (fun _ => some ()) := by
  intro feasible
  have bound := feasible ()
  have cohort_univ : cohort (fun _ : ℕ => some ()) () = Set.univ := by
    ext doctor
    simp
  rw [cohort_univ, Set.encard_univ, ENat.card_eq_top_of_infinite] at bound
  simp at bound

/-- Ordinary natural cardinality defaults to zero on an infinite cohort,
so its naive quota bound accepts the same assignment rejected above. -/
theorem infinite_constant_assignment_ncard_bound :
    (cohort (fun _ : ℕ => some ()) ()).ncard ≤ 1 := by
  simp [cohort]

end Market
end GameTheory.Experimental.Exp168.Capacitated
