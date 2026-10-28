module

/-
# Placement of the outside-option guard

This alternative responsive rule asks whether a newcomer is acceptable only
when filling a vacant place. A replacement instead compares the newcomer
directly with its incumbent. It recovers the existing one-to-one blocking
predicate at unit quotas without extra preference laws. On individually
rational assignments with transitive hospital rankings, it agrees with the
direct candidate's rule at every quota.
-/

public import GameTheory.Experimental.Exp168.Capacitated

@[expose] public section

namespace GameTheory.Experimental.Exp168.BlockingComparison

universe uDoctor uHospital

variable {Doctor : Type uDoctor} {Hospital : Type uHospital}

/-- Require outside-option acceptability for vacancy, and an incumbent
comparison for replacement. This is an experimental comparison, not a second
public capacitated stability concept. -/
def IsBlockingPair (market : Capacitated.Market Doctor Hospital)
    (assignment : MatchingMarket.Matching Doctor Hospital)
    (doctor : Doctor) (hospital : Hospital) : Prop :=
  Preference.strict market.rankings.prefersLeft doctor (some hospital) (assignment doctor) ∧
    (((Capacitated.Market.cohort assignment hospital).encard <
        (market.capacity hospital : ℕ∞) ∧
      Preference.strict market.rankings.prefersRight hospital (some doctor) none) ∨
      ∃ incumbent ∈ Capacitated.Market.cohort assignment hospital,
        Preference.strict market.rankings.prefersRight hospital (some doctor) (some incumbent))

/-- The alternative rule specializes to canonical one-to-one blocking without
individual-rationality, transitivity, or linearity assumptions. -/
theorem isBlockingPair_iff_oneToOne_of_unitCapacity
    (market : Capacitated.Market Doctor Hospital)
    (unitCapacity : ∀ hospital, market.capacity hospital = 1)
    {assignment : MatchingMarket.Matching Doctor Hospital}
    (matching : MatchingMarket.IsMatching assignment) (doctor : Doctor) (hospital : Hospital) :
    IsBlockingPair market assignment doctor hospital ↔
      market.rankings.IsBlockingPair assignment doctor hospital := by
  have vacant : (Capacitated.Market.cohort assignment hospital).encard <
      (market.capacity hospital : ℕ∞) ↔
      ∀ incumbent, assignment incumbent ≠ some hospital := by
    simp only [unitCapacity, Nat.cast_one, Set.encard_lt_one,
      Set.eq_empty_iff_forall_notMem, Capacitated.Market.mem_cohort]
  constructor
  · rintro ⟨doctorPreferred, vacancy | replacement⟩
    · refine ⟨doctorPreferred, ?_, fun _ => vacancy.2⟩
      intro incumbent assigned
      exact False.elim ((vacant.mp vacancy.1 incumbent) assigned)
    · obtain ⟨incumbent, assigned, hospitalPreferred⟩ := replacement
      refine ⟨doctorPreferred, ?_, ?_⟩
      · intro other paired
        have same := matching other incumbent hospital paired assigned
        subst other
        exact hospitalPreferred
      · intro empty
        exact False.elim (empty incumbent assigned)
  · intro blocks
    classical
    by_cases occupied : ∃ incumbent, assignment incumbent = some hospital
    · obtain ⟨incumbent, assigned⟩ := occupied
      exact ⟨blocks.1, Or.inr ⟨incumbent, assigned, blocks.2.1 incumbent assigned⟩⟩
    · have empty : ∀ incumbent, assignment incumbent ≠ some hospital := by
        intro incumbent assigned
        exact occupied ⟨incumbent, assigned⟩
      exact ⟨blocks.1, Or.inl ⟨vacant.mpr empty, blocks.2.2 empty⟩⟩

/-- Using the alternative blocker, unit-quota stability is exactly canonical
one-to-one stability on raw rankings. No second stability predicate is needed
to state this comparison. -/
theorem stability_iff_oneToOne_of_unitCapacity
    (market : Capacitated.Market Doctor Hospital)
    (unitCapacity : ∀ hospital, market.capacity hospital = 1)
    (assignment : MatchingMarket.Matching Doctor Hospital) :
    (market.IsFeasible assignment ∧ market.rankings.IsIndividuallyRational assignment ∧
      ¬ ∃ doctor hospital, IsBlockingPair market assignment doctor hospital) ↔
      market.rankings.IsStable assignment := by
  constructor
  · rintro ⟨feasible, rational, unblocked⟩
    have matching :=
      (market.isFeasible_iff_isMatching_of_unitCapacity unitCapacity assignment).mp feasible
    refine ⟨matching, rational, ?_⟩
    rintro ⟨doctor, hospital, blocks⟩
    exact unblocked ⟨doctor, hospital,
      (isBlockingPair_iff_oneToOne_of_unitCapacity market unitCapacity matching doctor hospital).mpr
        blocks⟩
  · rintro ⟨matching, rational, unblocked⟩
    refine ⟨(market.isFeasible_iff_isMatching_of_unitCapacity unitCapacity assignment).mpr matching,
      rational, ?_⟩
    rintro ⟨doctor, hospital, blocks⟩
    exact unblocked ⟨doctor, hospital,
      (isBlockingPair_iff_oneToOne_of_unitCapacity market unitCapacity matching doctor hospital).mp
        blocks⟩

/-- Under the source ranking laws and individual rationality, a superior
replacement is already acceptable, so either guard placement gives the same
responsive blocking pairs. This holds at arbitrary quotas. -/
theorem current_iff_alternate (market : Capacitated.Market Doctor Hospital)
    (hospitalTransitive : Preference.Transitive market.rankings.prefersRight)
    {assignment : MatchingMarket.Matching Doctor Hospital}
    (rational : market.rankings.IsIndividuallyRational assignment)
    (doctor : Doctor) (hospital : Hospital) :
    market.IsBlockingPair assignment doctor hospital ↔
      IsBlockingPair market assignment doctor hospital := by
  constructor
  · rintro ⟨doctorPreferred, acceptable, vacancy | replacement⟩
    · exact ⟨doctorPreferred, Or.inl ⟨vacancy, acceptable⟩⟩
    · exact ⟨doctorPreferred, Or.inr replacement⟩
  · rintro ⟨doctorPreferred, vacancy | replacement⟩
    · exact ⟨doctorPreferred, vacancy.2, Or.inl vacancy.1⟩
    · obtain ⟨incumbent, assigned, hospitalPreferred⟩ := replacement
      refine ⟨doctorPreferred, ?_, Or.inr ⟨incumbent, assigned, hospitalPreferred⟩⟩
      exact Rank.strict_trans (hospitalTransitive hospital) hospitalPreferred
        (rational incumbent hospital assigned).2

namespace Controls

/-- The hospital cycles: newcomer over incumbent, incumbent over outside,
and outside over newcomer. No transitivity law is asserted for this raw data. -/
def cyclic : Capacitated.Market Bool Unit where
  rankings :=
    { prefersLeft := fun _ first second => first = some () ∨ second = none
      prefersRight := fun _ first second => first = second ∨
        (first = some false ∧ second = some true) ∨
        (first = some true ∧ second = none) ∨
        (first = none ∧ second = some false) }
  capacity _ := 1

/-- Only the incumbent `true` is assigned. -/
def assigned : MatchingMarket.Matching Bool Unit :=
  fun doctor => if doctor then some () else none

theorem assigned_isMatching : MatchingMarket.IsMatching assigned := by
  intro first second hospital firstAssigned secondAssigned
  cases first <;> cases second <;> simp_all [assigned]

theorem assigned_rational : cyclic.rankings.IsIndividuallyRational assigned := by
  intro doctor hospital paired
  cases doctor <;> cases hospital <;> simp [assigned, cyclic] at paired ⊢

theorem assigned_feasible : cyclic.IsFeasible assigned :=
  (cyclic.isFeasible_iff_isMatching_of_unitCapacity (fun _ => rfl) assigned).mpr
    assigned_isMatching

theorem hospital_not_transitive : ¬ Preference.Transitive cyclic.rankings.prefersRight := by
  intro transitive
  have impossible := transitive () (some false) (some true) none
    (by simp [cyclic]) (by simp [cyclic])
  simp [cyclic] at impossible

/-- The alternative rule permits replacing the inferior incumbent. -/
theorem alternate_blocks : IsBlockingPair cyclic assigned false () := by
  refine ⟨?_, Or.inr ⟨true, rfl, ?_⟩⟩ <;>
    simp [Preference.strict, Rank.strict, cyclic, assigned]

/-- The current rule rejects this replacement because the newcomer is not
acceptable relative to the outside option under the nontransitive ranking. -/
theorem current_does_not_block : ¬ cyclic.IsBlockingPair assigned false () := by
  intro blocks
  have acceptable := blocks.2.1.1
  simp [cyclic] at acceptable

/-- Guard placement is observably different on raw rankings even for a valid,
feasible, individually rational unit-quota assignment. -/
theorem guard_placement_differs :
    MatchingMarket.IsMatching assigned ∧ cyclic.IsFeasible assigned ∧
      cyclic.rankings.IsIndividuallyRational assigned ∧
      IsBlockingPair cyclic assigned false () ∧ ¬ cyclic.IsBlockingPair assigned false () :=
  ⟨assigned_isMatching, assigned_feasible, assigned_rational,
    alternate_blocks, current_does_not_block⟩

end Controls

end GameTheory.Experimental.Exp168.BlockingComparison
