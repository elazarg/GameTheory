module

/-
# Ordered hospital-slot encoding

Each hospital is represented by its finite quota of slots, using the existing
one-to-one matching semantics. Doctors compare
different hospitals by their original ranking and refine slots of the same
hospital by preferring earlier indices. Every slot inherits its hospital's
ranking of doctors. Slot stability projects to responsive capacitated
stability. An arbitrary lift of a stable hospital assignment need not be
slot-stable: the ordering of occupied slots matters.
-/

public import GameTheory.Cooperative.Matching.Capacitated
public import GameTheory.Cooperative.GaleShapley
public import Mathlib.Data.Fintype.Card

@[expose] public section

noncomputable section

namespace GameTheory.CapacitatedMarket

open MatchingMarket

universe uDoctor uHospital

variable {Doctor : Type uDoctor} {Hospital : Type uHospital}

/-- A hospital together with one of its quota-many distinct slots. -/
abbrev Slot (market : CapacitatedMarket Doctor Hospital) :=
  (hospital : Hospital) × Fin (market.capacity hospital)

/-- Forget the artificial slot index, retaining the outside option. -/
def hospitalOf {market : CapacitatedMarket Doctor Hospital} :
    Option (Slot market) → Option Hospital :=
  Option.map Sigma.fst

/-- The within-hospital priority used only by the encoding. -/
def slotIndex {market : CapacitatedMarket Doctor Hospital} : Option (Slot market) → ℕ
  | none => 0
  | some slot => slot.2.val

/-- The one-to-one market on doctors and ordered hospital slots. -/
def slotMarket (market : CapacitatedMarket Doctor Hospital) :
    MatchingMarket Doctor (Slot market) where
  prefersLeft doctor first second :=
    market.rankings.prefersLeft doctor (hospitalOf first) (hospitalOf second) ∧
      (hospitalOf first = hospitalOf second → slotIndex first ≤ slotIndex second)
  prefersRight slot := market.rankings.prefersRight slot.1

private theorem slot_eq_of_readouts {market : CapacitatedMarket Doctor Hospital}
    {first second : Option (Slot market)}
    (hospital : hospitalOf first = hospitalOf second)
    (index : slotIndex first = slotIndex second) : first = second := by
  cases first with
  | none => cases second <;> simp_all [hospitalOf]
  | some first =>
      cases second with
      | none => simp_all [hospitalOf]
      | some second =>
          rcases first with ⟨firstHospital, firstIndex⟩
          rcases second with ⟨secondHospital, secondIndex⟩
          have equal : firstHospital = secondHospital := Option.some.inj hospital
          subst secondHospital
          have sameIndex : firstIndex = secondIndex := Fin.ext index
          subst secondIndex
          rfl

/-- The explicit slot refinement preserves strict linearity. It introduces no
numerical utility representation of the underlying hospital ranking. -/
theorem slotMarket_linear (market : CapacitatedMarket Doctor Hospital)
    (linear : market.rankings.HasLinearPreferences) :
    (slotMarket market).HasLinearPreferences := by
  constructor
  · intro doctor
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro item
      exact ⟨(linear.left doctor).1 _, fun _ => le_rfl⟩
    · intro first middle last firstPreferred lastPreferred
      refine ⟨(linear.left doctor).2.1 _ _ _ firstPreferred.1 lastPreferred.1, ?_⟩
      intro endsEqual
      have middleEqual : hospitalOf first = hospitalOf middle :=
        (linear.left doctor).2.2.2 _ _ firstPreferred.1 (by
          have reverse := lastPreferred.1
          rw [← endsEqual] at reverse
          exact reverse)
      exact (firstPreferred.2 middleEqual).trans
        (lastPreferred.2 (middleEqual.symm.trans endsEqual))
    · intro first second
      by_cases same : hospitalOf first = hospitalOf second
      · rcases le_total (slotIndex first) (slotIndex second) with forward | reverse
        · refine Or.inl ⟨?_, fun _ => forward⟩
          rw [same]
          exact (linear.left doctor).1 _
        · refine Or.inr ⟨?_, fun _ => reverse⟩
          rw [← same]
          exact (linear.left doctor).1 _
      · rcases (linear.left doctor).2.2.1 (hospitalOf first) (hospitalOf second) with
          forward | reverse
        · exact Or.inl ⟨forward, fun equal => False.elim (same equal)⟩
        · exact Or.inr ⟨reverse, fun equal => False.elim (same equal.symm)⟩
    · intro first second forward reverse
      have same := (linear.left doctor).2.2.2 _ _ forward.1 reverse.1
      exact slot_eq_of_readouts same (le_antisymm (forward.2 same) (reverse.2 same.symm))
  · intro slot
    exact linear.right slot.1

/-- Project a slot assignment back to a doctor-to-hospital assignment. -/
def collapse (market : CapacitatedMarket Doctor Hospital)
    (assignment : Matching Doctor (Slot market)) : Matching Doctor Hospital :=
  fun doctor => hospitalOf (assignment doctor)

@[simp]
theorem collapse_none_iff (market : CapacitatedMarket Doctor Hospital)
    (assignment : Matching Doctor (Slot market)) (doctor : Doctor) :
    collapse market assignment doctor = none ↔ assignment doctor = none := by
  simp [collapse, hospitalOf]

/-- A hospital assignment in the projection has a concrete occupied slot. -/
theorem mem_cohort_collapse_iff (market : CapacitatedMarket Doctor Hospital)
    (assignment : Matching Doctor (Slot market)) (doctor : Doctor) (hospital : Hospital) :
    doctor ∈ MatchingMarket.cohort (collapse market assignment) hospital ↔
      ∃ index : Fin (market.capacity hospital), assignment doctor = some ⟨hospital, index⟩ := by
  constructor
  · intro member
    change hospitalOf (assignment doctor) = some hospital at member
    cases paired : assignment doctor with
    | none => simp [paired, hospitalOf] at member
    | some slot =>
        rcases slot with ⟨other, index⟩
        have same : other = hospital := by simpa [paired, hospitalOf] using member
        subst other
        exact ⟨index, rfl⟩
  · rintro ⟨index, paired⟩
    change hospitalOf (assignment doctor) = some hospital
    rw [paired]
    rfl

/-- Occupied slot indices at one hospital. -/
def occupied (market : CapacitatedMarket Doctor Hospital)
    (assignment : Matching Doctor (Slot market)) (hospital : Hospital) :
    Set (Fin (market.capacity hospital)) :=
  {index | ∃ doctor, assignment doctor = some ⟨hospital, index⟩}

/-- A valid slot assignment gives a bijection between a hospital's collapsed
cohort and its occupied slots, without a finite-doctor assumption. -/
theorem cohort_encard_eq_occupied (market : CapacitatedMarket Doctor Hospital)
    {assignment : Matching Doctor (Slot market)} (valid : IsMatching assignment)
    (hospital : Hospital) :
    (MatchingMarket.cohort (collapse market assignment) hospital).encard =
      (occupied market assignment hospital).encard := by
  classical
  let index (doctor : MatchingMarket.cohort (collapse market assignment) hospital) :
      Fin (market.capacity hospital) :=
    Classical.choose ((mem_cohort_collapse_iff market assignment doctor.1 hospital).mp doctor.2)
  have assigned (doctor : MatchingMarket.cohort (collapse market assignment) hospital) :
      assignment doctor.1 = some ⟨hospital, index doctor⟩ :=
    Classical.choose_spec
      ((mem_cohort_collapse_iff market assignment doctor.1 hospital).mp doctor.2)
  let forward : MatchingMarket.cohort (collapse market assignment) hospital →
      occupied market assignment hospital :=
    fun doctor => ⟨index doctor, doctor.1, assigned doctor⟩
  have injective : Function.Injective forward := by
    intro first second equal
    apply Subtype.ext
    have sameIndex : index first = index second := congrArg Subtype.val equal
    exact valid first.1 second.1 ⟨hospital, index first⟩ (assigned first)
      (by rw [sameIndex]; exact assigned second)
  have surjective : Function.Surjective forward := by
    rintro ⟨slot, doctor, paired⟩
    have member := (mem_cohort_collapse_iff market assignment doctor hospital).mpr ⟨slot, paired⟩
    refine ⟨⟨doctor, member⟩, ?_⟩
    apply Subtype.ext
    apply Fin.ext
    exact congrArg (fun slot : Slot market => slot.2.val)
      (Option.some.inj ((assigned ⟨doctor, member⟩).symm.trans paired))
  exact Set.encard_congr (Equiv.ofBijective forward ⟨injective, surjective⟩)

/-- Slot injectivity enforces quotas even on an infinite doctor carrier. -/
theorem collapse_isFeasible (market : CapacitatedMarket Doctor Hospital)
    {assignment : Matching Doctor (Slot market)} (valid : IsMatching assignment) :
    market.IsFeasible (collapse market assignment) := by
  intro hospital
  rw [cohort_encard_eq_occupied market valid hospital]
  exact Set.encard_le_card.trans_eq (by simp)

/-- A genuinely vacant hospital has an unoccupied slot. A zero quota cannot
satisfy the vacancy premise. -/
theorem exists_empty_slot_of_vacancy (market : CapacitatedMarket Doctor Hospital)
    {assignment : Matching Doctor (Slot market)} (valid : IsMatching assignment)
    (hospital : Hospital)
    (vacancy : (MatchingMarket.cohort (collapse market assignment) hospital).encard <
      (market.capacity hospital : ℕ∞)) :
    ∃ index : Fin (market.capacity hospital),
      ∀ doctor, assignment doctor ≠ some ⟨hospital, index⟩ := by
  classical
  by_contra absent
  push Not at absent
  have full : occupied market assignment hospital = Set.univ :=
    Set.eq_univ_iff_forall.mpr absent
  rw [cohort_encard_eq_occupied market valid hospital, full] at vacancy
  simp at vacancy

/-- A strict improvement between hospitals is a strict improvement to every
slot of the preferred hospital, independently of the artificial slot order. -/
theorem doctor_strict_at_slot (market : CapacitatedMarket Doctor Hospital)
    (assignment : Matching Doctor (Slot market)) (doctor : Doctor) (hospital : Hospital)
    (index : Fin (market.capacity hospital))
    (preferred : Preference.strict market.rankings.prefersLeft doctor
      (some hospital) (collapse market assignment doctor)) :
    Preference.strict (slotMarket market).prefersLeft doctor
      (some ⟨hospital, index⟩) (assignment doctor) := by
  refine ⟨⟨preferred.1, ?_⟩, fun reverse => preferred.2 reverse.1⟩
  intro same
  change some hospital = hospitalOf (assignment doctor) at same
  change Preference.strict market.rankings.prefersLeft doctor
    (some hospital) (hospitalOf (assignment doctor)) at preferred
  rw [← same] at preferred
  exact False.elim (preferred.2 preferred.1)

/-- Slot individual rationality projects to the original hospital ranking. -/
theorem collapse_individuallyRational (market : CapacitatedMarket Doctor Hospital)
    {assignment : Matching Doctor (Slot market)}
    (rational : (slotMarket market).IsIndividuallyRational assignment) :
    market.rankings.IsIndividuallyRational (collapse market assignment) := by
  intro doctor hospital paired
  obtain ⟨index, slotPaired⟩ :=
    (mem_cohort_collapse_iff market assignment doctor hospital).mp paired
  have conditions := rational doctor ⟨hospital, index⟩ slotPaired
  exact ⟨conditions.1.1, conditions.2⟩

/-- Every responsive hospital blocking pair gives a blocking pair at a vacant
slot or at the slot held by the less-preferred incumbent. -/
theorem blocking_pair_lifts (market : CapacitatedMarket Doctor Hospital)
    {assignment : Matching Doctor (Slot market)} (valid : IsMatching assignment)
    {doctor : Doctor} {hospital : Hospital}
    (blocks : market.IsBlockingPair (collapse market assignment) doctor hospital) :
    ∃ slot : Slot market, (slotMarket market).IsBlockingPair assignment doctor slot := by
  rcases blocks with ⟨doctorPreferred, ⟨vacancy, hospitalAccepts⟩ | replacement⟩
  · obtain ⟨index, empty⟩ := exists_empty_slot_of_vacancy market valid hospital vacancy
    refine ⟨⟨hospital, index⟩, ?_⟩
    apply ((slotMarket market).isBlockingPair_iff_pairwise valid doctor _).mpr
    refine ⟨doctor_strict_at_slot market assignment doctor hospital index doctorPreferred, ?_, ?_⟩
    · intro incumbent paired
      exact False.elim (empty incumbent paired)
    · intro _
      exact hospitalAccepts
  · obtain ⟨incumbent, member, hospitalPreferred⟩ := replacement
    obtain ⟨index, incumbentPaired⟩ :=
      (mem_cohort_collapse_iff market assignment incumbent hospital).mp member
    refine ⟨⟨hospital, index⟩, ?_⟩
    apply ((slotMarket market).isBlockingPair_iff_pairwise valid doctor _).mpr
    refine ⟨doctor_strict_at_slot market assignment doctor hospital index doctorPreferred, ?_, ?_⟩
    · intro other paired
      have same := valid other incumbent ⟨hospital, index⟩ paired incumbentPaired
      subst other
      exact hospitalPreferred
    · intro empty
      exact False.elim (empty incumbent incumbentPaired)

/-- A stable one-to-one slot assignment collapses to a quota-feasible,
individually rational assignment with no responsive hospital blocking pair.
This projection needs no finite doctor carrier or extra preference laws. -/
theorem slot_stable_collapse (market : CapacitatedMarket Doctor Hospital)
    {assignment : Matching Doctor (Slot market)}
    (stable : (slotMarket market).IsStable assignment) :
    market.IsStable (collapse market assignment) := by
  refine ⟨collapse_isFeasible market stable.isMatching,
    collapse_individuallyRational market stable.isIndividuallyRational, ?_⟩
  rintro ⟨doctor, hospital, blocks⟩
  obtain ⟨slot, slotBlocks⟩ := blocking_pair_lifts market stable.isMatching blocks
  exact stable.not_isBlockingPair doctor slot slotBlocks

/-- The slot encoding cannot assign a doctor to a zero-quota hospital. -/
theorem capacity_zero_unassigned (market : CapacitatedMarket Doctor Hospital)
    {assignment : Matching Doctor (Slot market)} (valid : IsMatching assignment)
    {hospital : Hospital} (zero : market.capacity hospital = 0) (doctor : Doctor) :
    collapse market assignment doctor ≠ some hospital :=
  (collapse_isFeasible market valid).not_assigned_of_capacity_zero zero doctor

/-- Finite responsive markets have a stable assignment by applying the
existing one-to-one deferred-acceptance theorem to their ordered slots. -/
theorem exists_stable (market : CapacitatedMarket Doctor Hospital)
    [Fintype Doctor] [Fintype Hospital] (linear : market.rankings.HasLinearPreferences) :
    ∃ assignment : Matching Doctor Hospital, market.IsStable assignment := by
  let slotLinear := slotMarket_linear market linear
  exact ⟨collapse market ((slotMarket market).deferredAcceptance slotLinear),
    slot_stable_collapse market ((slotMarket market).deferredAcceptance_isStable slotLinear)⟩

end GameTheory.CapacitatedMarket
