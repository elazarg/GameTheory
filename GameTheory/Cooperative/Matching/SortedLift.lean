module

/-
# Sorted slot lifts of responsive stable assignments

At each hospital, sort the assigned doctors by that hospital's ranking and
place them in the initial segment of its ordered slots. The ordering rules
out artificial improvements between two slots of the same hospital. Genuine
hospital moves project to responsive blocking pairs of the original assignment.
-/

public import GameTheory.Cooperative.Matching.Slots
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.List.Nodup

@[expose] public section

noncomputable section

namespace GameTheory.CapacitatedMarket

open MatchingMarket
open Classical

universe uDoctor uHospital

variable {Doctor : Type uDoctor} {Hospital : Type uHospital}
    (market : CapacitatedMarket Doctor Hospital)

@[instance_reducible]
private def hospitalOrder (linear : market.rankings.HasLinearPreferences)
    (hospital : Hospital) : LinearOrder Doctor where
  le first second := market.rankings.prefersRight hospital (some first) (some second)
  le_refl doctor := (linear.right hospital).1 _
  le_trans _ _ _ := (linear.right hospital).2.1 _ _ _
  le_antisymm _ _ forward reverse :=
    Option.some.inj ((linear.right hospital).2.2.2 _ _ forward reverse)
  le_total _ _ := (linear.right hospital).2.2.1 _ _
  toDecidableLE := Classical.decRel _

variable [Fintype Doctor]

/-- The assigned doctors in their hospital's preference order, best first. -/
def cohortList (linear : market.rankings.HasLinearPreferences)
    (assignment : Matching Doctor Hospital) (hospital : Hospital) : List Doctor :=
  letI := hospitalOrder market linear hospital
  (Finset.univ.filter (fun doctor => assignment doctor = some hospital)).sort

@[simp]
theorem mem_cohortList (linear : market.rankings.HasLinearPreferences)
    (assignment : Matching Doctor Hospital) (hospital : Hospital) (doctor : Doctor) :
    doctor ∈ market.cohortList linear assignment hospital ↔ assignment doctor = some hospital := by
  simp [cohortList]

theorem cohortList_nodup (linear : market.rankings.HasLinearPreferences)
    (assignment : Matching Doctor Hospital) (hospital : Hospital) :
    (market.cohortList linear assignment hospital).Nodup := by
  simp [cohortList]

theorem cohortList_pairwise (linear : market.rankings.HasLinearPreferences)
    (assignment : Matching Doctor Hospital) (hospital : Hospital) :
    List.Pairwise (fun first second =>
      market.rankings.prefersRight hospital (some first) (some second))
        (market.cohortList linear assignment hospital) := by
  let := hospitalOrder market linear hospital
  exact Finset.pairwise_sort
    (Finset.univ.filter (fun doctor => assignment doctor = some hospital))
    (fun first second : Doctor => first ≤ second)

theorem cohortList_length_encard (linear : market.rankings.HasLinearPreferences)
    (assignment : Matching Doctor Hospital) (hospital : Hospital) :
    ((market.cohortList linear assignment hospital).length : ℕ∞) =
      (cohort assignment hospital).encard := by
  have cohortEq : ((Finset.univ.filter (fun doctor => assignment doctor = some hospital) :
      Finset Doctor) : Set Doctor) = cohort assignment hospital := by
    ext doctor
    simp [cohort]
  simp only [cohortList, Finset.length_sort]
  rw [← cohortEq, Set.encard_coe_eq_coe_finsetCard]

theorem cohortList_length_le (linear : market.rankings.HasLinearPreferences)
    (assignment : Matching Doctor Hospital) (feasible : market.IsFeasible assignment)
    (hospital : Hospital) :
    (market.cohortList linear assignment hospital).length ≤ market.capacity hospital := by
  apply ENat.natCast_le_natCast.mp
  rw [market.cohortList_length_encard linear assignment hospital]
  exact feasible hospital

/-- Assign every doctor its rank in the sorted cohort of its hospital. -/
def sortedLift (linear : market.rankings.HasLinearPreferences)
    (assignment : Matching Doctor Hospital) (feasible : market.IsFeasible assignment) :
    Matching Doctor market.Slot := fun doctor =>
  match paired : assignment doctor with
  | none => none
  | some hospital =>
      have member : doctor ∈ market.cohortList linear assignment hospital :=
        (market.mem_cohortList linear assignment hospital doctor).mpr paired
      have bound : (market.cohortList linear assignment hospital).idxOf doctor <
          market.capacity hospital :=
        (List.idxOf_lt_length_of_mem member).trans_le
          (market.cohortList_length_le linear assignment feasible hospital)
      some ⟨hospital, ⟨(market.cohortList linear assignment hospital).idxOf doctor, bound⟩⟩

/-- Sorting changes only the slot index, never a doctor's assigned hospital. -/
@[simp]
theorem collapse_sortedLift (linear : market.rankings.HasLinearPreferences)
    (assignment : Matching Doctor Hospital) (feasible : market.IsFeasible assignment) :
    market.collapse (market.sortedLift linear assignment feasible) = assignment := by
  funext doctor
  unfold collapse sortedLift
  split <;> simp_all only [hospitalOf, Option.map_none, Option.map_some]

theorem sortedLift_some (linear : market.rankings.HasLinearPreferences)
    (assignment : Matching Doctor Hospital) (feasible : market.IsFeasible assignment)
    {doctor : Doctor} {hospital : Hospital} (paired : assignment doctor = some hospital) :
    ∃ index : Fin (market.capacity hospital),
      market.sortedLift linear assignment feasible doctor = some ⟨hospital, index⟩ ∧
        index.val = (market.cohortList linear assignment hospital).idxOf doctor := by
  unfold sortedLift
  split
  next absent =>
    rw [absent] at paired
    cases paired
  next other pairedOther =>
    have same : other = hospital := Option.some.inj (pairedOther.symm.trans paired)
    subst other
    exact ⟨_, rfl, rfl⟩

theorem sortedLift_native_pair (linear : market.rankings.HasLinearPreferences)
    (assignment : Matching Doctor Hospital) (feasible : market.IsFeasible assignment)
    {doctor : Doctor} {slot : market.Slot}
    (paired : market.sortedLift linear assignment feasible doctor = some slot) :
    assignment doctor = some slot.1 :=
  (congrFun (market.collapse_sortedLift linear assignment feasible) doctor).symm.trans
    (congrArg hospitalOf paired)

theorem sortedLift_index (linear : market.rankings.HasLinearPreferences)
    (assignment : Matching Doctor Hospital) (feasible : market.IsFeasible assignment)
    {doctor : Doctor} {hospital : Hospital} {index : Fin (market.capacity hospital)}
    (paired : market.sortedLift linear assignment feasible doctor = some ⟨hospital, index⟩) :
    (market.cohortList linear assignment hospital).idxOf doctor = index.val := by
  have native := market.sortedLift_native_pair linear assignment feasible paired
  obtain ⟨other, otherPaired, ranked⟩ := market.sortedLift_some linear assignment feasible native
  exact ranked.symm.trans (congrArg slotIndex (otherPaired.symm.trans paired))

/-- Sorted slot assignments are one-to-one, even if a hospital employs many doctors. -/
theorem sortedLift_isMatching (linear : market.rankings.HasLinearPreferences)
    (assignment : Matching Doctor Hospital) (feasible : market.IsFeasible assignment) :
    IsMatching (market.sortedLift linear assignment feasible) := by
  intro first second slot firstPaired secondPaired
  rcases slot with ⟨hospital, index⟩
  have firstNative := market.sortedLift_native_pair linear assignment feasible firstPaired
  have firstIndex := market.sortedLift_index linear assignment feasible firstPaired
  have secondIndex := market.sortedLift_index linear assignment feasible secondPaired
  exact (List.idxOf_inj ((market.mem_cohortList linear assignment hospital first).mpr
    firstNative)).mp (firstIndex.trans secondIndex.symm)

/-- Exactly the initial segment of each hospital's slots is occupied. -/
theorem sortedLift_occupies_initial (linear : market.rankings.HasLinearPreferences)
    (assignment : Matching Doctor Hospital) (feasible : market.IsFeasible assignment)
    (hospital : Hospital) (index : Fin (market.capacity hospital))
    (before : index.val < (market.cohortList linear assignment hospital).length) :
    ∃ doctor, market.sortedLift linear assignment feasible doctor = some ⟨hospital, index⟩ := by
  let doctor := (market.cohortList linear assignment hospital).get ⟨index.val, before⟩
  have member : doctor ∈ market.cohortList linear assignment hospital := List.get_mem _ _
  obtain ⟨other, paired, ranked⟩ := market.sortedLift_some linear assignment feasible
    ((market.mem_cohortList linear assignment hospital doctor).mp member)
  have same : other = index := by
    apply Fin.ext
    exact ranked.trans (List.get_idxOf (market.cohortList_nodup linear assignment hospital) _)
  exact ⟨doctor, by simpa only [same] using paired⟩

theorem sortedLift_hospital_prefers_of_index_lt
    (linear : market.rankings.HasLinearPreferences)
    (assignment : Matching Doctor Hospital) (feasible : market.IsFeasible assignment)
    {first second : Doctor} {hospital : Hospital}
    {firstIndex secondIndex : Fin (market.capacity hospital)}
    (firstPaired : market.sortedLift linear assignment feasible first = some ⟨hospital, firstIndex⟩)
    (secondPaired : market.sortedLift linear assignment feasible second =
      some ⟨hospital, secondIndex⟩)
    (before : firstIndex.val < secondIndex.val) :
    market.rankings.prefersRight hospital (some first) (some second) := by
  have firstMember := (market.mem_cohortList linear assignment hospital first).mpr
    (market.sortedLift_native_pair linear assignment feasible firstPaired)
  have secondMember := (market.mem_cohortList linear assignment hospital second).mpr
    (market.sortedLift_native_pair linear assignment feasible secondPaired)
  have firstRank := market.sortedLift_index linear assignment feasible firstPaired
  have secondRank := market.sortedLift_index linear assignment feasible secondPaired
  have rankLt : (market.cohortList linear assignment hospital).idxOf first <
      (market.cohortList linear assignment hospital).idxOf second := by
    rw [firstRank, secondRank]
    exact before
  have ordered := (market.cohortList_pairwise linear assignment hospital).rel_get_of_lt
    (a := ⟨_, List.idxOf_lt_length_of_mem firstMember⟩)
    (b := ⟨_, List.idxOf_lt_length_of_mem secondMember⟩) rankLt
  simpa only [List.idxOf_get] using ordered

/-- Sorting occupied slots removes the artificial same-hospital blocking
pairs, while every genuine hospital move would block the native assignment. -/
theorem sortedLift_stable (linear : market.rankings.HasLinearPreferences)
    {assignment : Matching Doctor Hospital} (stable : market.IsStable assignment) :
    market.slotMarket.IsStable
      (market.sortedLift linear assignment stable.isFeasible) := by
  have valid := market.sortedLift_isMatching linear assignment stable.isFeasible
  apply (market.slotMarket.isStable_iff _).mpr
  refine ⟨valid, ?_, ?_⟩
  · intro doctor slot paired
    have native := market.sortedLift_native_pair linear assignment stable.isFeasible paired
    have rational := stable.isIndividuallyRational doctor slot.1 native
    refine ⟨⟨rational.1, ?_⟩, rational.2⟩
    intro same
    change some slot.1 = none at same
    cases same
  · rintro ⟨doctor, ⟨hospital, index⟩, blocked⟩
    have blocks := (market.slotMarket.isBlockingPair_iff_pairwise valid doctor _).mp blocked
    by_cases nativePaired : assignment doctor = some hospital
    · obtain ⟨current, currentPaired, currentRank⟩ :=
        market.sortedLift_some linear assignment stable.isFeasible nativePaired
      have before : index.val < current.val := by
        apply Nat.lt_of_not_ge
        intro reversed
        apply blocks.1.2
        rw [currentPaired]
        exact ⟨(linear.left doctor).1 _, fun _ => reversed⟩
      have bound : current.val < (market.cohortList linear assignment hospital).length := by
        rw [currentRank]
        exact List.idxOf_lt_length_of_mem
          ((market.mem_cohortList linear assignment hospital doctor).mpr nativePaired)
      obtain ⟨earlier, earlierPaired⟩ :=
        market.sortedLift_occupies_initial linear assignment stable.isFeasible
          hospital index (before.trans bound)
      have ordered := market.sortedLift_hospital_prefers_of_index_lt linear assignment
        stable.isFeasible earlierPaired currentPaired before
      exact (blocks.2.1 earlier earlierPaired).2 ordered
    · have weak := blocks.1.1.1
      change market.rankings.prefersLeft doctor (some hospital)
        (hospitalOf (market.sortedLift linear assignment stable.isFeasible doctor)) at weak
      have projected :
          hospitalOf (market.sortedLift linear assignment stable.isFeasible doctor) =
            assignment doctor :=
        congrFun (market.collapse_sortedLift linear assignment stable.isFeasible) doctor
      rw [projected] at weak
      have directStrict : Preference.strict market.rankings.prefersLeft doctor
          (some hospital) (assignment doctor) :=
        ⟨weak, fun reverse => nativePaired ((linear.left doctor).2.2.2 _ _ reverse weak)⟩
      apply stable.not_isBlockingPair doctor hospital
      refine ⟨directStrict, ?_⟩
      by_cases occupied : ∃ incumbent,
          market.sortedLift linear assignment stable.isFeasible incumbent =
            some ⟨hospital, index⟩
      · obtain ⟨incumbent, paired⟩ := occupied
        exact Or.inr ⟨incumbent,
          market.sortedLift_native_pair linear assignment stable.isFeasible paired,
          blocks.2.1 incumbent paired⟩
      · have beyond : (market.cohortList linear assignment hospital).length ≤ index.val := by
          apply Nat.le_of_not_gt
          intro before
          exact occupied
            (market.sortedLift_occupies_initial linear assignment stable.isFeasible
              hospital index before)
        have vacancy : (cohort assignment hospital).encard < (market.capacity hospital : ℕ∞) := by
          rw [← market.cohortList_length_encard linear assignment hospital]
          exact ENat.natCast_lt_natCast.mpr (beyond.trans_lt index.isLt)
        exact Or.inl ⟨vacancy, blocks.2.2 (fun incumbent paired => occupied ⟨incumbent, paired⟩)⟩

/-- Every finite-doctor native stable assignment has a stable ordered-slot
lift with exactly the same doctor-to-hospital assignment. -/
theorem exists_stable_slot_lift (linear : market.rankings.HasLinearPreferences)
    {assignment : Matching Doctor Hospital} (stable : market.IsStable assignment) :
    ∃ lift : Matching Doctor market.Slot,
      market.slotMarket.IsStable lift ∧ market.collapse lift = assignment :=
  ⟨market.sortedLift linear assignment stable.isFeasible,
    market.sortedLift_stable linear stable,
    market.collapse_sortedLift linear assignment stable.isFeasible⟩

end GameTheory.CapacitatedMarket
