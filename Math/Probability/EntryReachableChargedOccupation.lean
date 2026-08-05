/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability.AnalyticOccupationRealization
import Math.Probability.ReachableClosedClass

/-!
# Entry-aware charged occupation alternatives

Given a finite family of actual source-consuming transitions, first discard
every transition whose source is not support-reachable from the current
entry.  The charged occupation alternative on this restricted operational
family has two useful branches:

* a positive charged circulation whose active support is closed and entirely
  reachable from the entry;
* a potential taking values in `[0,1]` whose one-step discrepancies dominate
  a common positive rescaling of every reachable charge.

Restriction can destroy positive charge: an unrestricted circulation may
live entirely in an unreachable closed class.  The final section gives the
minimal two-state example and isolates the exact support condition under
which an existing circulation survives restriction.
-/

noncomputable section

namespace Math
namespace Probability

open Finset BigOperators

variable {S I : Type*}

/-- A support edge available from a source state under at least one
operational transition. -/
def AvailableSupportStep
    (kernel : I → PMF S) (source : I → S)
    (current next : S) : Prop :=
  ∃ i, source i = current ∧ kernel i next ≠ 0

/-- Reachability in the union of the operational transition supports. -/
def AvailableReachable
    (kernel : I → PMF S) (source : I → S)
    (current next : S) : Prop :=
  Relation.ReflTransGen
    (AvailableSupportStep kernel source) current next

/-- Operational indices whose source can be reached from the current
entry. -/
noncomputable def reachableOccupationIndices
    [Fintype I]
    (kernel : I → PMF S) (source : I → S) (entry : S) :
    Finset I := by
  classical
  exact Finset.univ.filter fun i =>
    AvailableReachable kernel source entry (source i)

abbrev ReachableOccupationIndex
    [Fintype I]
    (kernel : I → PMF S) (source : I → S) (entry : S) :=
  ↥(reachableOccupationIndices kernel source entry)

theorem ReachableOccupationIndex.source_reachable
    [Fintype I]
    (kernel : I → PMF S) (source : I → S) (entry : S)
    (i : ReachableOccupationIndex kernel source entry) :
    AvailableReachable kernel source entry (source i.1) := by
  classical
  have hi := i.property
  change i.1 ∈ reachableOccupationIndices kernel source entry at hi
  unfold reachableOccupationIndices at hi
  exact (Finset.mem_filter.mp hi).2

/-- A normalized charged circulation on the entry-reachable operational
family, with one explicit positive-charge index selected from its mass. -/
structure EntryReachablePositiveChargedCirculation
    [Fintype S] [Fintype I] [DecidableEq S]
    (kernel : I → PMF S) (source : I → S)
    (charge : I → ℝ) (entry : S) where
  mass : ReachableOccupationIndex kernel source entry → ℝ
  mass_nonneg : ∀ i, 0 ≤ mass i
  balance :
    ∀ destination,
      ∑ i, mass i *
        actualOccupationColumn
          (fun j : ReachableOccupationIndex kernel source entry =>
            kernel j.1)
          (fun j : ReachableOccupationIndex kernel source entry =>
            source j.1)
          i destination = 0
  charge_eq_one :
    ∑ i, mass i * charge i.1 = 1
  selected : ReachableOccupationIndex kernel source entry
  selected_charge_pos : 0 < mass selected * charge selected.1

namespace EntryReachablePositiveChargedCirculation

variable [Fintype S] [Fintype I] [DecidableEq S]
  {kernel : I → PMF S} {source : I → S}
  {charge : I → ℝ} {entry : S}

/-- A normalized restricted circulation always has a positive summand. -/
theorem of_hasNormalizedPositiveChargedCirculation
    (C :
      HasNormalizedPositiveChargedCirculation
        (actualOccupationColumn
          (fun i : ReachableOccupationIndex kernel source entry =>
            kernel i.1)
          (fun i : ReachableOccupationIndex kernel source entry =>
            source i.1))
        (fun i : ReachableOccupationIndex kernel source entry =>
          charge i.1)) :
    Nonempty
      (EntryReachablePositiveChargedCirculation
        kernel source charge entry) := by
  obtain ⟨mass, hmass, hbalance, hcharge⟩ := C
  have hselected :
      ∃ i, 0 < mass i * charge i.1 := by
    by_contra hnone
    push Not at hnone
    have hnonpos :
        (∑ i, mass i * charge i.1) ≤ 0 :=
      Finset.sum_nonpos fun i _ => hnone i
    rw [hcharge] at hnonpos
    norm_num at hnonpos
  obtain ⟨selected, hselected⟩ := hselected
  exact ⟨{
    mass := mass
    mass_nonneg := hmass
    balance := hbalance
    charge_eq_one := hcharge
    selected := selected
    selected_charge_pos := hselected
  }⟩

theorem selected_mass_pos
    (C : EntryReachablePositiveChargedCirculation
      kernel source charge entry) :
    0 < C.mass C.selected := by
  have hcharge :
      0 < charge C.selected.1 :=
    pos_of_mul_pos_right C.selected_charge_pos
      (C.mass_nonneg C.selected)
  exact pos_of_mul_pos_left C.selected_charge_pos hcharge.le

theorem selected_charge_positive
    (C : EntryReachablePositiveChargedCirculation
      kernel source charge entry) :
    0 < charge C.selected.1 :=
  pos_of_mul_pos_right C.selected_charge_pos
    (C.mass_nonneg C.selected)

/-- The explicit selected source is reachable from the external entry. -/
theorem selectedSource_reachable
    (C : EntryReachablePositiveChargedCirculation
      kernel source charge entry) :
    AvailableReachable kernel source entry (source C.selected.1) :=
  C.selected.source_reachable kernel source entry

/-- The explicit selected source lies in the positive source support. -/
theorem selectedSource_mem_activeStates
    (C : EntryReachablePositiveChargedCirculation
      kernel source charge entry) :
    source C.selected.1 ∈
      occupationActiveStates
        (fun i : ReachableOccupationIndex kernel source entry =>
          source i.1)
        C.mass := by
  have hsource :
      0 <
        occupationSourceMass
          (fun i : ReachableOccupationIndex kernel source entry =>
            source i.1)
          C.mass (source C.selected.1) :=
    occupationSourceMass_pos_of_coordinate_pos
      (fun i : ReachableOccupationIndex kernel source entry =>
        source i.1)
      C.mass_nonneg C.selected_mass_pos
  simpa [occupationActiveStates] using hsource

/-- Every active source of the restricted circulation is reachable from the
external entry. -/
theorem activeState_reachable
    (C : EntryReachablePositiveChargedCirculation
      kernel source charge entry)
    (state :
      occupationActiveStates
        (fun i : ReachableOccupationIndex kernel source entry =>
          source i.1)
        C.mass) :
    AvailableReachable kernel source entry state.1 := by
  have hsourcePos :
      0 <
        occupationSourceMass
          (fun i : ReachableOccupationIndex kernel source entry =>
            source i.1)
          C.mass state.1 :=
    occupationActiveState_sourceMass_pos _ _ state
  have hindex :
      ∃ i : ReachableOccupationIndex kernel source entry,
        source i.1 = state.1 ∧ 0 < C.mass i := by
    by_contra hnone
    push Not at hnone
    have hnonpos :
        occupationSourceMass
            (fun i : ReachableOccupationIndex kernel source entry =>
              source i.1)
            C.mass state.1 ≤ 0 := by
      apply Finset.sum_nonpos
      intro i hi
      have hisource :
          source i.1 = state.1 :=
        (Finset.mem_filter.mp hi).2
      exact hnone i hisource
    exact (not_lt_of_ge hnonpos) hsourcePos
  obtain ⟨i, hisource, -⟩ := hindex
  rw [← hisource]
  exact i.source_reachable kernel source entry

/-- The positive source support is closed under the induced operational
kernel. -/
theorem operationalKernel_closed
    (C : EntryReachablePositiveChargedCirculation
      kernel source charge entry)
    (state :
      occupationActiveStates
        (fun i : ReachableOccupationIndex kernel source entry =>
          source i.1)
        C.mass)
    {destination : S}
    (hdestination :
      destination ∉
        occupationActiveStates
          (fun i : ReachableOccupationIndex kernel source entry =>
            source i.1)
          C.mass) :
    occupationOperationalKernel
        (fun i : ReachableOccupationIndex kernel source entry =>
          kernel i.1)
        (fun i : ReachableOccupationIndex kernel source entry =>
          source i.1)
        C.mass C.mass_nonneg
        (occupationActiveState_sourceMass_pos _ _ state)
        destination = 0 := by
  exact occupationOperationalKernel_eq_zero_of_not_active
    (fun i : ReachableOccupationIndex kernel source entry =>
      kernel i.1)
    (fun i : ReachableOccupationIndex kernel source entry =>
      source i.1)
    C.mass_nonneg C.balance
    (occupationActiveState_sourceMass_pos _ _ state)
    hdestination

end EntryReachablePositiveChargedCirculation

/-- A bounded discrepancy account for the entry-reachable operational
family. `scale` records the common rescaling of the original charges. -/
structure EntryReachableBoundedChargePotential
    [Fintype I]
    (kernel : I → PMF S) (source : I → S)
    (charge : I → ℝ) (entry : S) where
  potential : S → ℝ
  scale : ℝ
  scale_pos : 0 < scale
  bounded : ∀ state, 0 ≤ potential state ∧ potential state ≤ 1
  charge_le_discrepancy :
    ∀ i : ReachableOccupationIndex kernel source entry,
      charge i.1 / scale ≤
        expect (kernel i.1) potential - potential (source i.1)

/-- Every finite drift potential can be affinely normalized into `[0,1]`.
The constant shift cancels from every one-step discrepancy. -/
theorem exists_entryReachableBoundedChargePotential_of_drift
    [Finite S] [Fintype I]
    (kernel : I → PMF S) (source : I → S)
    (charge : I → ℝ) (entry : S)
    (h :
      ∃ potential : S → ℝ,
        ∀ i : ReachableOccupationIndex kernel source entry,
          charge i.1 ≤
            expect (kernel i.1) potential -
              potential (source i.1)) :
    Nonempty
      (EntryReachableBoundedChargePotential
        kernel source charge entry) := by
  letI : Fintype S := Fintype.ofFinite S
  obtain ⟨raw, hraw⟩ := h
  let bound : ℝ := ∑ state, |raw state| + 1
  have hbound : 0 < bound := by
    dsimp only [bound]
    positivity
  let scale : ℝ := 2 * bound
  have hscale : 0 < scale := mul_pos (by norm_num) hbound
  let potential : S → ℝ :=
    fun state => raw state / scale + 1 / 2
  have hbounded :
      ∀ state, 0 ≤ potential state ∧ potential state ≤ 1 := by
    intro state
    have habs :
        |raw state| ≤ ∑ other, |raw other| :=
      Finset.single_le_sum
        (fun other _ => abs_nonneg (raw other))
        (Finset.mem_univ state)
    have hlower : -bound ≤ raw state := by
      dsimp only [bound]
      linarith [neg_abs_le (raw state)]
    have hupper : raw state ≤ bound := by
      dsimp only [bound]
      linarith [le_abs_self (raw state)]
    have hdivLower : -(1 / 2 : ℝ) ≤ raw state / scale := by
      apply (le_div_iff₀ hscale).2
      dsimp only [scale]
      linarith
    have hdivUpper : raw state / scale ≤ (1 / 2 : ℝ) := by
      apply (div_le_iff₀ hscale).2
      dsimp only [scale]
      linarith
    dsimp only [potential]
    constructor <;> linarith
  refine ⟨{
    potential := potential
    scale := scale
    scale_pos := hscale
    bounded := hbounded
    charge_le_discrepancy := ?_
  }⟩
  intro i
  have hscaled :
      charge i.1 / scale ≤
        (expect (kernel i.1) raw - raw (source i.1)) / scale :=
    (div_le_div_iff_of_pos_right hscale).2 (hraw i)
  calc
    charge i.1 / scale ≤
        (expect (kernel i.1) raw - raw (source i.1)) / scale :=
      hscaled
    _ =
        expect (kernel i.1) potential -
          potential (source i.1) := by
      rw [show potential =
          fun state => (1 / scale) * raw state + 1 / 2 by
        funext state
        dsimp only [potential]
        ring]
      rw [expect_add, expect_const_mul, expect_const]
      ring

/-- **Entry-aware charged occupation alternative.**

Only operational transitions whose source is reachable from `entry` are
used. The circulation branch has a selected positive-charge entry and a
closed, entirely reachable active support. The potential branch is already
normalized for a bounded public discrepancy ledger. -/
theorem entryReachablePositiveChargedCirculation_or_boundedPotential
    [Fintype S] [Fintype I] [DecidableEq S]
    (kernel : I → PMF S) (source : I → S)
    (charge : I → ℝ) (entry : S) :
    Nonempty
        (EntryReachablePositiveChargedCirculation
          kernel source charge entry) ∨
      Nonempty
        (EntryReachableBoundedChargePotential
          kernel source charge entry) := by
  let reachableKernel :
      ReachableOccupationIndex kernel source entry → PMF S :=
    fun i => kernel i.1
  let reachableSource :
      ReachableOccupationIndex kernel source entry → S :=
    fun i => source i.1
  let reachableCharge :
      ReachableOccupationIndex kernel source entry → ℝ :=
    fun i => charge i.1
  have h :=
    normalizedPositiveChargedCirculation_xor_driftPotential
      reachableKernel reachableSource reachableCharge
  rw [xor_def] at h
  rcases h with ⟨hcirculation, -⟩ | ⟨hpotential, -⟩
  · exact Or.inl
      (EntryReachablePositiveChargedCirculation.of_hasNormalizedPositiveChargedCirculation
        hcirculation)
  · exact Or.inr
      (exists_entryReachableBoundedChargePotential_of_drift
        kernel source charge entry hpotential)

/-- An existing circulation survives entry restriction when all of its
positive mass is already supported on reachable source indices. -/
theorem restrict_positiveChargedCirculation_of_mass_support
    [Fintype S] [Fintype I] [DecidableEq S]
    (kernel : I → PMF S) (source : I → S)
    (charge : I → ℝ) (entry : S)
    (mass : I → ℝ)
    (hmass : ∀ i, 0 ≤ mass i)
    (hbalance :
      ∀ destination,
        ∑ i, mass i *
          actualOccupationColumn kernel source i destination = 0)
    (hcharge : ∑ i, mass i * charge i = 1)
    (hsupport :
      ∀ i, 0 < mass i →
        AvailableReachable kernel source entry (source i)) :
    HasNormalizedPositiveChargedCirculation
      (actualOccupationColumn
        (fun i : ReachableOccupationIndex kernel source entry =>
          kernel i.1)
        (fun i : ReachableOccupationIndex kernel source entry =>
          source i.1))
      (fun i : ReachableOccupationIndex kernel source entry =>
        charge i.1) := by
  let reachable :=
    reachableOccupationIndices kernel source entry
  let restrictedMass :
      ReachableOccupationIndex kernel source entry → ℝ :=
    fun i => mass i.1
  refine ⟨restrictedMass, fun i => hmass i.1, ?_, ?_⟩
  · intro destination
    have hzero :
        ∀ i ∉ reachable,
          mass i *
            actualOccupationColumn kernel source i destination = 0 := by
      intro i hi
      have hnotReachable :
          ¬AvailableReachable kernel source entry (source i) := by
        simpa [reachable, reachableOccupationIndices] using hi
      have hmassZero : mass i = 0 := by
        exact le_antisymm
          (not_lt.mp fun hpos => hnotReachable (hsupport i hpos))
          (hmass i)
      rw [hmassZero, zero_mul]
    calc
      (∑ i, restrictedMass i *
          actualOccupationColumn
            (fun j : ReachableOccupationIndex kernel source entry =>
              kernel j.1)
            (fun j : ReachableOccupationIndex kernel source entry =>
              source j.1)
            i destination) =
          ∑ i ∈ reachable,
            mass i *
              actualOccupationColumn kernel source i destination := by
            change
              (∑ i :
                  ↥(reachableOccupationIndices kernel source entry),
                mass i.1 *
                  actualOccupationColumn
                    kernel source i.1 destination) =
                ∑ i ∈ reachable,
                  mass i *
                    actualOccupationColumn
                      kernel source i destination
            simpa only [reachable] using
              (Finset.sum_subtype
                (reachableOccupationIndices kernel source entry)
                (fun _ => Iff.rfl)
                (fun i =>
                  mass i *
                    actualOccupationColumn
                      kernel source i destination)).symm
      _ =
          ∑ i, mass i *
            actualOccupationColumn kernel source i destination := by
          apply Finset.sum_subset (Finset.subset_univ _)
          intro i _ hi
          exact hzero i hi
      _ = 0 := hbalance destination
  · calc
      (∑ i, restrictedMass i * charge i.1) =
          ∑ i ∈ reachable, mass i * charge i := by
            change
              (∑ i :
                  ↥(reachableOccupationIndices kernel source entry),
                mass i.1 * charge i.1) =
                ∑ i ∈ reachable, mass i * charge i
            simpa only [reachable] using
              (Finset.sum_subtype
                (reachableOccupationIndices kernel source entry)
                (fun _ => Iff.rfl)
                (fun i => mass i * charge i)).symm
      _ = ∑ i, mass i * charge i := by
          apply Finset.sum_subset (Finset.subset_univ _)
          intro i _ hi
          have hnotReachable :
              ¬AvailableReachable kernel source entry (source i) := by
            simpa [reachable, reachableOccupationIndices] using hi
          have hmassZero : mass i = 0 := by
            exact le_antisymm
              (not_lt.mp fun hpos =>
                hnotReachable (hsupport i hpos))
              (hmass i)
          rw [hmassZero, zero_mul]
      _ = 1 := hcharge

namespace ChargeLossCounterexample

abbrev State := Bool
abbrev Index := Bool

def kernel (index : Index) : PMF State :=
  PMF.pure index

def source (index : Index) : State :=
  index

def charge (index : Index) : ℝ :=
  if index then 1 else 0

/-- The unrestricted family has unit positive charge in the unreachable
absorbing class `true`. -/
theorem unrestricted_positiveChargedCirculation :
    HasNormalizedPositiveChargedCirculation
      (actualOccupationColumn kernel source) charge := by
  refine ⟨fun i => if i then 1 else 0, ?_, ?_, ?_⟩
  · intro i
    cases i <;> norm_num
  · intro destination
    cases destination <;>
      norm_num [actualOccupationColumn, kernel, source]
  · norm_num [charge]

theorem availableSupportStep_eq
    {current next : State}
    (hstep : AvailableSupportStep kernel source current next) :
    current = next := by
  obtain ⟨index, hsource, hkernel⟩ := hstep
  have hnext : next = index := by
    simpa [kernel] using hkernel
  exact hsource.symm.trans hnext.symm

theorem eq_of_availableReachable
    {current next : State}
    (hreach : AvailableReachable kernel source current next) :
    current = next := by
  induction hreach using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head hstep _ ih =>
      exact (availableSupportStep_eq hstep).trans ih

theorem reachableIndex_eq_false
    (i : ReachableOccupationIndex kernel source false) :
    i.1 = false := by
  have hreach := i.source_reachable kernel source false
  simpa [source] using eq_of_availableReachable hreach

/-- After restricting to sources reachable from `false`, every remaining
charge is zero, so no positive charged circulation remains. -/
theorem no_restricted_positiveChargedCirculation :
    ¬HasNormalizedPositiveChargedCirculation
      (actualOccupationColumn
        (fun i : ReachableOccupationIndex kernel source false =>
          kernel i.1)
        (fun i : ReachableOccupationIndex kernel source false =>
          source i.1))
      (fun i : ReachableOccupationIndex kernel source false =>
        charge i.1) := by
  rintro ⟨mass, -, -, hcharge⟩
  have hzero :
      (∑ i : ReachableOccupationIndex kernel source false,
        mass i * charge i.1) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [reachableIndex_eq_false i]
    simp [charge]
  rw [hzero] at hcharge
  norm_num at hcharge

/-- Positive charge is genuinely lost by entry restriction. -/
theorem unrestricted_positive_but_restricted_not :
    HasNormalizedPositiveChargedCirculation
        (actualOccupationColumn kernel source) charge ∧
      ¬HasNormalizedPositiveChargedCirculation
        (actualOccupationColumn
          (fun i : ReachableOccupationIndex kernel source false =>
            kernel i.1)
          (fun i : ReachableOccupationIndex kernel source false =>
            source i.1))
        (fun i : ReachableOccupationIndex kernel source false =>
          charge i.1) :=
  ⟨unrestricted_positiveChargedCirculation,
    no_restricted_positiveChargedCirculation⟩

end ChargeLossCounterexample

end Probability
end Math
