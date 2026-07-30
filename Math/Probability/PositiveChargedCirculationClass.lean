/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability.EntryReachableChargedClass

/-!
# Positive-charge classes of finite occupation circulations

A normalized charged circulation induces a stationary operational kernel on
its positive source support.  The communicating classes of that kernel
partition its stationary charge, whose total is one.  Hence one class has
strictly positive aggregate charge for the original charge function.

The returned entry is internal: it is a positive-mass source in the selected
class, and every state of the class is reachable from it under the induced
operational kernel.  No supplied external state is asserted to reach this
entry.  That stronger implication is false, as shown by
`PositiveCirculationNotReachable.circulation_and_closed_but_not_reachable`
and `ChargeLossCounterexample.unrestricted_positive_but_restricted_not`.
-/

set_option autoImplicit false

noncomputable section

namespace Math
namespace Probability

open Finset BigOperators

variable {S I : Type*}

/-- Coordinate form of balance expected by the occupation-kernel
constructor. -/
theorem actualOccupationBalance_explicit
    [Fintype I] [DecidableEq S]
    (kernel : I → PMF S) (source : I → S) (mass : I → ℝ)
    (balance :
      ∀ destination,
        ∑ index, mass index *
          actualOccupationColumn kernel source index destination = 0) :
    ∀ destination,
      ∑ index, mass index *
        ((kernel index destination).toReal -
          if destination = source index then 1 else 0) = 0 := by
  simpa only [actualOccupationColumn] using balance

/-- Original mass-weighted charge contributed by indices at one source
state. -/
def occupationSourceCharge
    [Fintype I] [DecidableEq S]
    (source : I → S) (charge mass : I → ℝ) (state : S) : ℝ :=
  ∑ index ∈ Finset.univ.filter (fun index => source index = state),
    mass index * charge index

/-- Stationary charge contributed at one positive-mass source state. -/
def occupationActiveStateCharge
    [Fintype S] [Fintype I] [DecidableEq S]
    (source : I → S) (charge mass : I → ℝ)
    (mass_nonneg : ∀ index, 0 ≤ mass index)
    (total_pos : 0 < occupationTotalMass mass)
    (state : occupationActiveStates source mass) : ℝ :=
  (occupationInvariantPMF
      source mass mass_nonneg total_pos state).toReal *
    ∑ index : occupationSourceFiber source state.1,
      (occupationPolicyPMF source mass mass_nonneg
        (occupationActiveState_sourceMass_pos source mass state)
        index).toReal *
      charge index.1

/-- The stationary charge at one active source is its original
mass-weighted source charge divided by the total circulation mass. -/
theorem occupationActiveStateCharge_eq_sourceCharge_div
    [Fintype S] [Fintype I] [DecidableEq S]
    (source : I → S) (charge mass : I → ℝ)
    (mass_nonneg : ∀ index, 0 ≤ mass index)
    (total_pos : 0 < occupationTotalMass mass)
    (state : occupationActiveStates source mass) :
    occupationActiveStateCharge
        source charge mass mass_nonneg total_pos state =
      occupationSourceCharge source charge mass state.1 /
        occupationTotalMass mass := by
  rw [occupationActiveStateCharge,
    occupationInvariantPMF_toReal,
    occupationPolicy_reward_eq_conditional]
  rw [div_mul_eq_mul_div, Finset.mul_sum]
  congr 1
  rw [occupationSourceCharge]
  calc
    (∑ index,
        occupationSourceMass source mass state.1 *
          (occupationConditionalWeight source mass state.1 index *
            charge index)) =
        ∑ index,
          (if source index = state.1 then mass index else 0) *
            charge index := by
      apply Finset.sum_congr rfl
      intro index _
      rw [← mul_assoc,
        occupationSourceMass_mul_conditionalWeight
          source mass_nonneg]
    _ =
        ∑ index ∈
          Finset.univ.filter
            (fun index => source index = state.1),
          mass index * charge index := by
      simp [Finset.sum_filter]

/-- Aggregate original charge of one communication class of the induced
operational kernel. -/
def occupationCommunicationClassCharge
    [Fintype S] [Fintype I] [DecidableEq S]
    (kernel : I → PMF S) (source : I → S)
    (charge mass : I → ℝ)
    (mass_nonneg : ∀ index, 0 ≤ mass index)
    (total_pos : 0 < occupationTotalMass mass)
    (balance :
      ∀ destination,
        ∑ index, mass index *
          actualOccupationColumn kernel source index destination = 0)
    (representative : occupationActiveStates source mass) : ℝ :=
  ∑ state ∈
      pmfCommunicationClass
        (occupationActiveKernel
          kernel source mass mass_nonneg
          (actualOccupationBalance_explicit
            kernel source mass balance))
        representative,
    occupationActiveStateCharge
      source charge mass mass_nonneg total_pos state

/-- Raw original mass-weighted charge of one communication class. -/
def occupationCommunicationClassOriginalCharge
    [Fintype S] [Fintype I] [DecidableEq S]
    (kernel : I → PMF S) (source : I → S)
    (charge mass : I → ℝ)
    (mass_nonneg : ∀ index, 0 ≤ mass index)
    (balance :
      ∀ destination,
        ∑ index, mass index *
          actualOccupationColumn kernel source index destination = 0)
    (representative : occupationActiveStates source mass) : ℝ :=
  ∑ state ∈
      pmfCommunicationClass
        (occupationActiveKernel
          kernel source mass mass_nonneg
          (actualOccupationBalance_explicit
            kernel source mass balance))
        representative,
    occupationSourceCharge source charge mass state.1

/-- Class stationary charge is exactly raw original class charge divided
by total circulation mass. -/
theorem occupationCommunicationClassCharge_eq_original_div
    [Fintype S] [Fintype I] [DecidableEq S]
    (kernel : I → PMF S) (source : I → S)
    (charge mass : I → ℝ)
    (mass_nonneg : ∀ index, 0 ≤ mass index)
    (total_pos : 0 < occupationTotalMass mass)
    (balance :
      ∀ destination,
        ∑ index, mass index *
          actualOccupationColumn kernel source index destination = 0)
    (representative : occupationActiveStates source mass) :
    occupationCommunicationClassCharge
        kernel source charge mass mass_nonneg total_pos
        balance representative =
      occupationCommunicationClassOriginalCharge
        kernel source charge mass mass_nonneg
        balance representative /
          occupationTotalMass mass := by
  rw [occupationCommunicationClassCharge,
    occupationCommunicationClassOriginalCharge, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro state _
  exact occupationActiveStateCharge_eq_sourceCharge_div
    source charge mass mass_nonneg total_pos state

/-- A positive aggregate-charge communicating class extracted from one
normalized charged circulation.

`closedClass` is reachable from `representative` because its initial state
is that same internal representative.  There is deliberately no external
entry field. -/
structure PositiveChargedCirculationClass
    [Fintype S] [Fintype I] [DecidableEq S]
    (kernel : I → PMF S) (source : I → S) (charge : I → ℝ) where
  mass : I → ℝ
  mass_nonneg : ∀ index, 0 ≤ mass index
  balance :
    ∀ destination,
      ∑ index, mass index *
        actualOccupationColumn kernel source index destination = 0
  charge_eq_one : ∑ index, mass index * charge index = 1
  total_pos : 0 < occupationTotalMass mass
  representative : occupationActiveStates source mass
  class_charge_pos :
    0 <
      occupationCommunicationClassCharge
        kernel source charge mass mass_nonneg total_pos
        balance representative
  original_class_charge_pos :
    0 <
      occupationCommunicationClassOriginalCharge
        kernel source charge mass mass_nonneg
        balance representative
  closedClass :
    ReachableClosedClass
      (occupationActiveKernel
        kernel source mass mass_nonneg
        (actualOccupationBalance_explicit
          kernel source mass balance))
      representative
  closedClass_entry : closedClass.entry = representative

/-- Every normalized finite charged circulation has a communicating class
with strictly positive aggregate charge for its original charge function.

The proof decomposes the induced stationary operational kernel into its
finite communication classes and uses that their aggregate charges sum to
the normalized total charge one. -/
theorem HasNormalizedPositiveChargedCirculation.exists_positiveChargedClass
    [Fintype S] [Fintype I] [DecidableEq S]
    (kernel : I → PMF S) (source : I → S) (charge : I → ℝ)
    (circulation :
      HasNormalizedPositiveChargedCirculation
        (actualOccupationColumn kernel source) charge) :
    Nonempty
      (PositiveChargedCirculationClass kernel source charge) := by
  classical
  obtain ⟨mass, mass_nonneg, balance, charge_eq_one⟩ := circulation
  have hpositiveSummand :
      ∃ index, 0 < mass index * charge index := by
    by_contra hnone
    push Not at hnone
    have hnonpos :
        (∑ index, mass index * charge index) ≤ 0 :=
      Finset.sum_nonpos fun index _ => hnone index
    rw [charge_eq_one] at hnonpos
    norm_num at hnonpos
  obtain ⟨positiveIndex, hpositiveIndex⟩ := hpositiveSummand
  have hpositiveCharge : 0 < charge positiveIndex :=
    pos_of_mul_pos_right hpositiveIndex
      (mass_nonneg positiveIndex)
  have hpositiveMass : 0 < mass positiveIndex :=
    pos_of_mul_pos_left hpositiveIndex hpositiveCharge.le
  have total_pos : 0 < occupationTotalMass mass :=
    occupationTotalMass_pos_of_coordinate_pos
      mass_nonneg hpositiveMass
  let activeKernel :
      occupationActiveStates source mass →
        PMF (occupationActiveStates source mass) :=
    occupationActiveKernel kernel source mass mass_nonneg
      (actualOccupationBalance_explicit
        kernel source mass balance)
  let activeInvariant :
      PMF (occupationActiveStates source mass) :=
    occupationInvariantPMF source mass mass_nonneg total_pos
  have activeInvariant_pos :
      ∀ state, 0 < (activeInvariant state).toReal := by
    intro state
    rw [show
      (activeInvariant state).toReal =
        occupationSourceMass source mass state.1 /
          occupationTotalMass mass by
      exact occupationInvariantPMF_toReal
        source mass mass_nonneg total_pos state]
    exact div_pos
      (occupationActiveState_sourceMass_pos source mass state)
      total_pos
  have activeInvariant_stationary :
      ∀ destination,
        (∑ state,
          (activeInvariant state).toReal *
            (activeKernel state destination).toReal) =
          (activeInvariant destination).toReal := by
    intro destination
    exact occupationInvariantPMF_stationary
      kernel source mass_nonneg total_pos
      (actualOccupationBalance_explicit
        kernel source mass balance)
      destination
  let communication :=
    pmfCommunicatesSetoid activeKernel
  letI :
      DecidableRel
        ((communication :
          Setoid (occupationActiveStates source mass)).r) :=
    Classical.decRel _
  let Class := Quotient communication
  let classCharge : Class → ℝ := fun component =>
    ∑ state : occupationActiveStates source mass,
      if component = Quotient.mk'' state then
        occupationActiveStateCharge
          source charge mass mass_nonneg total_pos state
      else 0
  have hsum :
      (∑ component : Class, classCharge component) =
        ∑ state,
          occupationActiveStateCharge
            source charge mass mass_nonneg total_pos state := by
    dsimp only [classCharge]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro state _
    rw [Fintype.sum_eq_single (Quotient.mk'' state)]
    · simp
    · intro component hcomponent
      simp [hcomponent]
  have htotalCharge :
      0 <
        ∑ state,
          occupationActiveStateCharge
            source charge mass mass_nonneg total_pos state := by
    simpa only [occupationActiveStateCharge] using
      occupationInvariantPMF_policyReward_pos
        source mass_nonneg total_pos charge
        (by rw [charge_eq_one]; norm_num)
  have hsumPos : 0 < ∑ component : Class, classCharge component := by
    rw [hsum]
    exact htotalCharge
  have hexists :
      ∃ component : Class, 0 < classCharge component := by
    by_contra hnone
    push Not at hnone
    have hnonpos :
        (∑ component : Class, classCharge component) ≤ 0 :=
      Finset.sum_nonpos fun component _ => hnone component
    exact (not_lt_of_ge hnonpos) hsumPos
  obtain ⟨component, hcomponent⟩ := hexists
  let representative : occupationActiveStates source mass :=
    Quotient.out component
  have hclassCharge :
      classCharge component =
        occupationCommunicationClassCharge
          kernel source charge mass mass_nonneg total_pos
          balance representative := by
    change
      (∑ state,
        if component = Quotient.mk'' state then
          occupationActiveStateCharge
            source charge mass mass_nonneg total_pos state
        else 0) =
      ∑ state ∈ pmfCommunicationClass
          activeKernel representative,
        occupationActiveStateCharge
          source charge mass mass_nonneg total_pos state
    have hclassSet :
        pmfCommunicationClass activeKernel representative =
          Finset.univ.filter
            (PMFCommunicates activeKernel representative) := by
      ext state
      simp [mem_pmfCommunicationClass_iff]
    rw [hclassSet, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro state _
    have hequivalent :
        component = Quotient.mk'' state ↔
          PMFCommunicates activeKernel representative state := by
      rw [← Quotient.out_eq' component, Quotient.eq'']
      rfl
    by_cases hstate :
        PMFCommunicates activeKernel representative state
    · simp [hstate, hequivalent.mpr hstate]
    · have hquotient :
          component ≠ Quotient.mk'' state :=
        fun h => hstate (hequivalent.mp h)
      simp [hstate, hquotient]
  have class_charge_pos :
      0 <
        occupationCommunicationClassCharge
          kernel source charge mass mass_nonneg total_pos
          balance representative := by
    rw [← hclassCharge]
    exact hcomponent
  have original_class_charge_pos :
      0 <
        occupationCommunicationClassOriginalCharge
          kernel source charge mass mass_nonneg
          balance representative := by
    have hquotient :
        0 <
          occupationCommunicationClassOriginalCharge
            kernel source charge mass mass_nonneg
            balance representative /
              occupationTotalMass mass := by
      rw [← occupationCommunicationClassCharge_eq_original_div]
      exact class_charge_pos
    rcases (div_pos_iff.mp hquotient) with hpos | hneg
    · exact hpos.1
    · exact False.elim ((not_lt_of_ge total_pos.le) hneg.2)
  let closedClass :
      ReachableClosedClass activeKernel representative :=
    reachableClosedClass_of_stationary_fullSupport
      activeKernel
      (fun state => (activeInvariant state).toReal)
      activeInvariant_pos activeInvariant_stationary representative
  exact ⟨{
    mass := mass
    mass_nonneg := mass_nonneg
    balance := balance
    charge_eq_one := charge_eq_one
    total_pos := total_pos
    representative := representative
    class_charge_pos := class_charge_pos
    original_class_charge_pos := original_class_charge_pos
    closedClass := closedClass
    closedClass_entry := rfl
  }⟩

namespace PositiveChargedCirculationClass

variable [Fintype S] [Fintype I] [DecidableEq S]
  {kernel : I → PMF S} {source : I → S} {charge : I → ℝ}

/-- The internal representative is the source of an original transition
carrying positive occupation mass. -/
theorem exists_positive_index_at_representative
    (C : PositiveChargedCirculationClass kernel source charge) :
    ∃ index, source index = C.representative.1 ∧
      0 < C.mass index := by
  have hsourceMass :
      0 <
        occupationSourceMass
          source C.mass C.representative.1 :=
    occupationActiveState_sourceMass_pos
      source C.mass C.representative
  by_contra hnone
  push Not at hnone
  have hnonpos :
      occupationSourceMass
          source C.mass C.representative.1 ≤ 0 := by
    apply Finset.sum_nonpos
    intro index hindex
    have hsource :
        source index = C.representative.1 :=
      (Finset.mem_filter.mp hindex).2
    exact hnone index hsource
  exact (not_lt_of_ge hnonpos) hsourceMass

/-- Every state of the selected class is reachable from its internal
positive-mass representative under the induced operational kernel. -/
theorem reachable_from_representative
    (C : PositiveChargedCirculationClass kernel source charge)
    {state : occupationActiveStates source C.mass}
    (hstate : state ∈ C.closedClass.states) :
    PMFReachable
      (occupationActiveKernel
        kernel source C.mass C.mass_nonneg
        (actualOccupationBalance_explicit
          kernel source C.mass C.balance))
      C.representative state := by
  apply C.closedClass.communicates
  · simpa only [C.closedClass_entry] using
      C.closedClass.entry_mem
  · exact hstate

end PositiveChargedCirculationClass

end Probability
end Math
