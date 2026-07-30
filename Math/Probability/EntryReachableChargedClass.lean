/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability.EntryReachableChargedOccupation
import Math.Probability.HarmonicClosedClass
import Math.Probability.StationaryCommunicatingClass
import Mathlib.Data.Fintype.Quotient

/-!
# Positive communicating classes of entry-reachable occupations

An entry-reachable positive charged circulation induces a finite Markov
kernel on its positive source support.  Its normalized source mass is a
full-support invariant law, so every active state is recurrent and the
active kernel splits into closed communicating classes.

The total stationary charge is the sum of the charges of these classes.
Thus at least one class has positive aggregate charge.  This is stronger
than selecting a single positive transition: negative contributions in
the same class are included before the class is selected.
-/

set_option autoImplicit false

noncomputable section

namespace Math
namespace Probability

open Finset BigOperators

variable {S I : Type*}

namespace EntryReachablePositiveChargedCirculation

variable [Fintype S] [Fintype I] [DecidableEq S]
  {kernel : I → PMF S} {source : I → S}
  {charge : I → ℝ} {entry : S}

abbrev ActiveState
    (C : EntryReachablePositiveChargedCirculation
      kernel source charge entry) :=
  occupationActiveStates
    (fun i : ReachableOccupationIndex kernel source entry =>
      source i.1)
    C.mass

/-- The explicit form of balance needed by the occupation realization
theorems. -/
theorem balance_explicit
    (C : EntryReachablePositiveChargedCirculation
      kernel source charge entry) :
    ∀ destination,
      ∑ i, C.mass i *
        ((kernel i.1 destination).toReal -
          if destination = source i.1 then 1 else 0) = 0 := by
  intro destination
  simpa [actualOccupationColumn] using C.balance destination

/-- A positive selected coordinate makes the total occupation mass
strictly positive. -/
theorem totalMass_pos
    (C : EntryReachablePositiveChargedCirculation
      kernel source charge entry) :
    0 < occupationTotalMass C.mass :=
  occupationTotalMass_pos_of_coordinate_pos
    C.mass_nonneg C.selected_mass_pos

/-- The induced Markov kernel on the positive source support. -/
def activeKernel
    (C : EntryReachablePositiveChargedCirculation
      kernel source charge entry) :
    ActiveState C → PMF (ActiveState C) :=
  occupationActiveKernel
    (fun i : ReachableOccupationIndex kernel source entry =>
      kernel i.1)
    (fun i : ReachableOccupationIndex kernel source entry =>
      source i.1)
    C.mass C.mass_nonneg C.balance_explicit

/-- The invariant law of the induced active kernel. -/
def activeInvariant
    (C : EntryReachablePositiveChargedCirculation
      kernel source charge entry) :
    PMF (ActiveState C) :=
  occupationInvariantPMF
    (fun i : ReachableOccupationIndex kernel source entry =>
      source i.1)
    C.mass C.mass_nonneg C.totalMass_pos

@[simp]
theorem activeInvariant_toReal
    (C : EntryReachablePositiveChargedCirculation
      kernel source charge entry)
    (state : ActiveState C) :
    (C.activeInvariant state).toReal =
      occupationSourceMass
          (fun i : ReachableOccupationIndex kernel source entry =>
            source i.1)
          C.mass state.1 /
        occupationTotalMass C.mass := by
  exact occupationInvariantPMF_toReal
    (fun i : ReachableOccupationIndex kernel source entry =>
      source i.1)
    C.mass C.mass_nonneg C.totalMass_pos state

theorem activeInvariant_pos
    (C : EntryReachablePositiveChargedCirculation
      kernel source charge entry)
    (state : ActiveState C) :
    0 < (C.activeInvariant state).toReal := by
  rw [C.activeInvariant_toReal state]
  exact div_pos
    (occupationActiveState_sourceMass_pos _ _ state)
    C.totalMass_pos

theorem activeInvariant_stationary
    (C : EntryReachablePositiveChargedCirculation
      kernel source charge entry) :
    ∀ destination,
      ∑ state,
          (C.activeInvariant state).toReal *
            (C.activeKernel state destination).toReal =
        (C.activeInvariant destination).toReal := by
  exact occupationInvariantPMF_stationary
    (fun i : ReachableOccupationIndex kernel source entry =>
      kernel i.1)
    (fun i : ReachableOccupationIndex kernel source entry =>
      source i.1)
    C.mass_nonneg C.totalMass_pos C.balance_explicit

/-- Stationary charge contributed by one active state. -/
def activeStateCharge
    (C : EntryReachablePositiveChargedCirculation
      kernel source charge entry)
    (state : ActiveState C) : ℝ :=
  (C.activeInvariant state).toReal *
    ∑ i : occupationSourceFiber
        (fun j : ReachableOccupationIndex kernel source entry =>
          source j.1)
        state.1,
      (occupationPolicyPMF
        (fun j : ReachableOccupationIndex kernel source entry =>
          source j.1)
        C.mass C.mass_nonneg
        (occupationActiveState_sourceMass_pos _ _ state) i).toReal *
        charge i.1.1

/-- Total stationary charge of the active kernel is positive. -/
theorem sum_activeStateCharge_pos
    (C : EntryReachablePositiveChargedCirculation
      kernel source charge entry) :
    0 < ∑ state, C.activeStateCharge state := by
  apply occupationInvariantPMF_policyReward_pos
    (fun i : ReachableOccupationIndex kernel source entry =>
      source i.1)
    C.mass_nonneg C.totalMass_pos
    (fun i : ReachableOccupationIndex kernel source entry =>
      charge i.1)
  rw [C.charge_eq_one]
  norm_num

/-- Aggregate stationary charge of the communication class containing
`representative`. -/
def communicationClassCharge
    (C : EntryReachablePositiveChargedCirculation
      kernel source charge entry)
    (representative : ActiveState C) : ℝ :=
  ∑ state ∈ pmfCommunicationClass
      C.activeKernel representative,
    C.activeStateCharge state

/-- A closed communicating class with positive aggregate stationary charge,
together with its entry path from the external state. -/
structure PositiveCommunicatingClass
    (C : EntryReachablePositiveChargedCirculation
      kernel source charge entry) where
  representative : ActiveState C
  charge_pos : 0 < C.communicationClassCharge representative
  closedClass :
    ReachableClosedClass C.activeKernel representative
  closedClass_entry : closedClass.entry = representative
  reachable_from_external :
    AvailableReachable kernel source entry representative.1

/-- Every active state supplies a closed communicating class. -/
def closedClassAt
    (C : EntryReachablePositiveChargedCirculation
      kernel source charge entry)
    (state : ActiveState C) :
    ReachableClosedClass C.activeKernel state :=
  reachableClosedClass_of_stationary_fullSupport
    C.activeKernel
    (fun active => (C.activeInvariant active).toReal)
    C.activeInvariant_pos C.activeInvariant_stationary state

/-- Communication classes partition the positive total stationary charge,
so one class has positive aggregate charge. -/
theorem exists_positiveCommunicatingClass
    (C : EntryReachablePositiveChargedCirculation
      kernel source charge entry) :
    Nonempty (PositiveCommunicatingClass C) := by
  classical
  let communication :=
    pmfCommunicatesSetoid C.activeKernel
  letI :
      DecidableRel
        ((communication : Setoid (ActiveState C)).r) :=
    Classical.decRel _
  let Class := Quotient communication
  let classCharge : Class → ℝ :=
    fun component =>
      ∑ state : ActiveState C,
        if component = Quotient.mk'' state then
          C.activeStateCharge state
        else 0
  have hsum :
      (∑ component : Class, classCharge component) =
        ∑ state, C.activeStateCharge state := by
    dsimp only [classCharge]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro state _
    rw [Fintype.sum_eq_single (Quotient.mk'' state)]
    · simp
    · intro component hcomponent
      simp [hcomponent]
  have hsumPos :
      0 < ∑ component : Class, classCharge component := by
    rw [hsum]
    exact C.sum_activeStateCharge_pos
  have hexists :
      ∃ component : Class, 0 < classCharge component := by
    by_contra hnone
    push Not at hnone
    have hnonpos :
        (∑ component : Class, classCharge component) ≤ 0 :=
      Finset.sum_nonpos fun component _ => hnone component
    exact (not_lt_of_ge hnonpos) hsumPos
  obtain ⟨component, hclass⟩ := hexists
  let representative : ActiveState C := Quotient.out component
  have hclass_eq :
      classCharge component =
        C.communicationClassCharge representative := by
    dsimp only [classCharge, communicationClassCharge,
      pmfCommunicationClass]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro state _
    have hequivalent :
        component = Quotient.mk'' state ↔
          PMFCommunicates C.activeKernel representative state := by
      rw [← Quotient.out_eq' component, Quotient.eq'']
      rfl
    by_cases hstate :
        PMFCommunicates C.activeKernel representative state
    · simp [hstate, hequivalent.mpr hstate]
    · have hquotient :
          component ≠ Quotient.mk'' state :=
        fun h => hstate (hequivalent.mp h)
      simp [hstate, hquotient]
  have hcharge :
      0 < C.communicationClassCharge representative := by
    rw [← hclass_eq]
    exact hclass
  have hreachable :
      AvailableReachable kernel source entry representative.1 :=
    C.activeState_reachable representative
  exact ⟨{
    representative := representative
    charge_pos := hcharge
    closedClass := C.closedClassAt representative
    closedClass_entry := rfl
    reachable_from_external := hreachable
  }⟩

namespace PositiveCommunicatingClass

/-- A payoff vector harmonic on the selected positive class agrees with its
whole-vector value at the class representative. -/
theorem harmonicVector_eq_representative
    {Player : Type*}
    (C : EntryReachablePositiveChargedCirculation
      kernel source charge entry)
    (P : PositiveCommunicatingClass C)
    (value : ActiveState C → Player → ℝ)
    (harmonic :
      ∀ state, state ∈ P.closedClass.states →
        ∀ player,
          value state player =
            expect (C.activeKernel state)
              (fun next => value next player))
    {state : ActiveState C}
    (hstate : state ∈ P.closedClass.states) :
    value state = value P.representative := by
  have hvalue :=
    P.closedClass.harmonicVector_eq_entry
      value harmonic hstate
  rwa [P.closedClass_entry] at hvalue

end PositiveCommunicatingClass

end EntryReachablePositiveChargedCirculation

end Probability
end Math
