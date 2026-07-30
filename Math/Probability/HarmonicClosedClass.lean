/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability.ReachableClosedClass

/-!
# Harmonic values on finite closed communicating classes

The finite maximum principle says that a real-valued function harmonic for
a Markov kernel is constant on every finite closed communicating class.
Applying the scalar statement coordinatewise transports an entire finite or
infinite payoff vector; no positivity of an occupation charge is involved.
-/

set_option autoImplicit false

noncomputable section

namespace Math
namespace Probability

open Finset BigOperators

variable {S Player : Type*}

namespace ReachableClosedClass

variable [Fintype S] [DecidableEq S]
  {kernel : S → PMF S} {initial : S}

/-- Repoint a closed communicating class at any other state in the same
class. The external reachability path is extended inside the class. -/
def repoint
    (C : ReachableClosedClass kernel initial)
    (newEntry : S) (hnewEntry : newEntry ∈ C.states) :
    ReachableClosedClass kernel initial where
  states := C.states
  states_nonempty := C.states_nonempty
  closed := C.closed
  communicates := C.communicates
  entry := newEntry
  entry_mem := hnewEntry
  reachable_entry :=
    C.reachable_entry.trans
      (C.communicates C.entry_mem hnewEntry)

/-- At a maximum of a harmonic function on a closed finite set, every
positive-probability successor has the same value. -/
private theorem value_eq_max_of_supportStep
    (C : ReachableClosedClass kernel initial)
    (value : S → ℝ)
    (hharmonic :
      ∀ state, state ∈ C.states →
        value state = expect (kernel state) value)
    (maximum current next : S)
    (hmaximum :
      ∀ state, state ∈ C.states →
        value state ≤ value maximum)
    (hcurrent : current ∈ C.states)
    (hcurrentValue : value current = value maximum)
    (hstep : PMFSupportStep kernel current next) :
    value next = value maximum := by
  let clipped : S → ℝ :=
    fun state =>
      if state ∈ C.states then value state else value maximum
  have hnext : next ∈ C.states :=
    C.closed hcurrent hstep
  have hclipped_le :
      ∀ state, clipped state ≤ value maximum := by
    intro state
    by_cases hstate : state ∈ C.states
    · simpa [clipped, hstate] using hmaximum state hstate
    · simp [clipped, hstate]
  have hexpect_eq :
      expect (kernel current) clipped =
        expect (kernel current) value := by
    rw [expect_eq_sum, expect_eq_sum]
    apply Finset.sum_congr rfl
    intro state _
    by_cases hstate : state ∈ C.states
    · simp [clipped, hstate]
    · have hkernelZero : kernel current state = 0 := by
        by_contra hkernel
        exact hstate (C.closed hcurrent hkernel)
      simp [clipped, hstate, hkernelZero]
  have hexpect :
      expect (kernel current) clipped = value maximum := by
    rw [hexpect_eq, ← hharmonic current hcurrent,
      hcurrentValue]
  have hclippedNext :
      clipped next = value maximum := by
    apply le_antisymm (hclipped_le next)
    by_contra hnot
    have hlt : clipped next < value maximum :=
      lt_of_not_ge hnot
    have hstrict :=
      expect_lt_const_of_le_of_exists_lt
        (kernel current) clipped hclipped_le
        ⟨next, hstep, hlt⟩
    linarith
  simpa [clipped, hnext] using hclippedNext

/-- A scalar function harmonic on a finite closed communicating class is
constant there. -/
theorem harmonic_eq_on_class
    (C : ReachableClosedClass kernel initial)
    (value : S → ℝ)
    (hharmonic :
      ∀ state, state ∈ C.states →
        value state = expect (kernel state) value) :
    ∀ ⦃left⦄, left ∈ C.states →
      ∀ ⦃right⦄, right ∈ C.states →
        value left = value right := by
  obtain ⟨maximum, hmaximumMem, hmaximum⟩ :=
    Finset.exists_max_image C.states value C.states_nonempty
  have hvalueReachable :
      ∀ {state},
        PMFReachable kernel maximum state →
          state ∈ C.states ∧ value state = value maximum := by
    intro state hreach
    induction hreach with
    | refl =>
        exact ⟨hmaximumMem, rfl⟩
    | tail hprefix hstep ih =>
        have hstate : _ ∈ C.states :=
          C.closed ih.1 hstep
        have hvalue :
            value _ = value maximum :=
          value_eq_max_of_supportStep
            C value hharmonic maximum _ _
            hmaximum ih.1 ih.2 hstep
        exact ⟨hstate, hvalue⟩
  intro left hleft right hright
  have hleftValue :=
    (hvalueReachable
      (C.communicates hmaximumMem hleft)).2
  have hrightValue :=
    (hvalueReachable
      (C.communicates hmaximumMem hright)).2
  exact hleftValue.trans hrightValue.symm

/-- A vector-valued function harmonic coordinatewise on a finite closed
communicating class is constant there as a whole vector. -/
theorem harmonicVector_eq_on_class
    (C : ReachableClosedClass kernel initial)
    (value : S → Player → ℝ)
    (hharmonic :
      ∀ state, state ∈ C.states →
        ∀ player,
          value state player =
            expect (kernel state)
              (fun next => value next player)) :
    ∀ ⦃left⦄, left ∈ C.states →
      ∀ ⦃right⦄, right ∈ C.states →
        value left = value right := by
  intro left hleft right hright
  funext player
  exact C.harmonic_eq_on_class
    (fun state => value state player)
    (fun state hstate => hharmonic state hstate player)
    hleft hright

/-- In particular, a harmonic payoff vector agrees with its value at the
distinguished class entry everywhere in the class. -/
theorem harmonicVector_eq_entry
    (C : ReachableClosedClass kernel initial)
    (value : S → Player → ℝ)
    (hharmonic :
      ∀ state, state ∈ C.states →
        ∀ player,
          value state player =
            expect (kernel state)
              (fun next => value next player))
    {state : S} (hstate : state ∈ C.states) :
    value state = value C.entry :=
  C.harmonicVector_eq_on_class value hharmonic
    hstate C.entry_mem

end ReachableClosedClass

end Probability
end Math
