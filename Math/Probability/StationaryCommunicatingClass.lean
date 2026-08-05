/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability.ReachableClosedClass

/-!
# Communicating classes under a full-support invariant law

A finite Markov kernel admitting a stationary law with strictly positive
mass at every state has no transient states.  Equivalently, every support
edge can be followed by a support path back to its source.  Consequently,
the mutual-reachability class of any state is closed.

The results here isolate the finite Markov-chain fact needed to decompose a
positive occupation circulation into closed communicating classes.
-/

noncomputable section

namespace Math
namespace Probability

open Finset BigOperators

variable {S : Type*}

/-- Mutual support reachability for a Markov kernel. -/
def PMFCommunicates (kernel : S → PMF S) (source destination : S) : Prop :=
  PMFReachable kernel source destination ∧
    PMFReachable kernel destination source

/-- Mutual support reachability is an equivalence relation. -/
def pmfCommunicatesSetoid (kernel : S → PMF S) : Setoid S where
  r := PMFCommunicates kernel
  iseqv := {
    refl := fun _ =>
      ⟨Relation.ReflTransGen.refl,
        Relation.ReflTransGen.refl⟩
    symm := fun h => h.symm
    trans := fun h₁ h₂ =>
      ⟨h₁.1.trans h₂.1, h₂.2.trans h₁.2⟩
  }

/-- The finite mutual-reachability class of a state. -/
noncomputable def pmfCommunicationClass
    [Fintype S] (kernel : S → PMF S) (state : S) : Finset S := by
  classical
  exact Finset.univ.filter fun other =>
    PMFCommunicates kernel state other

theorem mem_pmfCommunicationClass_iff
    [Fintype S] (kernel : S → PMF S) (state other : S) :
    other ∈ pmfCommunicationClass kernel state ↔
      PMFCommunicates kernel state other := by
  classical
  simp [pmfCommunicationClass]

theorem self_mem_pmfCommunicationClass
    [Fintype S] (kernel : S → PMF S) (state : S) :
    state ∈ pmfCommunicationClass kernel state := by
  classical
  apply (mem_pmfCommunicationClass_iff kernel state state).mpr
  exact
    ⟨Relation.ReflTransGen.refl,
      Relation.ReflTransGen.refl⟩

/-- Coordinatewise stationarity implies equality of expectations. -/
theorem stationary_expectation
    [Fintype S]
    (kernel : S → PMF S) (weight : S → ℝ)
    (hstationary :
      ∀ destination,
        ∑ source, weight source *
            (kernel source destination).toReal =
          weight destination)
    (observable : S → ℝ) :
    (∑ source, weight source *
        expect (kernel source) observable) =
      ∑ state, weight state * observable state := by
  calc
    (∑ source, weight source *
        expect (kernel source) observable) =
        ∑ source, ∑ destination,
          weight source *
            (kernel source destination).toReal *
              observable destination := by
      apply Finset.sum_congr rfl
      intro source _
      rw [expect_eq_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro destination _
      ring
    _ =
        ∑ destination, ∑ source,
          weight source *
            (kernel source destination).toReal *
              observable destination :=
      Finset.sum_comm
    _ =
        ∑ destination,
          (∑ source, weight source *
            (kernel source destination).toReal) *
            observable destination := by
      apply Finset.sum_congr rfl
      intro destination _
      rw [Finset.sum_mul]
    _ = ∑ state, weight state * observable state := by
      apply Finset.sum_congr rfl
      intro destination _
      rw [hstationary destination]

/-- A support edge of a finite kernel with a full-support stationary weight
always lies on a support cycle. -/
theorem supportStep_returns_of_stationary_fullSupport
    [Fintype S]
    (kernel : S → PMF S) (weight : S → ℝ)
    (hweight : ∀ state, 0 < weight state)
    (hstationary :
      ∀ destination,
        ∑ source, weight source *
            (kernel source destination).toReal =
          weight destination)
    {source destination : S}
    (hstep : PMFSupportStep kernel source destination) :
    PMFReachable kernel destination source := by
  classical
  by_contra hnotReachable
  let reachable : Finset S :=
    Finset.univ.filter fun state =>
      PMFReachable kernel destination state
  have hdestination : destination ∈ reachable := by
    apply Finset.mem_filter.mpr
    exact
      ⟨Finset.mem_univ destination,
        Relation.ReflTransGen.refl⟩
  have hsource : source ∉ reachable := by
    simpa [reachable] using hnotReachable
  have hclosed :
      ∀ ⦃current⦄, current ∈ reachable →
        ∀ ⦃next⦄, PMFSupportStep kernel current next →
          next ∈ reachable := by
    intro current hcurrent next hnext
    have hreachCurrent :
        PMFReachable kernel destination current := by
      simpa [reachable] using hcurrent
    have hreachNext :
        PMFReachable kernel destination next :=
      hreachCurrent.tail hnext
    simpa [reachable] using hreachNext
  let indicator : S → ℝ :=
    fun state => if state ∈ reachable then 1 else 0
  have hexpect_one :
      ∀ current, current ∈ reachable →
        expect (kernel current) indicator = 1 := by
    intro current hcurrent
    rw [expect_eq_sum]
    calc
      (∑ next,
          (kernel current next).toReal * indicator next) =
          ∑ next, (kernel current next).toReal := by
        apply Finset.sum_congr rfl
        intro next _
        by_cases hnext : next ∈ reachable
        · simp [indicator, hnext]
        · have hkernelZero : kernel current next = 0 := by
            by_contra hkernel
            exact hnext (hclosed hcurrent hkernel)
          simp [indicator, hnext, hkernelZero]
      _ = 1 := pmf_toReal_sum_one (kernel current)
  have hexpect_nonneg :
      ∀ current, 0 ≤ expect (kernel current) indicator := by
    intro current
    apply expect_nonneg
    intro state
    by_cases hstate : state ∈ reachable <;>
      simp [indicator, hstate]
  have hexpect_source_pos :
      0 < expect (kernel source) indicator := by
    rw [expect_eq_sum]
    apply Finset.sum_pos'
    · intro state _
      apply mul_nonneg ENNReal.toReal_nonneg
      by_cases hstate : state ∈ reachable <;>
        simp [indicator, hstate]
    · refine ⟨destination, Finset.mem_univ _, ?_⟩
      simp only [indicator, if_pos hdestination, mul_one]
      exact ENNReal.toReal_pos hstep
        (PMF.apply_ne_top (kernel source) destination)
  have hdiffPos :
      0 <
        ∑ current,
          ((weight current *
                expect (kernel current) indicator) -
            weight current * indicator current) := by
    apply Finset.sum_pos'
    · intro current _
      by_cases hcurrent : current ∈ reachable
      · rw [hexpect_one current hcurrent]
        simp [indicator, hcurrent]
      · have hnonneg := hexpect_nonneg current
        have hindicator : indicator current = 0 := by
          simp [indicator, hcurrent]
        rw [hindicator, mul_zero, sub_zero]
        exact mul_nonneg (hweight current).le hnonneg
    · refine ⟨source, Finset.mem_univ _, ?_⟩
      have hindicator : indicator source = 0 := by
        simp [indicator, hsource]
      rw [hindicator, mul_zero, sub_zero]
      exact mul_pos (hweight source) hexpect_source_pos
  have hdiff :
      (∑ current, weight current *
          expect (kernel current) indicator) -
          ∑ current, weight current * indicator current =
        ∑ current,
          ((weight current *
                expect (kernel current) indicator) -
            weight current * indicator current) := by
    rw [Finset.sum_sub_distrib]
  have hstrict :
      (∑ current, weight current * indicator current) <
        ∑ current, weight current *
          expect (kernel current) indicator := by
    linarith
  have heq :=
    stationary_expectation kernel weight hstationary indicator
  linarith

/-- Under a full-support invariant law, the communication class of every
state is closed. -/
theorem communicationClass_closed_of_stationary_fullSupport
    [Fintype S]
    (kernel : S → PMF S) (weight : S → ℝ)
    (hweight : ∀ state, 0 < weight state)
    (hstationary :
      ∀ destination,
        ∑ source, weight source *
            (kernel source destination).toReal =
          weight destination)
    (state : S) :
    IsPMFClosed kernel (pmfCommunicationClass kernel state) := by
  intro source hsource destination hstep
  have hcommunicates :
      PMFCommunicates kernel state source :=
    (mem_pmfCommunicationClass_iff kernel state source).mp hsource
  have hreturn :
      PMFReachable kernel destination source :=
    supportStep_returns_of_stationary_fullSupport
      kernel weight hweight hstationary hstep
  apply (mem_pmfCommunicationClass_iff
    kernel state destination).mpr
  exact
    ⟨hcommunicates.1.tail hstep,
      hreturn.trans hcommunicates.2⟩

/-- Every communication class is internally communicating. -/
theorem communicationClass_communicates
    [Fintype S]
    (kernel : S → PMF S) (state : S) :
    ∀ ⦃source⦄,
      source ∈ pmfCommunicationClass kernel state →
      ∀ ⦃destination⦄,
        destination ∈ pmfCommunicationClass kernel state →
        PMFReachable kernel source destination := by
  intro source hsource destination hdestination
  have hs :=
    (mem_pmfCommunicationClass_iff kernel state source).mp hsource
  have hd :=
    (mem_pmfCommunicationClass_iff
      kernel state destination).mp hdestination
  exact hs.2.trans hd.1

/-- A closed communicating class is exactly the canonical
mutual-reachability class of its distinguished entry. -/
theorem ReachableClosedClass.states_eq_communicationClass
    [Fintype S] [DecidableEq S]
    {kernel : S → PMF S} {initial : S}
    (C : ReachableClosedClass kernel initial) :
    C.states = pmfCommunicationClass kernel C.entry := by
  ext state
  rw [mem_pmfCommunicationClass_iff]
  constructor
  · intro hstate
    exact
      ⟨C.communicates C.entry_mem hstate,
        C.communicates hstate C.entry_mem⟩
  · intro hcommunicates
    have path_mem :
        ∀ {left right},
          left ∈ C.states →
            PMFReachable kernel left right →
              right ∈ C.states := by
      intro left right hleft hreach
      induction hreach with
      | refl => exact hleft
      | tail _ hstep ih => exact C.closed ih hstep
    exact path_mem C.entry_mem hcommunicates.1

/-- Every state of a finite full-support stationary kernel determines a
closed communicating class, reachable from itself. -/
def reachableClosedClass_of_stationary_fullSupport
    [Fintype S] [DecidableEq S]
    (kernel : S → PMF S) (weight : S → ℝ)
    (hweight : ∀ state, 0 < weight state)
    (hstationary :
      ∀ destination,
        ∑ source, weight source *
            (kernel source destination).toReal =
          weight destination)
    (state : S) :
    ReachableClosedClass kernel state where
  states := pmfCommunicationClass kernel state
  states_nonempty :=
    ⟨state, self_mem_pmfCommunicationClass kernel state⟩
  closed :=
    communicationClass_closed_of_stationary_fullSupport
      kernel weight hweight hstationary state
  communicates :=
    communicationClass_communicates kernel state
  entry := state
  entry_mem := self_mem_pmfCommunicationClass kernel state
  reachable_entry := Relation.ReflTransGen.refl

end Probability
end Math
