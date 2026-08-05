/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability.StationaryCommunicatingClass

/-!
# Reachable closed classes of finite Markov kernels

Every finite directed support graph has a sink strongly connected component
reachable from any prescribed initial vertex. Applied to the support graph
of a finite Markov kernel, this gives a `ReachableClosedClass` without a
stationary-distribution hypothesis.

The proof chooses, among states reachable from the initial state, one whose
forward reachable set has minimum cardinality. Any support successor has a
smaller forward reachable set by inclusion, hence the same set by
minimality. It can therefore return to the chosen state.
-/

noncomputable section

namespace Math
namespace Probability

variable {S : Type*}

/-- Finite forward support-reachable set of a state. -/
def pmfReachableSet
    [Fintype S]
    (kernel : S → PMF S) (source : S) : Finset S := by
  classical
  exact Finset.univ.filter fun destination =>
    PMFReachable kernel source destination

theorem mem_pmfReachableSet_iff
    [Fintype S]
    (kernel : S → PMF S) (source destination : S) :
    destination ∈ pmfReachableSet kernel source ↔
      PMFReachable kernel source destination := by
  classical
  simp [pmfReachableSet]

theorem self_mem_pmfReachableSet
    [Fintype S]
    (kernel : S → PMF S) (source : S) :
    source ∈ pmfReachableSet kernel source :=
  (mem_pmfReachableSet_iff kernel source source).mpr
    Relation.ReflTransGen.refl

/-- Forward reachability reverses inclusion of forward reachable sets. -/
theorem pmfReachableSet_subset_of_reachable
    [Fintype S]
    (kernel : S → PMF S) {source destination : S}
    (reachable : PMFReachable kernel source destination) :
    pmfReachableSet kernel destination ⊆
      pmfReachableSet kernel source := by
  intro state hstate
  apply (mem_pmfReachableSet_iff kernel source state).mpr
  exact reachable.trans
    ((mem_pmfReachableSet_iff
      kernel destination state).mp hstate)

/-- Every finite Markov kernel has a closed communicating class reachable
from the supplied initial state. -/
theorem exists_reachableClosedClass
    [Fintype S] [DecidableEq S]
    (kernel : S → PMF S) (initial : S) :
    Nonempty (ReachableClosedClass kernel initial) := by
  classical
  let reachableFromInitial := pmfReachableSet kernel initial
  have reachableFromInitial_nonempty :
      reachableFromInitial.Nonempty :=
    ⟨initial, self_mem_pmfReachableSet kernel initial⟩
  obtain ⟨terminal, terminal_mem, terminal_minimal⟩ :=
    Finset.exists_min_image reachableFromInitial
      (fun state => (pmfReachableSet kernel state).card)
      reachableFromInitial_nonempty
  have initial_reaches_terminal :
      PMFReachable kernel initial terminal := by
    exact
      (mem_pmfReachableSet_iff
        kernel initial terminal).mp terminal_mem
  have terminal_class_closed :
      IsPMFClosed kernel
        (pmfCommunicationClass kernel terminal) := by
    intro source source_mem destination step
    have terminal_communicates_source :
        PMFCommunicates kernel terminal source :=
      (mem_pmfCommunicationClass_iff
        kernel terminal source).mp source_mem
    have terminal_reaches_destination :
        PMFReachable kernel terminal destination :=
      terminal_communicates_source.1.tail step
    have destination_mem :
        destination ∈ reachableFromInitial := by
      apply (mem_pmfReachableSet_iff
        kernel initial destination).mpr
      exact initial_reaches_terminal.trans
        terminal_reaches_destination
    have destination_subset_terminal :
        pmfReachableSet kernel destination ⊆
          pmfReachableSet kernel terminal :=
      pmfReachableSet_subset_of_reachable
        kernel terminal_reaches_destination
    have terminal_card_le :
        (pmfReachableSet kernel terminal).card ≤
          (pmfReachableSet kernel destination).card :=
      terminal_minimal destination destination_mem
    have reachable_sets_eq :
        pmfReachableSet kernel destination =
          pmfReachableSet kernel terminal :=
      Finset.eq_of_subset_of_card_le
        destination_subset_terminal terminal_card_le
    have destination_reaches_terminal :
        PMFReachable kernel destination terminal := by
      apply (mem_pmfReachableSet_iff
        kernel destination terminal).mp
      rw [reachable_sets_eq]
      exact self_mem_pmfReachableSet kernel terminal
    apply (mem_pmfCommunicationClass_iff
      kernel terminal destination).mpr
    exact
      ⟨terminal_reaches_destination,
        destination_reaches_terminal⟩
  exact ⟨{
    states := pmfCommunicationClass kernel terminal
    states_nonempty :=
      ⟨terminal,
        self_mem_pmfCommunicationClass kernel terminal⟩
    closed := terminal_class_closed
    communicates :=
      communicationClass_communicates kernel terminal
    entry := terminal
    entry_mem :=
      self_mem_pmfCommunicationClass kernel terminal
    reachable_entry := initial_reaches_terminal
  }⟩

end Probability
end Math
