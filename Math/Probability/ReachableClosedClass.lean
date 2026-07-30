/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability.OccupationFlowAlternative

/-!
# Reachable closed classes for finite Markov kernels

An occupation circulation constructs an invariant law on its positive
source support.  This is an internal statement about the stationary
response.  Entering that response from an external state additionally
requires a support path from the actual entry state.

This file records the minimal finite interface for that extra obligation
and a two-state counterexample showing that a positive actual occupation
circulation does not provide it.
-/

set_option autoImplicit false

noncomputable section

namespace Math
namespace Probability

/-- One support edge of a Markov kernel. -/
def PMFSupportStep {S : Type*} (kernel : S → PMF S)
    (source destination : S) : Prop :=
  kernel source destination ≠ 0

/-- Reachability through finitely many positive-probability transitions. -/
def PMFReachable {S : Type*} (kernel : S → PMF S)
    (source destination : S) : Prop :=
  Relation.ReflTransGen (PMFSupportStep kernel) source destination

/-- A finite state set closed under every positive-probability transition. -/
def IsPMFClosed {S : Type*} (kernel : S → PMF S)
    (states : Finset S) : Prop :=
  ∀ ⦃source⦄, source ∈ states →
    ∀ ⦃destination⦄, PMFSupportStep kernel source destination →
      destination ∈ states

/-- A finite closed communicating class together with an entry path from
the externally supplied initial state. -/
structure ReachableClosedClass
    {S : Type*} [Fintype S] [DecidableEq S]
    (kernel : S → PMF S) (initial : S) where
  states : Finset S
  states_nonempty : states.Nonempty
  closed : IsPMFClosed kernel states
  communicates :
    ∀ ⦃source⦄, source ∈ states →
      ∀ ⦃destination⦄, destination ∈ states →
        PMFReachable kernel source destination
  entry : S
  entry_mem : entry ∈ states
  reachable_entry : PMFReachable kernel initial entry

namespace PositiveCirculationNotReachable

/-!
The smallest obstruction has two states.  The external state and the
circulation state are both absorbing.  The self-loop at `true` is a
positive actual occupation circulation, but it cannot be entered from
`false`.
-/

abbrev State := Bool
abbrev Index := Unit

/-- The ambient kernel has two disjoint absorbing classes. -/
def ambientKernel (state : State) : PMF State :=
  PMF.pure state

/-- The operational family consists only of the self-loop at `true`. -/
def operationalKernel (_ : Index) : PMF State :=
  PMF.pure true

def operationalSource (_ : Index) : State :=
  true

/-- The single actual transition is already a normalized positive
circulation. -/
theorem hasNormalizedPositiveCirculation :
    HasNormalizedPositiveCirculation
      (actualOccupationColumn operationalKernel operationalSource) () := by
  refine ⟨fun _ => 0, fun _ => le_rfl, ?_⟩
  intro destination
  cases destination <;>
    simp [actualOccupationColumn, operationalKernel, operationalSource]

theorem ambientSupportStep_eq
    {source destination : State}
    (hstep : PMFSupportStep ambientKernel source destination) :
    source = destination := by
  have : destination = source := by
    simpa [PMFSupportStep, ambientKernel] using hstep
  exact this.symm

/-- Every state reachable under the ambient self-loop kernel equals the
starting state. -/
theorem eq_of_ambientReachable
    {source destination : State}
    (hreach : PMFReachable ambientKernel source destination) :
    source = destination := by
  induction hreach using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head hstep _ ih =>
      exact (ambientSupportStep_eq hstep).trans ih

/-- The active circulation class cannot be reached from the external
entry. -/
theorem not_reachable_true_from_false :
    ¬PMFReachable ambientKernel false true := by
  intro hreach
  have hfalseTrue : false = true :=
    eq_of_ambientReachable hreach
  exact Bool.false_ne_true hfalseTrue

/-- The singleton circulation class is nevertheless closed. -/
theorem true_singleton_closed :
    IsPMFClosed ambientKernel {true} := by
  intro source hsource destination hstep
  have hsourceTrue : source = true := by
    simpa using hsource
  have hdestination : destination = source :=
    (ambientSupportStep_eq hstep).symm
  simp [hdestination, hsourceTrue]

/-- A positive circulation and a closed active class therefore do not imply
reachable class entry. -/
theorem circulation_and_closed_but_not_reachable :
    HasNormalizedPositiveCirculation
        (actualOccupationColumn operationalKernel operationalSource) () ∧
      IsPMFClosed ambientKernel {true} ∧
      ¬PMFReachable ambientKernel false true :=
  ⟨hasNormalizedPositiveCirculation,
    true_singleton_closed,
    not_reachable_true_from_false⟩

end PositiveCirculationNotReachable

end Probability
end Math
