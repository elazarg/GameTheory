/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.ChargedPathExecution
import UniformEquilibrium.Quitting.EssentialAPS.InfiniteRun

/-!
# Multivalued execution for segment-closed essential APS families

Algebraic essential-APS invariance uses a convex hull and does not by itself
select a chronological continuation. This file states the exact additional
hypothesis needed for multivalued execution: every family point has a terminal
decomposition or one singleton segment whose next owner remains in a supplied
carrier.

The carrier is an arbitrary set of owners. No finiteness, strong connectivity,
or uniqueness of the live successor is used. Under segment closure, dependent
choice produces either a finite charged path to a terminal point or an
infinite exact APS run. The recurrent branch also retains the selected Flesch
successor at every date.
-/

noncomputable section

namespace GameTheory

open StochasticGame
open Math.ChargedPathBudget

variable {ι : Type}

/-- Restrict an owner-indexed payoff family to a chosen owner carrier. -/
def quittingEssentialAPSCarrierFamily
    (carrier : Set ι) (family : ι → Set (Payoff ι)) :
    ι → Set (Payoff ι) :=
  fun owner => {value | owner ∈ carrier ∧ value ∈ family owner}

@[simp]
theorem mem_quittingEssentialAPSCarrierFamily_iff
    (carrier : Set ι) (family : ι → Set (Payoff ι))
    (owner : ι) (value : Payoff ι) :
    value ∈ quittingEssentialAPSCarrierFamily carrier family owner ↔
      owner ∈ carrier ∧ value ∈ family owner :=
  Iff.rfl

/-- A payoff labelled by an owner in the carrier. -/
structure QuittingEssentialAPSCarrierState
    (carrier : Set ι) (family : ι → Set (Payoff ι)) where
  owner : ι
  owner_mem : owner ∈ carrier
  value : Payoff ι
  value_mem : value ∈ family owner

/-- A carrier state is terminal when its value is the viable solo endpoint of
its displayed owner. -/
def IsQuittingEssentialAPSCarrierTerminal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {carrier : Set ι} {family : ι → Set (Payoff ι)}
    (state : QuittingEssentialAPSCarrierState carrier family) : Prop :=
  state.value ∈ quittingEssentialAPSTerminal reward state.owner

/-- One actual nonterminal singleton-flow edge inside the carrier. -/
structure QuittingEssentialAPSCarrierEdge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (carrier : Set ι) (family : ι → Set (Payoff ι)) where
  source : QuittingEssentialAPSCarrierState carrier family
  target : QuittingEssentialAPSCarrierState carrier family
  mass : ℝ
  mass_mem : mass ∈ Set.Ico (0 : ℝ) 1
  successor : QuittingFleschSuccessor reward source.owner target.owner
  arc : source.value = quittingSingletonArcPayoff mass
    (quittingSoloReward reward source.owner) target.value

/-- Carrier execution as a charged relation. Its charge is the selected
absorption mass, so finite budgets and infinite charge-selection results apply
without translating paths. -/
def quittingEssentialAPSCarrierRelation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (carrier : Set ι) (family : ι → Set (Payoff ι)) :
    ChargedRelation
      (QuittingEssentialAPSCarrierState carrier family)
      (QuittingEssentialAPSCarrierEdge reward carrier family) where
  src := QuittingEssentialAPSCarrierEdge.source
  tgt := QuittingEssentialAPSCarrierEdge.target
  charge := QuittingEssentialAPSCarrierEdge.mass
  charge_nonneg edge := edge.mass_mem.1

/-- Segment closure on an owner carrier.

This is intentionally stronger than ordinary algebraic essential-APS
subinvariance: the continuation is one selected segment and its next owner is
again in the carrier. -/
def IsQuittingEssentialAPSSegmentClosedOn
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (carrier : Set ι) (family : ι → Set (Payoff ι)) : Prop :=
  ∀ owner, owner ∈ carrier →
    family owner ⊆
      quittingSegmentEssentialAPSOwnerStep reward
        (quittingEssentialAPSCarrierFamily carrier family) owner

/-- Segment closure gives actual local progress. A displayed mass equal to one
is the terminal solo payoff; every remaining edge has mass in `[0,1)`. -/
theorem quittingEssentialAPSCarrier_terminal_or_edge_of_segmentClosed
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {carrier : Set ι} {family : ι → Set (Payoff ι)}
    (hclosed : IsQuittingEssentialAPSSegmentClosedOn reward carrier family)
    (current : QuittingEssentialAPSCarrierState carrier family) :
    IsQuittingEssentialAPSCarrierTerminal reward current ∨
      ∃ edge : QuittingEssentialAPSCarrierEdge reward carrier family,
        edge.source = current := by
  have hdecomposition :=
    hclosed current.owner current.owner_mem current.value_mem
  rcases hdecomposition with hterminal | hsegment
  · exact Or.inl hterminal
  · rcases hsegment with
      ⟨hviable, mass, hmass, nextValue, hnext, harc, _hactive⟩
    rcases hnext with
      ⟨nextOwner, hsuccessor, hnextCarrier, hnextMem⟩
    by_cases hmassOne : mass = 1
    · left
      refine ⟨?_, hviable⟩
      rw [harc, hmassOne]
      funext who
      simp [quittingSingletonArcPayoff]
    · right
      have hmassLt : mass < 1 := lt_of_le_of_ne hmass.2 hmassOne
      let next : QuittingEssentialAPSCarrierState carrier family := {
        owner := nextOwner
        owner_mem := hnextCarrier
        value := nextValue
        value_mem := hnextMem }
      let edge : QuittingEssentialAPSCarrierEdge reward carrier family := {
        source := current
        target := next
        mass := mass
        mass_mem := ⟨hmass.1, hmassLt⟩
        successor := hsuccessor
        arc := harc }
      exact ⟨edge, rfl⟩

/-- Segment closure yields one coherent chronological object from every
carrier-labelled initial value: either a finite terminal path or an infinite
stream of exact charged carrier edges. -/
theorem quittingEssentialAPSCarrier_execution_of_segmentClosed
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (carrier : Set ι) (family : ι → Set (Payoff ι))
    (hclosed : IsQuittingEssentialAPSSegmentClosedOn reward carrier family)
    (initial : QuittingEssentialAPSCarrierState carrier family) :
    ChargedRelation.HasChronologicalExecution
      (quittingEssentialAPSCarrierRelation reward carrier family)
      (IsQuittingEssentialAPSCarrierTerminal reward) initial := by
  apply ChargedRelation.hasChronologicalExecution_of_reachable_progress
  intro current _hreachable
  exact
    quittingEssentialAPSCarrier_terminal_or_edge_of_segmentClosed
      reward hclosed current

/-- The recurrent branch of carrier execution is the established essential-APS
infinite-run object, together with its carrier and exact-successor metadata.
No uniqueness or graph-connectivity hypothesis is required. -/
theorem quittingEssentialAPSCarrier_terminalPath_or_infiniteRun_of_segmentClosed
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (carrier : Set ι) (family : ι → Set (Payoff ι))
    (hclosed : IsQuittingEssentialAPSSegmentClosedOn reward carrier family)
    (initial : QuittingEssentialAPSCarrierState carrier family) :
    (∃ terminal,
        Nonempty ((quittingEssentialAPSCarrierRelation reward carrier family).Path
          initial terminal) ∧
        IsQuittingEssentialAPSCarrierTerminal reward terminal) ∨
      ∃ (owner : ℕ → ι) (mass : ℕ → ℝ) (value : ℕ → Payoff ι),
        IsQuittingEssentialAPSInfiniteRun reward family
          owner initial.value mass value ∧
        (∀ time, owner time ∈ carrier) ∧
        ∀ time, QuittingFleschSuccessor reward
          (owner time) (owner (time + 1)) := by
  rcases
      quittingEssentialAPSCarrier_execution_of_segmentClosed
        reward carrier family hclosed initial with hfinite | hinfinite
  · exact Or.inl hfinite
  · right
    rcases hinfinite with ⟨state, edge, hzero, hstep⟩
    let owner : ℕ → ι := fun time => (state time).owner
    let mass : ℕ → ℝ := fun time => (edge time).mass
    let value : ℕ → Payoff ι := fun time => (state time).value
    refine ⟨owner, mass, value, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · simpa [value] using congrArg
          (fun current => current.value) hzero
      · intro time
        exact (state time).value_mem
      · intro time
        have hsource : (edge time).source = state time := by
          simpa [quittingEssentialAPSCarrierRelation] using (hstep time).1
        have htarget : (edge time).target = state (time + 1) := by
          simpa [quittingEssentialAPSCarrierRelation] using (hstep time).2
        have harc := (edge time).arc
        rw [hsource, htarget] at harc
        exact ⟨(edge time).mass_mem, harc⟩
    · intro time
      exact (state time).owner_mem
    · intro time
      have hsource : (edge time).source = state time := by
        simpa [quittingEssentialAPSCarrierRelation] using (hstep time).1
      have htarget : (edge time).target = state (time + 1) := by
        simpa [quittingEssentialAPSCarrierRelation] using (hstep time).2
      have hsuccessor := (edge time).successor
      rw [hsource, htarget] at hsuccessor
      exact hsuccessor

end GameTheory
