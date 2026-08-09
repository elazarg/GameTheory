/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.EssentialAPS.Multivalued.Execution
import UniformEquilibrium.Quitting.EssentialAPS.InfiniteRun

/-!
# Segment-level execution in a multivalued essential-APS component

A finite Flesch strongly connected component is graph data. An executable APS
edge is stronger: it records one continuation value, one mass, and the exact
singleton-arc equation. This module never derives the second object from graph
connectivity or full convex-hull APS membership.

There are two deliberately separate layers.

1. `IsQuittingEssentialAPSSegmentSubinvariantOnSCC` is a genuine segment-level
   APS hypothesis. From it, every displayed state is terminal or has one exact
   internal segment, and
   `quittingEssentialAPSSCC_execution_of_segmentSubinvariant` produces a single
   finite absorbing execution or one coherent infinite execution.
2. Fixing a charge threshold `eta` gives the narrower diagnostic theorem
   `quittingEssentialAPSChargedSegment_executionOutcome`. It either executes
   using segments above that threshold or reaches a typed `noExecutableSegment`
   / `chargeGap` obstruction. It does not manufacture a positive threshold.

A source-to-component graph path is retained as graph metadata only. It is not
called an executable route unless a separate segment lift is supplied.
-/

noncomputable section

namespace GameTheory

open scoped BigOperators
open StochasticGame

universe u

/-- A finite strongly connected component of a supplied relation. Strong
connectivity is witnessed by paths whose vertices remain in `carrier`. -/
structure FiniteStronglyConnectedComponent
    {state : Type u} [DecidableEq state]
    (edge : state → state → Prop) where
  carrier : Finset state
  entry : state
  entry_mem : entry ∈ carrier
  stronglyConnected : ∀ {first second : state},
    first ∈ carrier → second ∈ carrier →
      FiniteSuccessorPathWithin carrier edge first second

/-- A graph-reachable SCC. The source path is intentionally graph-level data;
no strategic theorem below silently promotes it to an executable APS path. -/
structure FiniteReachableSCC
    {state : Type u} [DecidableEq state]
    (edge : state → state → Prop) (source : state)
    extends FiniteStronglyConnectedComponent edge where
  source_reaches_entry : FiniteSuccessorPath edge source entry

section EssentialAPS

variable {ι : Type} [DecidableEq ι]

/-- A finite SCC of the exact Flesch successor relation. -/
abbrev QuittingEssentialAPSSCC
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :=
  FiniteStronglyConnectedComponent (QuittingFleschSuccessor reward)

/-- A graph-reachable SCC of the exact Flesch successor relation. -/
abbrev QuittingEssentialAPSReachableSCC
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : ι) :=
  FiniteReachableSCC (QuittingFleschSuccessor reward) source

/-- Forget graph reachability while retaining the displayed SCC. -/
def FiniteReachableSCC.toStronglyConnectedComponent
    {state : Type u} [DecidableEq state]
    {edge : state → state → Prop} {source : state}
    (component : FiniteReachableSCC edge source) :
    FiniteStronglyConnectedComponent edge :=
  component.toFiniteStronglyConnectedComponent

/-- A payoff-labelled state inside the selected SCC. -/
structure QuittingEssentialAPSSCCState
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (component : QuittingEssentialAPSSCC reward)
    (family : ι → Set (Payoff ι)) where
  owner : ι
  owner_mem : owner ∈ component.carrier
  value : Payoff ι
  value_mem : value ∈ family owner

/-- The displayed initial state at the SCC entry. -/
def quittingEssentialAPSSCCInitialState
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (component : QuittingEssentialAPSSCC reward)
    (family : ι → Set (Payoff ι))
    (initialValue : Payoff ι)
    (hinitial : initialValue ∈ family component.entry) :
    QuittingEssentialAPSSCCState component family where
  owner := component.entry
  owner_mem := component.entry_mem
  value := initialValue
  value_mem := hinitial

/-- One exact executable singleton-flow segment internal to the chosen SCC. -/
structure IsQuittingEssentialAPSInternalSCCStep
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {component : QuittingEssentialAPSSCC reward}
    {family : ι → Set (Payoff ι)}
    (current next : QuittingEssentialAPSSCCState component family)
    (mass : ℝ) : Prop where
  mass_mem : mass ∈ Set.Ico (0 : ℝ) 1
  successor : QuittingFleschSuccessor reward current.owner next.owner
  arc : current.value = quittingSingletonArcPayoff mass
    (quittingSoloReward reward current.owner) next.value

/-- The finite branch ends at an essential-APS terminal point. -/
def IsQuittingEssentialAPSSCCAbsorbing
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {component : QuittingEssentialAPSSCC reward}
    {family : ι → Set (Payoff ι)}
    (current : QuittingEssentialAPSSCCState component family) : Prop :=
  current.value ∈ quittingEssentialAPSTerminal reward current.owner

/-- Restrict an owner-indexed payoff family to the displayed SCC carrier. -/
def quittingEssentialAPSSCCRestrictedFamily
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (component : QuittingEssentialAPSSCC reward)
    (family : ι → Set (Payoff ι)) : ι → Set (Payoff ι) :=
  fun owner => {value | owner ∈ component.carrier ∧ value ∈ family owner}

@[simp] theorem mem_quittingEssentialAPSSCCRestrictedFamily_iff
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (component : QuittingEssentialAPSSCC reward)
    (family : ι → Set (Payoff ι))
    (owner : ι) (value : Payoff ι) :
    value ∈ quittingEssentialAPSSCCRestrictedFamily component family owner ↔
      owner ∈ component.carrier ∧ value ∈ family owner :=
  Iff.rfl

/-- A named segment-level APS hypothesis on the displayed SCC.

Every family point at an SCC owner belongs to the existing segment owner step,
with continuations restricted to the same SCC. Unlike the full essential-APS
operator, this hypothesis already selects one exact continuation rather than a
convex combination of several continuation values. -/
def IsQuittingEssentialAPSSegmentSubinvariantOnSCC
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (component : QuittingEssentialAPSSCC reward)
    (family : ι → Set (Payoff ι)) : Prop :=
  ∀ owner, owner ∈ component.carrier →
    family owner ⊆
      quittingSegmentEssentialAPSOwnerStep reward
        (quittingEssentialAPSSCCRestrictedFamily component family) owner

/-- Segment subinvariance gives actual local progress: terminal absorption or
one exact internal singleton-flow segment. The apparent `mass = 1` segment is
converted to the terminal branch, leaving masses in `[0,1)` on execution
edges. -/
theorem
    quittingEssentialAPSSCC_terminal_or_internalStep_of_segmentSubinvariant
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {component : QuittingEssentialAPSSCC reward}
    {family : ι → Set (Payoff ι)}
    (hsegment :
      IsQuittingEssentialAPSSegmentSubinvariantOnSCC component family)
    (current : QuittingEssentialAPSSCCState component family) :
    IsQuittingEssentialAPSSCCAbsorbing current ∨
      ∃ (mass : ℝ) (next : QuittingEssentialAPSSCCState component family),
        IsQuittingEssentialAPSInternalSCCStep current next mass := by
  have hdecomposition :=
    hsegment current.owner current.owner_mem current.value_mem
  rcases hdecomposition with hterminal | hsegmentStep
  · exact Or.inl hterminal
  · rcases hsegmentStep with
      ⟨hviable, mass, hmass, nextValue, hnext,
        harc, _hactive⟩
    rcases hnext with
      ⟨successor, hsuccessor, hnextRestricted⟩
    change successor ∈ component.carrier ∧
      nextValue ∈ family successor at hnextRestricted
    rcases hnextRestricted with ⟨hsuccessorMem, hnextMem⟩
    by_cases hmassOne : mass = 1
    · left
      have hroot :
          current.value = quittingSoloReward reward current.owner := by
        rw [harc, hmassOne]
        funext who
        simp [quittingSingletonArcPayoff]
      exact ⟨hroot, hviable⟩
    · right
      have hmassLt : mass < 1 := lt_of_le_of_ne hmass.2 hmassOne
      let next : QuittingEssentialAPSSCCState component family := {
        owner := successor
        owner_mem := hsuccessorMem
        value := nextValue
        value_mem := hnextMem }
      refine ⟨mass, next, ?_⟩
      exact {
        mass_mem := ⟨hmass.1, hmassLt⟩
        successor := hsuccessor
        arc := harc }

/-- **Genuine segment-level multivalued execution theorem.**

A segment-subinvariant family restricted to the displayed SCC produces one
single chronological object from every initial entry value: either a finite
execution ending at an essential-APS terminal, or one coherent infinite exact
singleton-flow execution inside the SCC. Graph connectivity alone is not the
producer; `hsegment` is the consumed segment-level progress hypothesis. -/
theorem quittingEssentialAPSSCC_execution_of_segmentSubinvariant
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (component : QuittingEssentialAPSSCC reward)
    (family : ι → Set (Payoff ι))
    (hsegment :
      IsQuittingEssentialAPSSegmentSubinvariantOnSCC component family)
    (initialValue : Payoff ι)
    (hinitial : initialValue ∈ family component.entry) :
    ChronologicalExecution
      (fun current : QuittingEssentialAPSSCCState component family =>
        IsQuittingEssentialAPSSCCAbsorbing current)
      (fun current mass next =>
        IsQuittingEssentialAPSInternalSCCStep current next mass)
      (quittingEssentialAPSSCCInitialState
        component family initialValue hinitial) := by
  apply chronologicalExecution_of_reachable_progress
  intro current _hreach
  exact
    quittingEssentialAPSSCC_terminal_or_internalStep_of_segmentSubinvariant
      hsegment current

/-- Forgetting SCC membership turns the recurrent branch of the positive
segment theorem into the existing essential-APS infinite-run object. -/
theorem ChronologicalInfinitePath.toQuittingEssentialAPSInfiniteRun_of_internal
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {component : QuittingEssentialAPSSCC reward}
    {family : ι → Set (Payoff ι)}
    {initial : QuittingEssentialAPSSCCState component family}
    (path : ChronologicalInfinitePath
      (fun current mass next =>
        IsQuittingEssentialAPSInternalSCCStep current next mass)
      initial) :
    IsQuittingEssentialAPSInfiniteRun reward family
      (fun time => (path.vertex time).owner)
      initial.value
      path.charge
      (fun time => (path.vertex time).value) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using congrArg (fun current => current.value) path.initial
  · intro time
    exact (path.vertex time).value_mem
  · intro time
    exact ⟨(path.step time).mass_mem, (path.step time).arc⟩

/-! ## Optional quantitative charge layer -/

/-- An internal segment carrying at least `eta` absorption charge. The charge
is measured only along the selected chronological path, so it cannot be
cancelled by an occupation in another recurrent component. -/
def IsQuittingEssentialAPSChargedSCCStep
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {component : QuittingEssentialAPSSCC reward}
    {family : ι → Set (Payoff ι)}
    (eta : ℝ)
    (current next : QuittingEssentialAPSSCCState component family)
    (mass : ℝ) : Prop :=
  IsQuittingEssentialAPSInternalSCCStep current next mass ∧ eta ≤ mass

/-- Exact obstruction data at a reached SCC-labelled state. -/
inductive QuittingEssentialAPSSCCObstruction
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {component : QuittingEssentialAPSSCC reward}
    {family : ι → Set (Payoff ι)}
    (eta : ℝ)
    (current : QuittingEssentialAPSSCCState component family) : Prop
  | noExecutableSegment
      (failure : ¬ ∃ (mass : ℝ)
        (next : QuittingEssentialAPSSCCState component family),
          IsQuittingEssentialAPSInternalSCCStep current next mass)
  | chargeGap
      (hasSegment : ∃ (mass : ℝ)
        (next : QuittingEssentialAPSSCCState component family),
          IsQuittingEssentialAPSInternalSCCStep current next mass)
      (failure : ¬ ∃ (mass : ℝ)
        (next : QuittingEssentialAPSSCCState component family),
          IsQuittingEssentialAPSChargedSCCStep eta current next mass)

/-- A missing charged edge is classified without promoting algebraic APS
membership to an executable segment. -/
theorem quittingEssentialAPSSCC_classifyObstruction
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {component : QuittingEssentialAPSSCC reward}
    {family : ι → Set (Payoff ι)}
    (eta : ℝ)
    (current : QuittingEssentialAPSSCCState component family)
    (failure : ¬ ∃ (mass : ℝ)
      (next : QuittingEssentialAPSSCCState component family),
        IsQuittingEssentialAPSChargedSCCStep eta current next mass) :
    QuittingEssentialAPSSCCObstruction eta current := by
  classical
  by_cases hsegment : ∃ (mass : ℝ)
      (next : QuittingEssentialAPSSCCState component family),
        IsQuittingEssentialAPSInternalSCCStep current next mass
  · exact .chargeGap hsegment failure
  · exact .noExecutableSegment hsegment

/-- **Charged-segment execution-or-obstruction trichotomy.**

This theorem classifies the supplied relation “there is an exact internal
segment of mass at least `eta`.” It does not infer segment existence, exclude
its obstruction branch, or derive a positive `eta` from finiteness of the
owner SCC. Its positive branches are nevertheless single chronological paths,
never globally cancelled occupations. -/
theorem quittingEssentialAPSChargedSegment_executionOutcome
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (component : QuittingEssentialAPSSCC reward)
    (family : ι → Set (Payoff ι))
    (eta : ℝ)
    (initialValue : Payoff ι)
    (hinitial : initialValue ∈ family component.entry) :
    ChronologicalExecutionOutcome
      (fun current : QuittingEssentialAPSSCCState component family =>
        IsQuittingEssentialAPSSCCAbsorbing current)
      (fun current mass next =>
        IsQuittingEssentialAPSChargedSCCStep eta current next mass)
      (fun current => QuittingEssentialAPSSCCObstruction eta current)
      (quittingEssentialAPSSCCInitialState
        component family initialValue hinitial) :=
  chronologicalExecutionOutcome_of_classifier
    (fun current : QuittingEssentialAPSSCCState component family =>
      IsQuittingEssentialAPSSCCAbsorbing current)
    (fun current mass next =>
      IsQuittingEssentialAPSChargedSCCStep eta current next mass)
    (fun current => QuittingEssentialAPSSCCObstruction eta current)
    (quittingEssentialAPSSCCInitialState
      component family initialValue hinitial)
    (quittingEssentialAPSSCC_classifyObstruction eta)

/-- Forgetting SCC membership and the charge lower bound turns a charged
recurrent branch into the existing essential-APS infinite-run object. -/
theorem ChronologicalInfinitePath.toQuittingEssentialAPSInfiniteRun
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {component : QuittingEssentialAPSSCC reward}
    {family : ι → Set (Payoff ι)}
    {eta : ℝ}
    {initial : QuittingEssentialAPSSCCState component family}
    (path : ChronologicalInfinitePath
      (fun current mass next =>
        IsQuittingEssentialAPSChargedSCCStep eta current next mass)
      initial) :
    IsQuittingEssentialAPSInfiniteRun reward family
      (fun time => (path.vertex time).owner)
      initial.value
      path.charge
      (fun time => (path.vertex time).value) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using congrArg (fun current => current.value) path.initial
  · intro time
    exact (path.vertex time).value_mem
  · intro time
    exact ⟨(path.step time).1.mass_mem, (path.step time).1.arc⟩

/-- A pointwise component-local charge floor gives a linear prefix bound. -/
theorem ChronologicalInfinitePath.prefixCharge_lowerBound
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {component : QuittingEssentialAPSSCC reward}
    {family : ι → Set (Payoff ι)}
    {eta : ℝ}
    {initial : QuittingEssentialAPSSCCState component family}
    (path : ChronologicalInfinitePath
      (fun current mass next =>
        IsQuittingEssentialAPSChargedSCCStep eta current next mass)
      initial)
    (horizon : ℕ) :
    (horizon : ℝ) * eta ≤
      ∑ time ∈ Finset.range horizon, path.charge time := by
  induction horizon with
  | zero => simp
  | succ horizon ih =>
      calc
        ((horizon + 1 : ℕ) : ℝ) * eta =
            (horizon : ℝ) * eta + eta := by
              push_cast
              ring
        _ ≤ (∑ time ∈ Finset.range horizon, path.charge time) +
              path.charge horizon :=
            add_le_add ih (path.step horizon).2
        _ = ∑ time ∈ Finset.range (horizon + 1), path.charge time := by
            rw [Finset.sum_range_succ]

/-- If a positive pointwise charge floor is separately supplied, the same
chronological recurrent path reaches every finite charge target. -/
theorem ChronologicalInfinitePath.exists_prefixCharge_ge
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {component : QuittingEssentialAPSSCC reward}
    {family : ι → Set (Payoff ι)}
    {eta : ℝ}
    {initial : QuittingEssentialAPSSCCState component family}
    (path : ChronologicalInfinitePath
      (fun current mass next =>
        IsQuittingEssentialAPSChargedSCCStep eta current next mass)
      initial)
    (heta : 0 < eta)
    (target : ℝ) :
    ∃ horizon : ℕ,
      target ≤ ∑ time ∈ Finset.range horizon, path.charge time := by
  obtain ⟨horizon, hhorizon⟩ := exists_nat_gt (target / eta)
  refine ⟨horizon,
    le_trans ((div_lt_iff₀ heta).mp hhorizon).le
      (path.prefixCharge_lowerBound horizon)⟩

end EssentialAPS
end GameTheory
