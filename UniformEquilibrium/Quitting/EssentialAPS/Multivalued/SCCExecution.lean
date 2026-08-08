/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.EssentialAPS.Multivalued.Execution
import UniformEquilibrium.Quitting.EssentialAPS.InfiniteRun

/-!
# Executable multivalued essential-APS SCCs

A finite Flesch-successor SCC is graph data.  An executable APS edge is stronger:
it records one continuation value, one mass in `[0,1)`, and the exact singleton-
arc equation.  This module never derives the second object from convex-hull APS
membership alone.

Starting at a labelled value in a reachable SCC, the capstone returns one of:

* a finite component-internal execution ending at an absorbing APS terminal;
* one coherent infinite component-internal execution with a positive lower
  bound on every local absorption charge; or
* a reached typed obstruction saying either that no exact segment exists, or
  that exact segments exist but none carries the requested component-local
  charge.
-/

noncomputable section

namespace GameTheory

open scoped BigOperators
open StochasticGame

universe u

/-- A finite reachable strongly connected component of a supplied relation.
Strong connectivity is witnessed by paths whose vertices remain in `carrier`. -/
structure FiniteReachableSCC
    {state : Type u} [DecidableEq state]
    (edge : state → state → Prop) (source : state) where
  carrier : Finset state
  entry : state
  entry_mem : entry ∈ carrier
  source_reaches_entry : FiniteSuccessorPath edge source entry
  stronglyConnected : ∀ {first second : state},
    first ∈ carrier → second ∈ carrier →
      FiniteSuccessorPathWithin carrier edge first second

section EssentialAPS

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A reachable SCC of the exact Flesch successor relation. -/
abbrev QuittingEssentialAPSReachableSCC
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : ι) :=
  FiniteReachableSCC (QuittingFleschSuccessor reward) source

/-- A payoff-labelled state inside the selected SCC. -/
structure QuittingEssentialAPSSCCState
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {source : ι}
    (component : QuittingEssentialAPSReachableSCC reward source)
    (family : ι → Set (Payoff ι)) where
  owner : ι
  owner_mem : owner ∈ component.carrier
  value : Payoff ι
  value_mem : value ∈ family owner

/-- The displayed initial state at the reachable SCC entry. -/
def quittingEssentialAPSSCCInitialState
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {source : ι}
    (component : QuittingEssentialAPSReachableSCC reward source)
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
    {source : ι}
    {component : QuittingEssentialAPSReachableSCC reward source}
    {family : ι → Set (Payoff ι)}
    (current next : QuittingEssentialAPSSCCState component family)
    (mass : ℝ) : Prop where
  mass_mem : mass ∈ Set.Ico (0 : ℝ) 1
  successor : QuittingFleschSuccessor reward current.owner next.owner
  arc : current.value = quittingSingletonArcPayoff mass
    (quittingSoloReward reward current.owner) next.value

/-- An internal segment carrying at least `eta` absorption charge.  The charge
is component-local: it is measured only along the selected SCC path, so it
cannot be cancelled by an occupation in another recurrent component. -/
def IsQuittingEssentialAPSChargedSCCStep
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {source : ι}
    {component : QuittingEssentialAPSReachableSCC reward source}
    {family : ι → Set (Payoff ι)}
    (eta : ℝ)
    (current next : QuittingEssentialAPSSCCState component family)
    (mass : ℝ) : Prop :=
  IsQuittingEssentialAPSInternalSCCStep current next mass ∧ eta ≤ mass

/-- The finite branch ends at an essential-APS terminal point. -/
def IsQuittingEssentialAPSSCCAbsorbing
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {source : ι}
    {component : QuittingEssentialAPSReachableSCC reward source}
    {family : ι → Set (Payoff ι)}
    (current : QuittingEssentialAPSSCCState component family) : Prop :=
  current.value ∈ quittingEssentialAPSTerminal reward current.owner

/-- Exact obstruction data at a reached SCC state. -/
inductive QuittingEssentialAPSSCCObstruction
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {source : ι}
    {component : QuittingEssentialAPSReachableSCC reward source}
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
    {source : ι}
    {component : QuittingEssentialAPSReachableSCC reward source}
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

/-- **Multivalued essential-APS SCC execution.**

The conclusion contains one chronological object: a finite absorbing execution,
an infinite component-charged execution, or a finite execution reaching a typed
obstruction.  A globally balanced circulation is not an input and cannot
satisfy any edge of the returned path. -/
theorem quittingEssentialAPSSCC_executionOutcome
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {source : ι}
    (component : QuittingEssentialAPSReachableSCC reward source)
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

/-- Forgetting SCC membership and the charge lower bound turns the recurrent
branch into the existing essential-APS infinite-run object. -/
theorem ChronologicalInfinitePath.toQuittingEssentialAPSInfiniteRun
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {source : ι}
    {component : QuittingEssentialAPSReachableSCC reward source}
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

/-- Component-local charge gives a linear lower bound on every prefix. -/
theorem ChronologicalInfinitePath.prefixCharge_lowerBound
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {source : ι}
    {component : QuittingEssentialAPSReachableSCC reward source}
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

/-- If the component-local charge floor is positive, the same chronological
recurrent path reaches every finite charge target. -/
theorem ChronologicalInfinitePath.exists_prefixCharge_ge
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {source : ι}
    {component : QuittingEssentialAPSReachableSCC reward source}
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
