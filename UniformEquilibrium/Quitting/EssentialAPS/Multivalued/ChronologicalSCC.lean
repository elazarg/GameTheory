/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.EssentialAPS.InfiniteRun
import Math.Probability.PhaseOccupationDuality

/-!
# Chronological execution in a multivalued essential-APS SCC

A balanced occupation is not a play path.  This module keeps three layers
separate:

* a finite reachable strongly connected component of the exact Flesch graph;
* witnessed singleton-arc segments inside that component; and
* one chronological finite or infinite execution assembled only from those
  witnesses.

Failure to find a witnessed segment is retained as typed data.  A second
obstruction records that segments exist but none has the requested local
charge.  No convex-hull membership or cancellation across recurrent
components is silently promoted to an edge.
-/

noncomputable section

namespace GameTheory

open StochasticGame

universe u

/-- Reflexive-transitive closure of a supplied successor relation. -/
inductive FiniteSuccessorPath {alpha : Type u}
    (edge : alpha → alpha → Prop) : alpha → alpha → Prop
  | refl (vertex : alpha) : FiniteSuccessorPath edge vertex vertex
  | tail {source current next : alpha} :
      FiniteSuccessorPath edge source current →
      edge current next →
      FiniteSuccessorPath edge source next

/-- Finite reachability generated only by witnessed charged steps. -/
inductive ChargedExecutableReach {state : Type u}
    (Step : state → ℝ → state → Prop) (start : state) : state → Prop
  | refl : ChargedExecutableReach Step start start
  | tail {current next : state} :
      ChargedExecutableReach Step start current →
      (∃ mass, Step current mass next) →
      ChargedExecutableReach Step start next

/-- One coherent infinite chronological execution. -/
structure ChronologicalInfinitePath {state : Type u}
    (Step : state → ℝ → state → Prop) (start : state) where
  vertex : ℕ → state
  mass : ℕ → ℝ
  initial : vertex 0 = start
  step : ∀ time, Step (vertex time) (mass time) (vertex (time + 1))

/-- Exit, recurrent execution, or a reached typed obstruction. -/
inductive ChronologicalExecutionOutcome {state : Type u}
    (Terminal : state → Prop)
    (Step : state → ℝ → state → Prop)
    (Obstruction : state → Prop)
    (start : state) : Prop
  | absorbing (endpoint : state) :
      ChargedExecutableReach Step start endpoint →
      Terminal endpoint →
      ChronologicalExecutionOutcome Terminal Step Obstruction start
  | recurrent :
      ChronologicalInfinitePath Step start →
      ChronologicalExecutionOutcome Terminal Step Obstruction start
  | obstructed (endpoint : state) :
      ChargedExecutableReach Step start endpoint →
      Obstruction endpoint →
      ChronologicalExecutionOutcome Terminal Step Obstruction start

/-- **Generic chronological execution trichotomy.**

If a reachable terminal exists, retain a finite witnessed path to it.  If every
reachable state has a witnessed successor, recursively choose one coherent
infinite path.  Otherwise retain the first missing-successor fact as a typed
obstruction at a reached state. -/
theorem chronologicalExecutionOutcome_of_classifier
    {state : Type u}
    (Terminal : state → Prop)
    (Step : state → ℝ → state → Prop)
    (Obstruction : state → Prop)
    (start : state)
    (classify : ∀ current,
      (¬ ∃ mass next, Step current mass next) → Obstruction current) :
    ChronologicalExecutionOutcome Terminal Step Obstruction start := by
  classical
  by_cases hterminal :
      ∃ endpoint,
        ChargedExecutableReach Step start endpoint ∧ Terminal endpoint
  · obtain ⟨endpoint, hreach, hend⟩ := hterminal
    exact .absorbing endpoint hreach hend
  by_cases hclosed : ∀ current,
      ChargedExecutableReach Step start current →
        ∃ mass next, Step current mass next
  · let Reachable :=
      {current : state // ChargedExecutableReach Step start current}
    have hnext : ∀ current : Reachable,
        ∃ mass next, Step current.1 mass next := by
      intro current
      exact hclosed current.1 current.2
    let chosenMass : Reachable → ℝ :=
      fun current => Classical.choose (hnext current)
    let chosenNext : Reachable → state :=
      fun current => Classical.choose (Classical.choose_spec (hnext current))
    have chosenStep (current : Reachable) :
        Step current.1 (chosenMass current) (chosenNext current) :=
      Classical.choose_spec (Classical.choose_spec (hnext current))
    let nextReachable : Reachable → Reachable := fun current =>
      ⟨chosenNext current,
        ChargedExecutableReach.tail current.2
          ⟨chosenMass current, chosenStep current⟩⟩
    let orbit : ℕ → Reachable := fun time =>
      Nat.rec
        (motive := fun _ => Reachable)
        ⟨start, ChargedExecutableReach.refl⟩
        (fun _ current => nextReachable current)
        time
    refine .recurrent {
      vertex := fun time => (orbit time).1
      mass := fun time => chosenMass (orbit time)
      initial := rfl
      step := ?_ }
    intro time
    have horbit : orbit (time + 1) = nextReachable (orbit time) := rfl
    rw [horbit]
    exact chosenStep (orbit time)
  · push_neg at hclosed
    obtain ⟨endpoint, hreach, hfailure⟩ := hclosed
    have hnone : ¬ ∃ mass next, Step endpoint mass next := by
      intro hstep
      obtain ⟨mass, next, hstep⟩ := hstep
      exact hfailure mass next hstep
    exact .obstructed endpoint hreach (classify endpoint hnone)

section EssentialAPS

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A finite Flesch-successor SCC with a displayed entry reachable from an
external source. -/
structure QuittingEssentialAPSReachableSCC
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : ι) where
  carrier : Finset ι
  entry : ι
  entry_mem : entry ∈ carrier
  source_reaches_entry :
    FiniteSuccessorPath (QuittingFleschSuccessor reward) source entry
  stronglyConnected : ∀ {first second : ι},
    first ∈ carrier → second ∈ carrier →
      FiniteSuccessorPath (QuittingFleschSuccessor reward) first second

/-- A payoff-labelled state in the selected component. -/
structure QuittingEssentialAPSSCCState
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {source : ι}
    (component : QuittingEssentialAPSReachableSCC reward source)
    (family : ι → Set (Payoff ι)) where
  owner : ι
  owner_mem : owner ∈ component.carrier
  value : Payoff ι
  value_mem : value ∈ family owner

/-- The labelled state at the displayed SCC entry. -/
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

/-- One exact executable singleton-arc segment internal to the chosen SCC. -/
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

/-- A witnessed internal segment carrying at least `eta` local charge. -/
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

/-- A missing charged edge is classified without pretending that algebraic APS
membership produced a segment. -/
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

The output is a finite absorbing exit, one coherent infinite path carrying at
least `eta` charge at every component edge, or a typed obstruction reached by
a finite executable prefix. -/
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
      path.mass
      (fun time => (path.vertex time).value) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using congrArg (fun current => current.value) path.initial
  · intro time
    exact (path.vertex time).value_mem
  · intro time
    exact ⟨(path.step time).1.mass_mem, (path.step time).1.arc⟩

/-- Componentwise charge gives a linear lower bound on every prefix. -/
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
      ∑ time ∈ Finset.range horizon, path.mass time := by
  induction horizon with
  | zero => simp
  | succ horizon ih =>
      rw [Finset.sum_range_succ]
      have hcast : ((horizon + 1 : ℕ) : ℝ) * eta =
          (horizon : ℝ) * eta + eta := by
        push_cast
        ring
      rw [hcast]
      exact add_le_add ih (path.step horizon).2

/-- For `eta > 0`, one chronological recurrent path reaches every finite
charge target. -/
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
      target ≤ ∑ time ∈ Finset.range horizon, path.mass time := by
  obtain ⟨horizon, hhorizon⟩ := exists_nat_gt (target / eta)
  refine ⟨horizon, le_trans ?_ (path.prefixCharge_lowerBound horizon)⟩
  exact ((div_lt_iff₀ heta).mp hhorizon).le

end EssentialAPS

/-! ## Regression: global occupation balance across SCCs is not execution -/

namespace EssentialAPSMultivaluedOccupationRegression

open Math.Probability
open Math.Probability.PhaseOccupationDuality

/-- Two disjoint closed recurrent classes. -/
inductive ClosedClass
  | positive
  | negative
  deriving DecidableEq, Fintype

/-- Identity dynamics: a path can never move between the two classes. -/
def kernel (_ : Unit) (current : ClosedClass) (_ : Unit) : PMF ClosedClass :=
  PMF.pure current

/-- One-phase schedule. -/
def word : Phase 1 → Unit := fun _ => ()

/-- Half of the global occupation is placed in each closed class. -/
def occupation : PhaseOccupation 1 ClosedClass Unit :=
  fun _ _ _ => (1 : ℝ) / 2

/-- The half-half occupation satisfies the exact phase-flow law. -/
theorem occupation_pointwiseFlow :
    HasPointwisePhaseShiftFlow kernel word occupation := by
  intro phase current
  cases current <;> simp [kernel, occupation]

/-- It is therefore a genuine feasible global phase occupation. -/
theorem occupation_feasible :
    IsPhaseOccupation kernel word occupation := by
  refine ⟨?_, ?_,
    hasPhaseShiftFlow_of_hasPointwisePhaseShiftFlow occupation_pointwiseFlow⟩
  · intro phase current action
    norm_num [occupation]
  · simp [phaseSum, occupation]

/-- Opposite component charges. -/
def charge : ClosedClass → ℝ
  | .positive => 1
  | .negative => -1

/-- The global occupation cancels the two SCC charges. -/
theorem global_occupation_charge_zero :
    phaseSum (fun phase current action =>
      occupation phase current action * charge current) = 0 := by
  simp [phaseSum, occupation, charge]

/-- Chronological identity edges. -/
def executableEdge (current next : ClosedClass) : Prop := next = current

/-- A path selected in the positive SCC stays there. -/
theorem path_started_positive_stays_positive
    (state : ℕ → ClosedClass)
    (hinitial : state 0 = .positive)
    (hstep : ∀ time, executableEdge (state time) (state (time + 1))) :
    ∀ time, state time = .positive := by
  intro time
  induction time with
  | zero => exact hinitial
  | succ time ih => exact (hstep time).trans ih

/-- Its prefix charge is its length, not the globally cancelled value zero. -/
theorem positive_path_prefix_charge
    (state : ℕ → ClosedClass)
    (hinitial : state 0 = .positive)
    (hstep : ∀ time, executableEdge (state time) (state (time + 1)))
    (horizon : ℕ) :
    ∑ time ∈ Finset.range horizon, charge (state time) = (horizon : ℝ) := by
  have hpositive := path_started_positive_stays_positive state hinitial hstep
  calc
    ∑ time ∈ Finset.range horizon, charge (state time) =
        ∑ _time ∈ Finset.range horizon, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro time htime
      simp [hpositive time, charge]
    _ = (horizon : ℝ) := by simp

/-- Regression package: global balance and incompatible chronological behavior
hold simultaneously. -/
theorem global_balance_does_not_supply_chronological_cancellation :
    (phaseSum (fun phase current action =>
        occupation phase current action * charge current) = 0) ∧
      ∀ (state : ℕ → ClosedClass),
        state 0 = .positive →
        (∀ time, executableEdge (state time) (state (time + 1))) →
        ∀ horizon : ℕ,
          ∑ time ∈ Finset.range horizon, charge (state time) =
            (horizon : ℝ) := by
  exact ⟨global_occupation_charge_zero,
    fun state hinitial hstep horizon =>
      positive_path_prefix_charge state hinitial hstep horizon⟩

end EssentialAPSMultivaluedOccupationRegression
end GameTheory
