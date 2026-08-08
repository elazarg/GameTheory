/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.EssentialAPS.InfiniteRun

/-!
# Multivalued essential-APS components

The existing essential-APS execution theorem assumes that every active owner
has one live successor fiber.  This file keeps that API unchanged and defines
the objects needed when several successor fibers are live.

The distinction between algebraic and executable data is explicit.  Membership
in the full convex-hull APS operator is not an edge.  An executable edge carries
one selected successor, one mass in `[0,1)`, and the exact singleton-arc
identity.  A charged edge additionally has a prescribed positive mass floor.

An SCC is owner-graph data.  Executability is separate: graph reachability or a
balanced occupation does not manufacture the required singleton-arc witness.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The Flesch successor relation restricted to a displayed finite owner set. -/
def QuittingEssentialAPSInternalSuccessor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (vertices : Finset ι) (source target : ι) : Prop :=
  source ∈ vertices ∧ target ∈ vertices ∧
    QuittingFleschSuccessor reward source target

/-- A finite strongly connected component of the Flesch successor graph.

The field records graph connectivity only.  In particular it does not assert
that any continuation value has a segment witness along an internal edge. -/
structure QuittingEssentialAPSSCC
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  vertices : Finset ι
  nonempty : vertices.Nonempty
  stronglyConnected : ∀ {source target},
    source ∈ vertices → target ∈ vertices →
      Relation.ReflTransGen
        (QuittingEssentialAPSInternalSuccessor reward vertices)
        source target

/-- A continuation value currently located at one owner of an SCC. -/
structure QuittingEssentialAPSSCCNode
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (family : ι → Set (Payoff ι))
    (component : QuittingEssentialAPSSCC reward) where
  owner : ι
  owner_mem : owner ∈ component.vertices
  value : Payoff ι
  value_mem : value ∈ family owner

/-- One chronological singleton-flow edge inside an SCC.

This is the path-compatible relation, not the full convex-hull APS operator. -/
structure QuittingEssentialAPSSCCStep
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (family : ι → Set (Payoff ι))
    (component : QuittingEssentialAPSSCC reward)
    (source target : QuittingEssentialAPSSCCNode reward family component) where
  edge : QuittingFleschSuccessor reward source.owner target.owner
  mass : ℝ
  mass_mem : mass ∈ Set.Ico (0 : ℝ) 1
  arc : source.value = quittingSingletonArcPayoff mass
    (quittingSoloReward reward source.owner) target.value

/-- Every witnessed SCC step is an edge of the finite internal successor
relation. -/
theorem QuittingEssentialAPSSCCStep.internalSuccessor
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {family : ι → Set (Payoff ι)}
    {component : QuittingEssentialAPSSCC reward}
    {source target : QuittingEssentialAPSSCCNode reward family component}
    (step : QuittingEssentialAPSSCCStep reward family component source target) :
    QuittingEssentialAPSInternalSuccessor reward component.vertices
      source.owner target.owner :=
  ⟨source.owner_mem, target.owner_mem, step.edge⟩

/-- The ordinary executable-edge relation. -/
def QuittingEssentialAPSSCCStepRel
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (family : ι → Set (Payoff ι))
    (component : QuittingEssentialAPSSCC reward)
    (source target : QuittingEssentialAPSSCCNode reward family component) : Prop :=
  Nonempty (QuittingEssentialAPSSCCStep reward family component source target)

/-- Executable edges whose singleton mass is at least `chargeFloor`. -/
def QuittingEssentialAPSChargedSCCStepRel
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (family : ι → Set (Payoff ι))
    (component : QuittingEssentialAPSSCC reward)
    (chargeFloor : ℝ)
    (source target : QuittingEssentialAPSSCCNode reward family component) : Prop :=
  ∃ step : QuittingEssentialAPSSCCStep reward family component source target,
    chargeFloor ≤ step.mass

/-- Forgetting the charge lower bound retains an executable segment. -/
theorem QuittingEssentialAPSChargedSCCStepRel.toStepRel
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {family : ι → Set (Payoff ι)}
    {component : QuittingEssentialAPSSCC reward}
    {chargeFloor : ℝ}
    {source target : QuittingEssentialAPSSCCNode reward family component}
    (step : QuittingEssentialAPSChargedSCCStepRel reward family component
      chargeFloor source target) :
    QuittingEssentialAPSSCCStepRel reward family component source target := by
  rcases step with ⟨witness, _⟩
  exact ⟨witness⟩

/-- A component node is terminal when its value is the viable solo endpoint of
its current owner.  Executing that owner with probability one is then the
absorbing exit following the finite segment path. -/
def QuittingEssentialAPSSCCNode.IsTerminal
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {family : ι → Set (Payoff ι)}
    {component : QuittingEssentialAPSSCC reward}
    (node : QuittingEssentialAPSSCCNode reward family component) : Prop :=
  node.value ∈ quittingEssentialAPSTerminal reward node.owner

/-- A proper APS segment into one internal successor fiber supplies an actual
SCC edge.  This is the direct adapter from the existing proper-prefix API. -/
theorem exists_quittingEssentialAPSSCCStep_of_properPrefix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (family : ι → Set (Payoff ι))
    (component : QuittingEssentialAPSSCC reward)
    (source : QuittingEssentialAPSSCCNode reward family component)
    {successor : ι} (hsuccessor : successor ∈ component.vertices)
    (hedge : QuittingFleschSuccessor reward source.owner successor)
    (hproper : source.value ∈
      quittingProperEssentialAPSPrefix reward source.owner (family successor)) :
    ∃ target : QuittingEssentialAPSSCCNode reward family component,
      QuittingEssentialAPSSCCStepRel reward family component source target := by
  rcases hproper with
    ⟨_hviable, mass, hmass, next, hnext, harc, _hactive⟩
  let target : QuittingEssentialAPSSCCNode reward family component := {
    owner := successor
    owner_mem := hsuccessor
    value := next
    value_mem := hnext }
  refine ⟨target, ⟨{
    edge := hedge
    mass := mass
    mass_mem := ⟨hmass.1.le, hmass.2⟩
    arc := harc }⟩⟩

/-- Zero-mass propagation is also an exact executable edge when the unchanged
value belongs to the successor fiber. -/
theorem quittingEssentialAPSSCCStepRel_zero_of_successor_mem
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (family : ι → Set (Payoff ι))
    (component : QuittingEssentialAPSSCC reward)
    (source : QuittingEssentialAPSSCCNode reward family component)
    {successor : ι} (hsuccessor : successor ∈ component.vertices)
    (hedge : QuittingFleschSuccessor reward source.owner successor)
    (hnext : source.value ∈ family successor) :
    ∃ target : QuittingEssentialAPSSCCNode reward family component,
      QuittingEssentialAPSSCCStepRel reward family component source target := by
  let target : QuittingEssentialAPSSCCNode reward family component := {
    owner := successor
    owner_mem := hsuccessor
    value := source.value
    value_mem := hnext }
  refine ⟨target, ⟨{
    edge := hedge
    mass := 0
    mass_mem := ⟨le_rfl, zero_lt_one⟩
    arc := ?_ }⟩⟩
  funext who
  simpa [quittingSingletonArcPayoff, target]

/-- A finite chronological execution may use any witnessed SCC segment. -/
def QuittingEssentialAPSSCCFiniteExecution
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (family : ι → Set (Payoff ι))
    (component : QuittingEssentialAPSSCC reward)
    (start finish : QuittingEssentialAPSSCCNode reward family component) : Prop :=
  Relation.ReflTransGen
    (QuittingEssentialAPSSCCStepRel reward family component)
    start finish

/-- A finite chronological prefix all of whose segments meet one charge floor. -/
def QuittingEssentialAPSChargedSCCFiniteExecution
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (family : ι → Set (Payoff ι))
    (component : QuittingEssentialAPSSCC reward)
    (chargeFloor : ℝ)
    (start finish : QuittingEssentialAPSSCCNode reward family component) : Prop :=
  Relation.ReflTransGen
    (QuittingEssentialAPSChargedSCCStepRel reward family component chargeFloor)
    start finish

/-- A charged prefix is, after forgetting its lower bounds, an ordinary
chronological execution. -/
theorem QuittingEssentialAPSChargedSCCFiniteExecution.toFiniteExecution
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {family : ι → Set (Payoff ι)}
    {component : QuittingEssentialAPSSCC reward}
    {chargeFloor : ℝ}
    {start finish : QuittingEssentialAPSSCCNode reward family component}
    (execution : QuittingEssentialAPSChargedSCCFiniteExecution reward family
      component chargeFloor start finish) :
    QuittingEssentialAPSSCCFiniteExecution reward family component
      start finish := by
  induction execution with
  | refl => exact .refl
  | tail hab hbc ih =>
      exact Relation.ReflTransGen.tail ih
        (QuittingEssentialAPSChargedSCCStepRel.toStepRel hbc)

/-- A finite executable path ending at a viable absorbing solo endpoint. -/
structure QuittingEssentialAPSSCCAbsorbingExit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (family : ι → Set (Payoff ι))
    (component : QuittingEssentialAPSSCC reward)
    (initial : QuittingEssentialAPSSCCNode reward family component) where
  terminal : QuittingEssentialAPSSCCNode reward family component
  execution : QuittingEssentialAPSSCCFiniteExecution reward family component
    initial terminal
  terminal_mem : terminal.IsTerminal

/-- An infinite chronological path with one explicit exact APS segment per
stage and a lower charge bound on every segment. -/
structure QuittingEssentialAPSSCCInfiniteExecution
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (family : ι → Set (Payoff ι))
    (component : QuittingEssentialAPSSCC reward)
    (chargeFloor : ℝ)
    (initial : QuittingEssentialAPSSCCNode reward family component) where
  node : ℕ → QuittingEssentialAPSSCCNode reward family component
  initial_eq : node 0 = initial
  step : ∀ time, QuittingEssentialAPSSCCStep reward family component
    (node time) (node (time + 1))
  charged : ∀ time, chargeFloor ≤ (step time).mass

/-- Failure of charged internal execution retains whether there is no physical
segment at all or only segments below the requested charge floor. -/
inductive QuittingEssentialAPSSCCObstruction
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (family : ι → Set (Payoff ι))
    (component : QuittingEssentialAPSSCC reward)
    (chargeFloor : ℝ)
    (state : QuittingEssentialAPSSCCNode reward family component) : Type
  | noExecutableSegment
      (nonterminal : ¬ state.IsTerminal)
      (noStep : ¬ ∃ target,
        QuittingEssentialAPSSCCStepRel reward family component state target)
  | chargeGap
      (nonterminal : ¬ state.IsTerminal)
      (hasStep : ∃ target,
        QuittingEssentialAPSSCCStepRel reward family component state target)
      (noChargedStep : ¬ ∃ target,
        QuittingEssentialAPSChargedSCCStepRel reward family component
          chargeFloor state target)

/-- A typed obstruction reached by one finite chronological charged path. -/
structure QuittingEssentialAPSReachableSCCObstruction
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (family : ι → Set (Payoff ι))
    (component : QuittingEssentialAPSSCC reward)
    (chargeFloor : ℝ)
    (initial : QuittingEssentialAPSSCCNode reward family component) where
  state : QuittingEssentialAPSSCCNode reward family component
  execution : QuittingEssentialAPSChargedSCCFiniteExecution reward family
    component chargeFloor initial state
  obstruction : QuittingEssentialAPSSCCObstruction reward family component
    chargeFloor state

/-- The three typed outcomes of multivalued SCC execution. -/
inductive QuittingEssentialAPSSCCExecutionOutcome
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (family : ι → Set (Payoff ι))
    (component : QuittingEssentialAPSSCC reward)
    (chargeFloor : ℝ)
    (initial : QuittingEssentialAPSSCCNode reward family component) : Type
  | absorbingExit
      (exit : QuittingEssentialAPSSCCAbsorbingExit reward family component
        initial)
  | recurrentPath
      (execution : QuittingEssentialAPSSCCInfiniteExecution reward family
        component chargeFloor initial)
  | obstructed
      (obstruction : QuittingEssentialAPSReachableSCCObstruction reward family
        component chargeFloor initial)

end GameTheory
