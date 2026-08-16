/-
# Experimental graphical requisite-observation criterion for MAIDs

This experiment leaves the canonical MAID syntax and evaluator unchanged.  A
`UtilityView` exposes one synthetic utility sink per owner and proves that the
owner's canonical utility depends only on the named assignment coordinates.
The probabilistic graph uses causal parents at chance nodes and observed
parents at decision nodes: an unobserved ordering predecessor is not thereby a
probabilistic input to a decision rule.

`DConnected` uses the standard ancestral-moral characterization of
d-connection.  Its conditioning argument remains a set throughout.  The
singleton observation criterion says that the observation is *requisite*, in
other words not graphically ignorable, when it remains connected to the
owner's utility sink after conditioning on the decision and every other
observation, and that sink is downstream of the decision.

The one-sink-per-owner view is deliberately conservative relative to
Koller--Milch's multiple local utility nodes: moralizing one combined sink can
join parents that belong to distinct utility terms.  This spike therefore
validates only the graph machinery and hostile distinction, not an exact
completeness API for graphical relevance.

No semantic soundness theorem is asserted here.  In particular, graphical
non-requisiteness cannot force an arbitrary policy to ignore an input; the
later semantic theorem must construct an equally good factoring policy or
take factorization as a hypothesis.
-/

import GameTheory.Languages.MAID.Basic

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.MAIDRequisiteObservation

open GameTheory.Languages.MAID

universe uPlayer uNode uValue

variable {Player : Type uPlayer} {Node : Type uNode}
variable {diagram : Structure Player Node}

/-- The probabilistic parents seen by the factor at a node.  Chance factors
use all causal parents, while decision factors use exactly their observations.
-/
def effectiveParents (diagram : Structure Player Node) (node : Node) :
    Finset Node :=
  match diagram.kind node with
  | .chance => diagram.parents node
  | .decision _ => diagram.observedParents node

/-- A proved graph-facing view of the canonical external utility.  The
synthetic sink for an owner has precisely `parents owner` as its parents.

Combining an owner's utility into one sink can conservatively add moral edges
between coordinates belonging to separate additive utility terms. -/
structure UtilityView (semantics : Semantics diagram) where
  parents : Player → Finset Node
  payoff : (owner : Player) → Config diagram (parents owner) → ℝ
  utility_eq : ∀ (owner : Player) (assignment : Assignment diagram),
    semantics.utility owner assignment =
      payoff owner (Assignment.restrict diagram assignment (parents owner))

/-- Variable nodes together with one synthetic utility sink per owner. -/
inductive GraphNode (Player : Type uPlayer) (Node : Type uNode)
  | base (node : Node)
  | utility (owner : Player)
  deriving DecidableEq

namespace UtilityView

variable {semantics : Semantics diagram}

/-- Parent sets in the graph augmented by the proved utility sinks. -/
def graphParents (view : UtilityView semantics)
    [DecidableEq Player] [DecidableEq Node] :
    GraphNode Player Node → Finset (GraphNode Player Node)
  | .base node =>
      (effectiveParents diagram node).image GraphNode.base
  | .utility owner =>
      (view.parents owner).image GraphNode.base

/-- A directed edge of the graph augmented by utility sinks. -/
def DirectedEdge (view : UtilityView semantics)
    [DecidableEq Player] [DecidableEq Node]
    (parent child : GraphNode Player Node) : Prop :=
  parent ∈ view.graphParents child

/-- Directed ancestry, allowing the node itself. -/
def AncestorOrSelf (view : UtilityView semantics)
    [DecidableEq Player] [DecidableEq Node]
    (ancestor descendant : GraphNode Player Node) : Prop :=
  Relation.ReflTransGen view.DirectedEdge ancestor descendant

/-- Membership in the ancestral closure of two query endpoints and the whole
conditioning set. -/
def InAncestralClosure (view : UtilityView semantics)
    [DecidableEq Player] [DecidableEq Node]
    (source target : GraphNode Player Node)
    (conditioned : Finset (GraphNode Player Node))
    (node : GraphNode Player Node) : Prop :=
  ∃ root ∈ insert source (insert target conditioned),
    view.AncestorOrSelf node root

/-- Adjacency in the ancestral moral graph after deleting every conditioned
node.  Besides underlying directed edges, two parents of the same ancestral
child are adjacent. -/
def MoralAdjacent (view : UtilityView semantics)
    [DecidableEq Player] [DecidableEq Node]
    (source target : GraphNode Player Node)
    (conditioned : Finset (GraphNode Player Node))
    (first second : GraphNode Player Node) : Prop :=
  first ≠ second ∧
    first ∉ conditioned ∧
    second ∉ conditioned ∧
    view.InAncestralClosure source target conditioned first ∧
    view.InAncestralClosure source target conditioned second ∧
    (view.DirectedEdge first second ∨
      view.DirectedEdge second first ∨
      ∃ child,
        view.InAncestralClosure source target conditioned child ∧
        view.DirectedEdge first child ∧
        view.DirectedEdge second child)

/-- D-connection through the ancestral moral graph.  The evidence remains a
set, rather than being collapsed to a singleton during the construction. -/
def DConnected (view : UtilityView semantics)
    [DecidableEq Player] [DecidableEq Node]
    (source target : GraphNode Player Node)
    (conditioned : Finset (GraphNode Player Node)) : Prop :=
  source ∉ conditioned ∧
    target ∉ conditioned ∧
    Relation.ReflTransGen
      (view.MoralAdjacent source target conditioned) source target

/-- Condition on the decision and on every observation outside the entire set
being tested.  Keeping `removed` set-valued is load-bearing: the exact
criterion removes all of `X` from the conditioning set at once. -/
def observationConditioningSet [DecidableEq Player] [DecidableEq Node]
    {owner : Player} (site : DecisionSite diagram owner)
    (removed : Finset Node) : Finset (GraphNode Player Node) :=
  insert (.base site.1)
    ((diagram.observedParents site.1 \ removed).image
      GraphNode.base)

/-- Singleton specialization of `observationConditioningSet`. -/
def observationConditioning [DecidableEq Player] [DecidableEq Node]
    {owner : Player} (site : DecisionSite diagram owner)
    (observation : Node) : Finset (GraphNode Player Node) :=
  observationConditioningSet site {observation}

@[simp]
theorem observationConditioning_eq [DecidableEq Player] [DecidableEq Node]
    {owner : Player} (site : DecisionSite diagram owner)
    (observation : Node) :
    observationConditioning site observation =
      insert (.base site.1)
        ((diagram.observedParents site.1).erase observation |>.image
          GraphNode.base) := by
  simp [observationConditioning, observationConditioningSet,
    Finset.sdiff_singleton_eq_erase]

/-- The set-valued graphical ignorability test against the conservative owner
sink.  It says either the owner sink is not relevant to the decision at all,
or every removed observation is d-separated from it after removing the whole
set from the conditioning context.  This remains a graph predicate only; no
semantic soundness theorem is claimed by the experiment. -/
def AreGraphicallyIgnorable (view : UtilityView semantics)
    [DecidableEq Player] [DecidableEq Node]
    {owner : Player} (site : DecisionSite diagram owner)
    (removed : Finset Node) : Prop :=
  removed ⊆ diagram.observedParents site.1 ∧
    (¬ view.AncestorOrSelf (.base site.1) (.utility owner) ∨
      ∀ observation ∈ removed,
        ¬ view.DConnected (.base observation) (.utility owner)
          (observationConditioningSet site removed))

/-- A singleton observation is requisite (the complement of graphically
ignorable) when it is observed at the decision and d-connected to that
owner's proved utility sink conditional on the decision and all other
observations. -/
def IsRequisiteObservation (view : UtilityView semantics)
    [DecidableEq Player] [DecidableEq Node]
    {owner : Player} (site : DecisionSite diagram owner)
    (observation : Node) : Prop :=
  observation ∈ diagram.observedParents site.1 ∧
    view.AncestorOrSelf (.base site.1) (.utility owner) ∧
    view.DConnected (.base observation) (.utility owner)
      (observationConditioning site observation)

/-- On a declared observation, the public singleton terminology is literally
the complement of the set-valued graphical ignorability test. -/
theorem isRequisiteObservation_iff_not_areGraphicallyIgnorable
    (view : UtilityView semantics)
    [DecidableEq Player] [DecidableEq Node]
    {owner : Player} (site : DecisionSite diagram owner)
    (observation : Node)
    (hobserved : observation ∈ diagram.observedParents site.1) :
    view.IsRequisiteObservation site observation ↔
      ¬ view.AreGraphicallyIgnorable site {observation} := by
  simp [IsRequisiteObservation, AreGraphicallyIgnorable,
    observationConditioning, observationConditioningSet, hobserved]

end UtilityView

/-! ## A one-edge hostile pair -/

inductive ExampleNode
  | signal
  | decision
  | reward
  deriving DecidableEq, Fintype

def exampleObservedParents : ExampleNode → Finset ExampleNode
  | .signal => ∅
  | .decision => {.signal}
  | .reward => {.decision}

namespace Nonrequisite

def parents : ExampleNode → Finset ExampleNode
  | .signal => ∅
  | .decision => {.signal}
  | .reward => {.decision}

def topologicalParents : GameTheory.Math.DAG.TopologicalOrder parents where
  order := [.signal, .decision, .reward]
  nodup := by decide
  complete node := by cases node <;> simp
  respects := by
    intro index parent hparent
    fin_cases index
    · simp [parents] at hparent
    · have hsignal : parent = .signal := by
        simpa [parents] using hparent
      subst parent
      exact ⟨0, by decide, rfl⟩
    · have hdecision : parent = .decision := by
        simpa [parents] using hparent
      subst parent
      exact ⟨1, by decide, rfl⟩

@[reducible]
def model : Structure Unit ExampleNode where
  kind
    | .signal => .chance
    | .decision => .decision ()
    | .reward => .chance
  parents := parents
  observedParents := exampleObservedParents
  Value _ := Bool
  observed_sub node := by
    cases node <;> simp [parents, exampleObservedParents]
  observed_eq_of_chance node hchance := by
    cases node <;> simp [parents, exampleObservedParents] at hchance ⊢
  acyclic := GameTheory.Math.DAG.acyclic_of_topologicalOrder
    topologicalParents

@[reducible]
def semantics : Semantics model where
  defaultValue _ := false
  chanceLaw node hchance _ := by
    cases node with
    | signal => exact GameTheory.Math.Probability.FinDist.pure false
    | decision => simp at hchance
    | reward => exact GameTheory.Math.Probability.FinDist.pure false
  utility _ assignment := if assignment .reward then 1 else 0

def utilityView : UtilityView (diagram := model) semantics where
  parents _ := {.reward}
  payoff _ configuration :=
    if configuration ⟨.reward, by simp⟩ then 1 else 0
  utility_eq _ _ := rfl

def decisionSite : DecisionSite model () := ⟨.decision, rfl⟩

/-- In the chain `signal → decision → reward → utility`, conditioning on the
decision blocks the only path from the observation to utility. -/
theorem signal_not_requisite :
    ¬ utilityView.IsRequisiteObservation decisionSite .signal := by
  rintro ⟨_, _, _, _, connection⟩
  have isolated : ∀ next,
      ¬ utilityView.MoralAdjacent
        (.base .signal) (.utility ())
        (UtilityView.observationConditioning decisionSite .signal)
        (.base .signal) next := by
    intro next hadjacent
    rcases hadjacent with
      ⟨hne, _, hnextOpen, _, _, hforward | hbackward | hcoparents⟩
    · cases next with
      | base node =>
          cases node with
          | signal => exact hne rfl
          | decision =>
              exact hnextOpen (by
                simp [UtilityView.observationConditioning,
                  UtilityView.observationConditioningSet, decisionSite])
          | reward =>
              simp [UtilityView.DirectedEdge, UtilityView.graphParents,
                effectiveParents, parents] at hforward
      | utility owner =>
          cases owner
          simp [UtilityView.DirectedEdge, UtilityView.graphParents,
            utilityView, model] at hforward
    · cases next with
      | base node =>
          cases node <;>
            simp [UtilityView.DirectedEdge, UtilityView.graphParents,
              effectiveParents, parents] at hbackward
      | utility owner =>
          cases owner
          simp [UtilityView.DirectedEdge, UtilityView.graphParents,
            effectiveParents, parents] at hbackward
    · obtain ⟨child, _, hsignalParent, hnextParent⟩ := hcoparents
      cases child with
      | base node =>
          cases node with
          | signal =>
              simp [UtilityView.DirectedEdge, UtilityView.graphParents,
                effectiveParents, parents] at hsignalParent
          | decision =>
              have hnext : next = .base .signal := by
                cases next with
                | base nextNode =>
                    cases nextNode <;>
                      simp [UtilityView.DirectedEdge,
                        UtilityView.graphParents, effectiveParents,
                        exampleObservedParents] at hnextParent ⊢
                | utility owner =>
                    cases owner
                    simp [UtilityView.DirectedEdge,
                      UtilityView.graphParents, effectiveParents,
                      exampleObservedParents] at hnextParent
              exact hne hnext.symm
          | reward =>
              simp [UtilityView.DirectedEdge, UtilityView.graphParents,
                effectiveParents, parents] at hsignalParent
      | utility owner =>
          cases owner
          simp [UtilityView.DirectedEdge, UtilityView.graphParents,
            utilityView, model] at hsignalParent
  rcases Relation.ReflTransGen.cases_head connection with heq | ⟨next, hstep, _⟩
  · cases heq
  · exact isolated next hstep

end Nonrequisite

namespace Requisite

/-- The control differs by the single additional edge `signal → reward`. -/
def parents : ExampleNode → Finset ExampleNode
  | .signal => ∅
  | .decision => {.signal}
  | .reward => {.signal, .decision}

def topologicalParents : GameTheory.Math.DAG.TopologicalOrder parents where
  order := [.signal, .decision, .reward]
  nodup := by decide
  complete node := by cases node <;> simp
  respects := by
    intro index parent hparent
    fin_cases index
    · simp [parents] at hparent
    · have hsignal : parent = .signal := by
        simpa [parents] using hparent
      subst parent
      exact ⟨0, by decide, rfl⟩
    · cases parent with
      | signal => exact ⟨0, by decide, rfl⟩
      | decision => exact ⟨1, by decide, rfl⟩
      | reward => simp [parents] at hparent

@[reducible]
def model : Structure Unit ExampleNode where
  kind
    | .signal => .chance
    | .decision => .decision ()
    | .reward => .chance
  parents := parents
  observedParents
    | .signal => ∅
    | .decision => {.signal}
    | .reward => {.signal, .decision}
  Value _ := Bool
  observed_sub node := by cases node <;> simp [parents]
  observed_eq_of_chance node hchance := by
    cases node <;> simp [parents] at hchance ⊢
  acyclic := GameTheory.Math.DAG.acyclic_of_topologicalOrder
    topologicalParents

@[reducible]
def semantics : Semantics model where
  defaultValue _ := false
  chanceLaw node hchance _ := by
    cases node with
    | signal => exact GameTheory.Math.Probability.FinDist.pure false
    | decision => simp at hchance
    | reward => exact GameTheory.Math.Probability.FinDist.pure false
  utility _ assignment := if assignment .reward then 1 else 0

def utilityView : UtilityView (diagram := model) semantics where
  parents _ := {.reward}
  payoff _ configuration :=
    if configuration ⟨.reward, by simp⟩ then 1 else 0
  utility_eq _ _ := rfl

def decisionSite : DecisionSite model () := ⟨.decision, rfl⟩

/-- The added direct edge leaves an active route
`signal → reward → utility` after conditioning on the decision. -/
theorem signal_requisite :
    utilityView.IsRequisiteObservation decisionSite .signal := by
  have decisionReward : utilityView.DirectedEdge
      (.base .decision) (.base .reward) := by
    simp [UtilityView.DirectedEdge, UtilityView.graphParents,
      effectiveParents, parents]
  have signalReward : utilityView.DirectedEdge
      (.base .signal) (.base .reward) := by
    simp [UtilityView.DirectedEdge, UtilityView.graphParents,
      effectiveParents, parents]
  have rewardUtility : utilityView.DirectedEdge
      (.base .reward) (.utility ()) := by
    simp [UtilityView.DirectedEdge, UtilityView.graphParents,
      utilityView, model]
  have decisionUtility : utilityView.AncestorOrSelf
      (.base .decision) (.utility ()) :=
    Relation.ReflTransGen.head decisionReward
      (Relation.ReflTransGen.single rewardUtility)
  have signalUtility : utilityView.AncestorOrSelf
      (.base .signal) (.utility ()) :=
    Relation.ReflTransGen.head signalReward
      (Relation.ReflTransGen.single rewardUtility)
  have sourceClosure : utilityView.InAncestralClosure
      (.base .signal) (.utility ())
      (UtilityView.observationConditioning decisionSite .signal)
      (.base .signal) :=
    ⟨.base .signal, by simp, Relation.ReflTransGen.refl⟩
  have rewardClosure : utilityView.InAncestralClosure
      (.base .signal) (.utility ())
      (UtilityView.observationConditioning decisionSite .signal)
      (.base .reward) :=
    ⟨.utility (), by simp,
      Relation.ReflTransGen.single rewardUtility⟩
  have utilityClosure : utilityView.InAncestralClosure
      (.base .signal) (.utility ())
      (UtilityView.observationConditioning decisionSite .signal)
      (.utility ()) :=
    ⟨.utility (), by simp, Relation.ReflTransGen.refl⟩
  have signalRewardMoral : utilityView.MoralAdjacent
      (.base .signal) (.utility ())
      (UtilityView.observationConditioning decisionSite .signal)
      (.base .signal) (.base .reward) := by
    exact ⟨by decide,
      by simp [UtilityView.observationConditioning,
        UtilityView.observationConditioningSet, decisionSite],
      by simp [UtilityView.observationConditioning,
        UtilityView.observationConditioningSet, decisionSite],
      sourceClosure, rewardClosure, Or.inl signalReward⟩
  have rewardUtilityMoral : utilityView.MoralAdjacent
      (.base .signal) (.utility ())
      (UtilityView.observationConditioning decisionSite .signal)
      (.base .reward) (.utility ()) := by
    exact ⟨by decide,
      by simp [UtilityView.observationConditioning,
        UtilityView.observationConditioningSet, decisionSite],
      by simp [UtilityView.observationConditioning,
        UtilityView.observationConditioningSet, decisionSite],
      rewardClosure, utilityClosure, Or.inl rewardUtility⟩
  refine ⟨by simp [model, decisionSite], decisionUtility, ?_⟩
  refine ⟨by simp [UtilityView.observationConditioning,
      UtilityView.observationConditioningSet, decisionSite],
    by simp [UtilityView.observationConditioning,
      UtilityView.observationConditioningSet, decisionSite], ?_⟩
  exact Relation.ReflTransGen.head signalRewardMoral
    (Relation.ReflTransGen.single rewardUtilityMoral)

end Requisite

end GameTheory.Experimental.PostArchitecture.MAIDRequisiteObservation
