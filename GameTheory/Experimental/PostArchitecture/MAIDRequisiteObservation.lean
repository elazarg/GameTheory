/-
# Experimental graphical requisite-observation criterion for MAIDs

This experiment leaves the canonical MAID syntax and evaluator unchanged.  A
`UtilityView` enumerates distinct, owner-indexed utility terms and proves that
their additive sum is the owner's canonical utility.
The probabilistic graph uses causal parents at chance nodes and observed
parents at decision nodes: an unobserved ordering predecessor is not thereby a
probabilistic input to a decision rule.

`DConnected` uses the standard ancestral-moral characterization of
d-connection.  Its conditioning argument remains a set throughout.  The
singleton observation criterion says that the observation is *requisite*, in
other words not graphically ignorable, when it remains connected to some
owner-relevant utility term after conditioning on the decision and every
other observation.

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

/-- One leaf utility term over a named set of assignment coordinates. -/
structure UtilityTerm (diagram : Structure Player Node) where
  parents : Finset Node
  payoff : Config diagram parents → ℝ

namespace UtilityTerm

/-- Evaluate one utility term on a complete assignment. -/
def value (term : UtilityTerm diagram) (assignment : Assignment diagram) : ℝ :=
  term.payoff (Assignment.restrict diagram assignment term.parents)

end UtilityTerm

/-- An exact finite additive decomposition of each owner's canonical utility.
The lists provide the finite utility-node enumeration; the stable MAID syntax
stores no additional finiteness or utility graph. -/
structure UtilityView (semantics : Semantics diagram) where
  terms : Player → List (UtilityTerm diagram)
  utility_eq_sum : ∀ (owner : Player) (assignment : Assignment diagram),
    semantics.utility owner assignment =
      ∑ term : Fin (terms owner).length,
        (terms owner)[term].value assignment

namespace UtilityView

variable {semantics : Semantics diagram}

/-- One owner's finite utility-site carrier. -/
abbrev UtilitySite (view : UtilityView semantics) (owner : Player) :=
  Fin (view.terms owner).length

/-- Recover the term named by one owner's utility site. -/
def term (view : UtilityView semantics) {owner : Player}
    (site : view.UtilitySite owner) : UtilityTerm diagram :=
  (view.terms owner)[site]

/-- Base variables together with the queried owner's distinct utility leaves.
Other owners' utility nodes are omitted: as leaves, they cannot enter this
owner's ancestral query graph. -/
inductive GraphNode (view : UtilityView semantics) (owner : Player)
  | base (node : Node)
  | utility (term : view.UtilitySite owner)

/-- Equality of an owner's graph nodes needs equality only on base nodes.  The
owner is an index, not graph data. -/
instance [DecidableEq Node] (view : UtilityView semantics) (owner : Player) :
    DecidableEq (GraphNode view owner)
  | .base first, .base second =>
      if h : first = second then
        isTrue (by cases h; rfl)
      else
        isFalse (fun equality => h (GraphNode.base.inj equality))
  | .utility first, .utility second =>
      if h : first = second then
        isTrue (by cases h; rfl)
      else
        isFalse (fun equality => h (GraphNode.utility.inj equality))
  | .base _, .utility _ => isFalse (by intro equality; cases equality)
  | .utility _, .base _ => isFalse (by intro equality; cases equality)

/-- Parent sets in the graph augmented by the proved utility sinks. -/
def graphParents (view : UtilityView semantics)
    [DecidableEq Node] {owner : Player} :
    GraphNode view owner → Finset (GraphNode view owner)
  | .base node =>
      (effectiveParents diagram node).image GraphNode.base
  | .utility term =>
      (view.term term).parents.image GraphNode.base

/-- A directed edge of the graph augmented by utility sinks. -/
def DirectedEdge (view : UtilityView semantics)
    [DecidableEq Node] {owner : Player}
    (parent child : GraphNode view owner) : Prop :=
  parent ∈ view.graphParents child

/-- Directed ancestry, allowing the node itself. -/
def AncestorOrSelf (view : UtilityView semantics)
    [DecidableEq Node] {owner : Player}
    (ancestor descendant : GraphNode view owner) : Prop :=
  Relation.ReflTransGen view.DirectedEdge ancestor descendant

/-- A utility term is relevant to a decision exactly when its distinct leaf is
a strict directed descendant of that decision. -/
def IsRelevantUtilityTerm (view : UtilityView semantics)
    [DecidableEq Node] {owner : Player}
    (site : DecisionSite diagram owner) (term : view.UtilitySite owner) : Prop :=
  Relation.TransGen view.DirectedEdge (.base site.1) (.utility term)

/-- Membership in the ancestral closure of two query endpoints and the whole
conditioning set. -/
def InAncestralClosure (view : UtilityView semantics)
    [DecidableEq Node] {owner : Player}
    (source target : GraphNode view owner)
    (conditioned : Finset (GraphNode view owner))
    (node : GraphNode view owner) : Prop :=
  ∃ root ∈ insert source (insert target conditioned),
    view.AncestorOrSelf node root

/-- Adjacency in the ancestral moral graph after deleting every conditioned
node.  Besides underlying directed edges, two parents of the same ancestral
child are adjacent. -/
def MoralAdjacent (view : UtilityView semantics)
    [DecidableEq Node] {owner : Player}
    (source target : GraphNode view owner)
    (conditioned : Finset (GraphNode view owner))
    (first second : GraphNode view owner) : Prop :=
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
    [DecidableEq Node] {owner : Player}
    (source target : GraphNode view owner)
    (conditioned : Finset (GraphNode view owner)) : Prop :=
  source ∉ conditioned ∧
    target ∉ conditioned ∧
    Relation.ReflTransGen
      (view.MoralAdjacent source target conditioned) source target

/-- Condition on the decision and on every observation outside the entire set
being tested.  Keeping `removed` set-valued is load-bearing: the exact
criterion removes all of `X` from the conditioning set at once. -/
def observationConditioningSet [DecidableEq Node]
    (view : UtilityView semantics)
    {owner : Player} (site : DecisionSite diagram owner)
    (removed : Finset Node) : Finset (GraphNode view owner) :=
  insert (.base site.1)
    ((diagram.observedParents site.1 \ removed).image
      GraphNode.base)

/-- Singleton specialization of `observationConditioningSet`. -/
def observationConditioning [DecidableEq Node]
    (view : UtilityView semantics)
    {owner : Player} (site : DecisionSite diagram owner)
    (observation : Node) : Finset (GraphNode view owner) :=
  view.observationConditioningSet site {observation}

@[simp]
theorem observationConditioning_eq [DecidableEq Node]
    (view : UtilityView semantics)
    {owner : Player} (site : DecisionSite diagram owner)
    (observation : Node) :
    view.observationConditioning site observation =
      insert (.base site.1)
        ((diagram.observedParents site.1).erase observation |>.image
          GraphNode.base) := by
  simp [observationConditioning, observationConditioningSet,
    Finset.sdiff_singleton_eq_erase]

/-- A set of observations is graphically ignorable when it is observed at the
decision and every removed observation is d-separated from every relevant
owned utility term after removing the whole set from the conditioning
context.  This remains a graph predicate only. -/
def AreGraphicallyIgnorable (view : UtilityView semantics)
    [DecidableEq Node]
    {owner : Player} (site : DecisionSite diagram owner)
    (removed : Finset Node) : Prop :=
  removed ⊆ diagram.observedParents site.1 ∧
    ∀ term : view.UtilitySite owner,
      view.IsRelevantUtilityTerm site term →
        ∀ observation ∈ removed,
          ¬ view.DConnected (.base observation) (.utility term)
            (view.observationConditioningSet site removed)

/-- A singleton observation is requisite (the complement of graphically
ignorable) when it is observed at the decision and d-connected to that
owner's proved relevant utility term conditional on the decision and all
other observations. -/
def IsRequisiteObservation (view : UtilityView semantics)
    [DecidableEq Node]
    {owner : Player} (site : DecisionSite diagram owner)
    (observation : Node) : Prop :=
  observation ∈ diagram.observedParents site.1 ∧
    ∃ term : view.UtilitySite owner,
      view.IsRelevantUtilityTerm site term ∧
        view.DConnected (.base observation) (.utility term)
          (view.observationConditioning site observation)

/-- On a declared observation, the public singleton terminology is literally
the complement of the set-valued graphical ignorability test. -/
theorem isRequisiteObservation_iff_not_areGraphicallyIgnorable
    (view : UtilityView semantics)
    [DecidableEq Node]
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

def rewardTerm : UtilityTerm model where
  parents := {.reward}
  payoff configuration :=
    if configuration ⟨.reward, by simp⟩ then 1 else 0

def utilityView : UtilityView (diagram := model) semantics where
  terms _ := [rewardTerm]
  utility_eq_sum _ _ := by
    simp [rewardTerm, UtilityTerm.value, Assignment.restrict]

def rewardSite : utilityView.UtilitySite () :=
  ⟨0, by simp [utilityView]⟩

def decisionSite : DecisionSite model () := ⟨.decision, rfl⟩

/-- In the chain `signal → decision → reward → utility`, conditioning on the
decision blocks the only path from the observation to utility. -/
theorem signal_not_requisite :
    ¬ utilityView.IsRequisiteObservation decisionSite .signal := by
  rintro ⟨_, term, _, _, _, connection⟩
  fin_cases term
  have isolated : ∀ next,
      ¬ utilityView.MoralAdjacent
        (.base .signal) (.utility rewardSite)
        (utilityView.observationConditioning decisionSite .signal)
        (.base .signal) next := by
    intro next hadjacent
    rcases hadjacent with
      ⟨hne, _, hnextOpen, _, _, hforward | hbackward | hcoparents⟩
    · cases next with
      | base node =>
          cases node with
          | signal => exact hne rfl
          | decision =>
              exact hnextOpen (Finset.mem_insert_self _ _)
          | reward =>
              simp [UtilityView.DirectedEdge, UtilityView.graphParents,
                effectiveParents, parents] at hforward
      | utility owner =>
          have hforward' : (.base .signal) ∈
              (utilityView.term owner).parents.image
                UtilityView.GraphNode.base := hforward
          obtain ⟨node, hnode, equality⟩ := Finset.mem_image.mp hforward'
          fin_cases owner
          have hreward : node = ExampleNode.reward := by
            simpa [UtilityView.term, utilityView, rewardTerm] using hnode
          subst node
          have hnode : ExampleNode.reward = .signal :=
            UtilityView.GraphNode.base.inj equality
          cases hnode
    · cases next with
      | base node =>
          cases node <;>
            simp [UtilityView.DirectedEdge, UtilityView.graphParents,
              effectiveParents, parents] at hbackward
      | utility owner =>
          fin_cases owner
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
                    fin_cases owner
                    simp [UtilityView.DirectedEdge,
                      UtilityView.graphParents, effectiveParents,
                      exampleObservedParents] at hnextParent
              exact hne hnext.symm
          | reward =>
              simp [UtilityView.DirectedEdge, UtilityView.graphParents,
                effectiveParents, parents] at hsignalParent
      | utility owner =>
          have hsignalParent' : (.base .signal) ∈
              (utilityView.term owner).parents.image
                UtilityView.GraphNode.base := hsignalParent
          obtain ⟨node, hnode, equality⟩ :=
            Finset.mem_image.mp hsignalParent'
          fin_cases owner
          have hreward : node = ExampleNode.reward := by
            simpa [UtilityView.term, utilityView, rewardTerm] using hnode
          subst node
          have hnode : ExampleNode.reward = .signal :=
            UtilityView.GraphNode.base.inj equality
          cases hnode
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

def rewardTerm : UtilityTerm model where
  parents := {.reward}
  payoff configuration :=
    if configuration ⟨.reward, by simp⟩ then 1 else 0

def utilityView : UtilityView (diagram := model) semantics where
  terms _ := [rewardTerm]
  utility_eq_sum _ _ := by
    simp [rewardTerm, UtilityTerm.value, Assignment.restrict]

def rewardSite : utilityView.UtilitySite () :=
  ⟨0, by simp [utilityView]⟩

def decisionSite : DecisionSite model () := ⟨.decision, rfl⟩

/-- The added direct edge leaves an active route
`signal → reward → utility` after conditioning on the decision. -/
theorem signal_requisite :
    utilityView.IsRequisiteObservation decisionSite .signal := by
  have decisionReward : utilityView.DirectedEdge
      (owner := ()) (.base .decision) (.base .reward) := by
    simp [UtilityView.DirectedEdge, UtilityView.graphParents,
      effectiveParents, parents]
  have signalReward : utilityView.DirectedEdge
      (owner := ()) (.base .signal) (.base .reward) := by
    simp [UtilityView.DirectedEdge, UtilityView.graphParents,
      effectiveParents, parents]
  have rewardUtility : utilityView.DirectedEdge
      (.base .reward) (.utility rewardSite) := by
    show (.base .reward : UtilityView.GraphNode utilityView ()) ∈
      (utilityView.term rewardSite).parents.image UtilityView.GraphNode.base
    have hterm : utilityView.term rewardSite = rewardTerm := by
      rfl
    rw [hterm]
    simp [rewardTerm]
  have decisionUtility : utilityView.IsRelevantUtilityTerm
      decisionSite rewardSite :=
    Relation.TransGen.head decisionReward
      (Relation.TransGen.single rewardUtility)
  have sourceClosure : utilityView.InAncestralClosure
      (.base .signal) (.utility rewardSite)
      (utilityView.observationConditioning decisionSite .signal)
      (.base .signal) :=
    ⟨.base .signal, by simp, Relation.ReflTransGen.refl⟩
  have rewardClosure : utilityView.InAncestralClosure
      (.base .signal) (.utility rewardSite)
      (utilityView.observationConditioning decisionSite .signal)
      (.base .reward) :=
    ⟨.utility rewardSite, by simp,
      Relation.ReflTransGen.single rewardUtility⟩
  have utilityClosure : utilityView.InAncestralClosure
      (.base .signal) (.utility rewardSite)
      (utilityView.observationConditioning decisionSite .signal)
      (.utility rewardSite) :=
    ⟨.utility rewardSite, by simp, Relation.ReflTransGen.refl⟩
  have signalRewardMoral : utilityView.MoralAdjacent
      (.base .signal) (.utility rewardSite)
      (utilityView.observationConditioning decisionSite .signal)
      (.base .signal) (.base .reward) := by
    exact ⟨by decide,
      by simp [UtilityView.observationConditioning,
        UtilityView.observationConditioningSet, decisionSite],
      by simp [UtilityView.observationConditioning,
        UtilityView.observationConditioningSet, decisionSite],
      sourceClosure, rewardClosure, Or.inl signalReward⟩
  have rewardUtilityMoral : utilityView.MoralAdjacent
      (.base .signal) (.utility rewardSite)
      (utilityView.observationConditioning decisionSite .signal)
      (.base .reward) (.utility rewardSite) := by
    exact ⟨by decide,
      by simp [UtilityView.observationConditioning,
        UtilityView.observationConditioningSet, decisionSite],
      by simp [UtilityView.observationConditioning,
        UtilityView.observationConditioningSet, decisionSite],
      rewardClosure, utilityClosure, Or.inl rewardUtility⟩
  refine ⟨by simp [model, decisionSite], rewardSite, decisionUtility, ?_⟩
  refine ⟨by simp [UtilityView.observationConditioning,
      UtilityView.observationConditioningSet, decisionSite],
    by simp [UtilityView.observationConditioning,
      UtilityView.observationConditioningSet, decisionSite], ?_⟩
  exact Relation.ReflTransGen.head signalRewardMoral
    (Relation.ReflTransGen.single rewardUtilityMoral)

end Requisite

/-! ## Same utility, split leaves versus one merged leaf

The next control is the reason utility terms must remain distinct.  Both views
prove exactly the same canonical utility.  In the split view, the signal-only
term is not a descendant of the decision and the reward-only term is separated
from the signal by the conditioned decision.  Merging the two summands into one
leaf instead makes the signal a parent of a decision-relevant utility leaf.
That merged graph therefore classifies the signal as requisite.
-/

namespace SplitMerged

def score (value : Bool) : ℝ := if value then 1 else 0

@[reducible]
def semantics : Semantics Nonrequisite.model where
  defaultValue _ := false
  chanceLaw node hchance _ := by
    cases node with
    | signal => exact GameTheory.Math.Probability.FinDist.pure false
    | decision => simp at hchance
    | reward => exact GameTheory.Math.Probability.FinDist.pure false
  utility _ assignment := score (assignment .reward) + score (assignment .signal)

def rewardTerm : UtilityTerm Nonrequisite.model where
  parents := {.reward}
  payoff configuration := score (configuration ⟨.reward, by simp⟩)

def signalTerm : UtilityTerm Nonrequisite.model where
  parents := {.signal}
  payoff configuration := score (configuration ⟨.signal, by simp⟩)

def mergedTerm : UtilityTerm Nonrequisite.model where
  parents := {.reward, .signal}
  payoff configuration :=
    score (configuration ⟨.reward, by simp⟩) +
      score (configuration ⟨.signal, by simp⟩)

def splitView : UtilityView (diagram := Nonrequisite.model) semantics where
  terms _ := [rewardTerm, signalTerm]
  utility_eq_sum _ _ := by
    simp [score, rewardTerm, signalTerm, UtilityTerm.value,
      Assignment.restrict]
    rfl

def mergedView : UtilityView (diagram := Nonrequisite.model) semantics where
  terms _ := [mergedTerm]
  utility_eq_sum _ _ := by
    simp [score, mergedTerm, UtilityTerm.value, Assignment.restrict]
    rfl

def splitRewardSite : splitView.UtilitySite () :=
  ⟨0, by simp [splitView]⟩

def splitSignalSite : splitView.UtilitySite () :=
  ⟨1, by simp [splitView]⟩

def mergedSite : mergedView.UtilitySite () :=
  ⟨0, by simp [mergedView]⟩

def decisionSite : DecisionSite Nonrequisite.model () := ⟨.decision, rfl⟩

/-- The signal-only summand is not owner-relevant to this decision: utility
leaves are sinks and there is no directed path from the decision back to the
signal. -/
theorem split_signal_term_not_relevant :
    ¬ splitView.IsRelevantUtilityTerm decisionSite splitSignalSite := by
  intro relevant
  have relevant' : Relation.TransGen splitView.DirectedEdge
      (.base decisionSite.1) (.utility splitSignalSite) := relevant
  rw [Relation.TransGen.tail'_iff] at relevant'
  obtain ⟨before, path, lastEdge⟩ := relevant'
  have lastEdge' : before ∈
      (splitView.term splitSignalSite).parents.image
        UtilityView.GraphNode.base := lastEdge
  have hterm : splitView.term splitSignalSite = signalTerm := by rfl
  rw [hterm] at lastEdge'
  obtain ⟨node, hnode, equality⟩ := Finset.mem_image.mp lastEdge'
  have hsignal : node = ExampleNode.signal := by
    simpa [signalTerm] using hnode
  subst node
  subst before
  rcases Relation.ReflTransGen.cases_tail path with equality | ⟨_, _, lastEdge⟩
  · have hnode : ExampleNode.signal = .decision :=
      UtilityView.GraphNode.base.inj equality
    cases hnode
  · simp [UtilityView.DirectedEdge, UtilityView.graphParents,
      effectiveParents, Nonrequisite.parents] at lastEdge

private theorem split_signal_utility_not_in_reward_closure :
    ¬ splitView.InAncestralClosure
      (.base .signal) (.utility splitRewardSite)
      (splitView.observationConditioning decisionSite .signal)
      (.utility splitSignalSite) := by
  have noOutgoing : ∀ next,
      ¬ splitView.DirectedEdge (.utility splitSignalSite) next := by
    intro next edge
    cases next with
    | base node =>
        have edge' : (.utility splitSignalSite) ∈
            (effectiveParents Nonrequisite.model node).image
              UtilityView.GraphNode.base := edge
        obtain ⟨_, _, equality⟩ := Finset.mem_image.mp edge'
        cases equality
    | utility term =>
        have edge' : (.utility splitSignalSite) ∈
            (splitView.term term).parents.image
              UtilityView.GraphNode.base := edge
        obtain ⟨_, _, equality⟩ := Finset.mem_image.mp edge'
        cases equality
  rintro ⟨root, hroot, path⟩
  rcases Relation.ReflTransGen.cases_head path with equality | ⟨next, edge, _⟩
  · subst root
    simp [UtilityView.observationConditioning,
      UtilityView.observationConditioningSet, decisionSite,
      splitRewardSite, splitSignalSite] at hroot
  · exact noOutgoing next edge

/-- With the utility summands represented by distinct leaves, the observed
signal is nonrequisite for the decision. -/
theorem split_signal_not_requisite :
    ¬ splitView.IsRequisiteObservation decisionSite .signal := by
  rintro ⟨_, term, relevant, _, _, connection⟩
  fin_cases term
  · have isolated : ∀ next,
        ¬ splitView.MoralAdjacent
          (.base .signal) (.utility splitRewardSite)
          (splitView.observationConditioning decisionSite .signal)
          (.base .signal) next := by
      intro next adjacent
      rcases adjacent with
        ⟨hne, _, hnextOpen, _, hnextClosure,
          hforward | hbackward | hcoparents⟩
      · cases next with
        | base node =>
            cases node with
            | signal => exact hne rfl
            | decision => exact hnextOpen (Finset.mem_insert_self _ _)
            | reward =>
                simp [UtilityView.DirectedEdge, UtilityView.graphParents,
                  effectiveParents, Nonrequisite.parents] at hforward
        | utility utilitySite =>
            have hforward' : (.base .signal) ∈
                (splitView.term utilitySite).parents.image
                  UtilityView.GraphNode.base := hforward
            fin_cases utilitySite
            · obtain ⟨node, hnode, equality⟩ :=
                Finset.mem_image.mp hforward'
              have hreward : node = ExampleNode.reward := by
                simpa [UtilityView.term, splitView, rewardTerm] using hnode
              subst node
              have hnode : ExampleNode.reward = .signal :=
                UtilityView.GraphNode.base.inj equality
              cases hnode
            · exact split_signal_utility_not_in_reward_closure hnextClosure
      · cases next with
        | base node =>
            cases node <;>
              simp [UtilityView.DirectedEdge, UtilityView.graphParents,
                effectiveParents, Nonrequisite.parents] at hbackward
        | utility utilitySite =>
            fin_cases utilitySite <;>
              simp [UtilityView.DirectedEdge, UtilityView.graphParents,
                effectiveParents, Nonrequisite.parents] at hbackward
      · obtain ⟨child, _, hsignalParent, hnextParent⟩ := hcoparents
        cases child with
        | base node =>
            cases node with
            | signal =>
                simp [UtilityView.DirectedEdge, UtilityView.graphParents,
                  effectiveParents, Nonrequisite.parents] at hsignalParent
            | decision =>
                have hnext : next = .base .signal := by
                  cases next with
                  | base nextNode =>
                      cases nextNode <;>
                        simp [UtilityView.DirectedEdge,
                          UtilityView.graphParents, effectiveParents,
                          exampleObservedParents] at hnextParent ⊢
                  | utility utilitySite =>
                      fin_cases utilitySite <;>
                        simp [UtilityView.DirectedEdge,
                          UtilityView.graphParents, effectiveParents,
                          exampleObservedParents] at hnextParent
                exact hne hnext.symm
            | reward =>
                simp [UtilityView.DirectedEdge, UtilityView.graphParents,
                  effectiveParents, Nonrequisite.parents] at hsignalParent
        | utility utilitySite =>
            have hsignalParent' : (.base .signal) ∈
                (splitView.term utilitySite).parents.image
                  UtilityView.GraphNode.base := hsignalParent
            have hnextParent' : next ∈
                (splitView.term utilitySite).parents.image
                  UtilityView.GraphNode.base := hnextParent
            fin_cases utilitySite
            · obtain ⟨node, hnode, equality⟩ :=
                Finset.mem_image.mp hsignalParent'
              have hreward : node = ExampleNode.reward := by
                simpa [UtilityView.term, splitView, rewardTerm] using hnode
              subst node
              have hnode : ExampleNode.reward = .signal :=
                UtilityView.GraphNode.base.inj equality
              cases hnode
            · obtain ⟨node, hnode, equality⟩ :=
                Finset.mem_image.mp hnextParent'
              have hsignal : node = ExampleNode.signal := by
                simpa [UtilityView.term, splitView, signalTerm] using hnode
              subst node
              exact hne equality
    rcases Relation.ReflTransGen.cases_head connection with
      equality | ⟨next, firstStep, _⟩
    · cases equality
    · exact isolated next firstStep
  · exact split_signal_term_not_relevant relevant

/-- The merged representation creates a signal-to-relevant-utility route even
though its additive value is definitionally the same as the split view's. -/
theorem merged_signal_requisite :
    mergedView.IsRequisiteObservation decisionSite .signal := by
  have decisionReward : mergedView.DirectedEdge
      (owner := ()) (.base .decision) (.base .reward) := by
    simp [UtilityView.DirectedEdge, UtilityView.graphParents,
      effectiveParents, Nonrequisite.parents]
  have rewardUtility : mergedView.DirectedEdge
      (.base .reward) (.utility mergedSite) := by
    show (.base .reward) ∈
      (mergedView.term mergedSite).parents.image UtilityView.GraphNode.base
    have hterm : mergedView.term mergedSite = mergedTerm := by rfl
    rw [hterm]
    apply Finset.mem_image.mpr
    exact ⟨.reward, by simp [mergedTerm], rfl⟩
  have signalUtility : mergedView.DirectedEdge
      (.base .signal) (.utility mergedSite) := by
    show (.base .signal) ∈
      (mergedView.term mergedSite).parents.image UtilityView.GraphNode.base
    have hterm : mergedView.term mergedSite = mergedTerm := by rfl
    rw [hterm]
    apply Finset.mem_image.mpr
    exact ⟨.signal, by simp [mergedTerm], rfl⟩
  have relevant : mergedView.IsRelevantUtilityTerm decisionSite mergedSite :=
    Relation.TransGen.head decisionReward
      (Relation.TransGen.single rewardUtility)
  have sourceClosure : mergedView.InAncestralClosure
      (.base .signal) (.utility mergedSite)
      (mergedView.observationConditioning decisionSite .signal)
      (.base .signal) :=
    ⟨.base .signal, by simp, Relation.ReflTransGen.refl⟩
  have targetClosure : mergedView.InAncestralClosure
      (.base .signal) (.utility mergedSite)
      (mergedView.observationConditioning decisionSite .signal)
      (.utility mergedSite) :=
    ⟨.utility mergedSite, by simp, Relation.ReflTransGen.refl⟩
  have activeEdge : mergedView.MoralAdjacent
      (.base .signal) (.utility mergedSite)
      (mergedView.observationConditioning decisionSite .signal)
      (.base .signal) (.utility mergedSite) := by
    exact ⟨by decide,
      by simp [UtilityView.observationConditioning,
        UtilityView.observationConditioningSet, decisionSite],
      by simp [UtilityView.observationConditioning,
        UtilityView.observationConditioningSet, decisionSite],
      sourceClosure, targetClosure, Or.inl signalUtility⟩
  refine ⟨by simp [Nonrequisite.model, exampleObservedParents, decisionSite],
    mergedSite, relevant, ?_⟩
  refine ⟨by simp [UtilityView.observationConditioning,
      UtilityView.observationConditioningSet, decisionSite],
    by simp [UtilityView.observationConditioning,
      UtilityView.observationConditioningSet, decisionSite], ?_⟩
  exact Relation.ReflTransGen.single activeEdge

end SplitMerged

end GameTheory.Experimental.PostArchitecture.MAIDRequisiteObservation
