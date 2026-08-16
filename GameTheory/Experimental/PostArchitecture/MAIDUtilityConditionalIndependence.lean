/-
# EXP-105: fixed-policy utility conditional independence

This module composes the mapped utility-leaf factorization with finite global
Markov soundness.  Its conclusion concerns one fixed canonical policy law.  It
does not identify continuation laws across replacements or claim observation
reduction.
-/

import GameTheory.Experimental.PostArchitecture.FiniteBNGlobalMarkovSoundness
import GameTheory.Experimental.PostArchitecture.MAIDUtilityFactorization
import GameTheory.Experimental.PostArchitecture.MAIDUtilitySeparationBridge

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.MAIDUtilityConditionalIndependence

open GameTheory.Languages.MAID
open GameTheory.Experimental.PostArchitecture.FiniteBNCoordinateIndependence
open GameTheory.Experimental.PostArchitecture.FiniteBNGlobalMarkovSoundness
open GameTheory.Experimental.PostArchitecture.MAIDRequisiteObservation
open GameTheory.Experimental.PostArchitecture.MAIDUtilityAugmentation
open GameTheory.Experimental.PostArchitecture.MAIDUtilityFactorization
open GameTheory.Experimental.PostArchitecture.MAIDUtilityGraphFinite
open GameTheory.Experimental.PostArchitecture.MAIDUtilitySeparationBridge

universe uPlayer uNode uValue

variable {Player : Type uPlayer} {Node : Type uNode}
variable {diagram : Structure.{uPlayer, uNode, max uNode uValue} Player Node}
variable {semantics : Semantics diagram}

/-- A proof-only `Structure` presentation of the canonical augmented parent
graph.  Every node is marked as chance because only `parents`, `Value`, and
acyclicity are consumed by generic finite-BN soundness. -/
@[reducible]
def utilityGraphStructure [DecidableEq Node]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (view : UtilityView semantics) (owner : Player) :
    Structure.{0, uNode, max uNode uValue} Unit
      (@UtilityView.GraphNode.{uPlayer, uNode, max uNode uValue}
        Player Node diagram semantics view owner) where
  kind _ := .chance
  parents := UtilityView.graphParents (diagram := diagram) view
  observedParents := UtilityView.graphParents (diagram := diagram) view
  Value := @graphValue.{uPlayer, uNode, uValue}
    Player Node diagram semantics view owner
  observed_sub _ := Finset.Subset.rfl
  observed_eq_of_chance _ _ := rfl
  acyclic := GameTheory.Math.DAG.acyclic_of_topologicalOrder
    (augmentedTopologicalOrder view owner topological)

/-- For one fixed policy, graphical ignorability gives division-free
conditional independence between the entire removed base-coordinate set and a
relevant typed utility-configuration leaf, conditional on the decision and
every kept observation. -/
theorem removed_conditionallyIndependent_of_graphicallyIgnorable
    [Fintype Node] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    [∀ node, DecidableEq (diagram.Value node)]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (view : UtilityView semantics) (owner : Player) (policy : Policy diagram)
    (site : DecisionSite diagram owner) (removed : Finset Node)
    (hignore : view.AreGraphicallyIgnorable site removed)
    (term : view.UtilitySite owner)
    (hrelevant : view.IsRelevantUtilityTerm site term) :
    CoordinatesConditionallyIndependent
      (diagram := utilityGraphStructure topological view owner)
      (augmentedLaw view owner policy)
      (removedGraphNodes view owner removed) {.utility term}
      (view.observationConditioningSet site removed) := by
  obtain ⟨hfirstSecond, hfirstEvidence, hsecondEvidence⟩ :=
    removed_query_disjointness view site removed term hignore.1
  exact coordinatesConditionallyIndependent_of_factorizes_of_separates
    (diagram := utilityGraphStructure topological view owner)
    (augmentedLaw view owner policy) view.graphParents
    (augmentedTopologicalOrder view owner topological)
    (augmentedKernels view policy)
    (augmentedLaw_factorizes topological view owner policy)
    (removedGraphNodes view owner removed) {.utility term}
    (view.observationConditioningSet site removed)
    hfirstSecond hfirstEvidence hsecondEvidence
    (separates_removedGraphNodes_of_areGraphicallyIgnorable view site removed
      hignore term hrelevant)

end GameTheory.Experimental.PostArchitecture.MAIDUtilityConditionalIndependence
