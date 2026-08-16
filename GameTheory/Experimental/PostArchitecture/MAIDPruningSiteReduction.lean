/-
# EXP-107: graphical target-site observation reduction

Relevant hybrid utility terms factor through the retained target context and
action.  Nonrelevant terms have a target-rule-invariant marginal.  Summing
those two exact lanes constructs the graph-free site-local utility certificate
and therefore an optimal rule that ignores the pruned target observations.

The result fixes every other site of a possibly multi-site owner.  It makes no
coverage, equilibrium, recall, or global pruning claim.
-/

import GameTheory.Experimental.PostArchitecture.MAIDPruningNonrelevantInvariance
import GameTheory.Experimental.PostArchitecture.MAIDPruningRelevantContinuation
import GameTheory.Experimental.PostArchitecture.MAIDPruningFixpointGraph
import GameTheory.Experimental.PostArchitecture.MAIDReplacementInvariantUtility
import GameTheory.Experimental.PostArchitecture.MAIDSiteLocalReduction

noncomputable section

open scoped BigOperators

namespace GameTheory.Experimental.PostArchitecture.MAIDPruningSiteReduction

open GameTheory
open GameTheory.Math.Probability
open GameTheory.Languages.MAID
open GameTheory.Languages.MAID.ObservationPruning
open GameTheory.Experimental.PostArchitecture.MAIDKernelMarginalization
open GameTheory.Experimental.PostArchitecture.MAIDPruningFixpointGraph
open GameTheory.Experimental.PostArchitecture.MAIDPruningNonrelevantInvariance
open GameTheory.Experimental.PostArchitecture.MAIDPruningRelevantContinuation
open GameTheory.Experimental.PostArchitecture.MAIDReplacementInvariantUtility
open GameTheory.Experimental.PostArchitecture.MAIDRequisiteObservation
open GameTheory.Experimental.PostArchitecture.MAIDSiteLocalReduction
open GameTheory.Experimental.PostArchitecture.MAIDSiteOptimality
open GameTheory.Experimental.PostArchitecture.MAIDSiteReplacementContext

universe uPlayer uNode uValue

variable {Player : Type uPlayer} {Node : Type uNode}
variable
  {diagram : Structure.{uPlayer, uNode, max uNode uValue} Player Node}
  {semantics : Semantics diagram}

private noncomputable def siteTermContinuationValue
    (pruning : Pruning diagram)
    [Fintype Node] [DecidableEq Player] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    [∀ node, DecidableEq (diagram.Value node)]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (semantics : Semantics diagram) (policy : pruning.ReducedPolicy)
    (owner : Player) (fixedOwner : pruning.ReducedOwnerPolicy owner)
    (target : DecisionSite diagram owner) (view : UtilityView semantics)
    (hstable :
      MAIDPruningFixpointGraph.UtilityView.IsEdgeAdditionStableAt view pruning
        target)
    (term : view.UtilitySite owner) (kept : KeptContext pruning target)
    (action : diagram.Value target.1) : ℝ := by
  classical
  by_cases hrelevant :
      MAIDPruningFixpointGraph.UtilityView.IsRelevantUtilityTermUnder view
        (Pruning.restoreAllAt pruning target) target term
  · exact
      ((relevantTermContinuationLawAt_of_edgeAdditionStableAt pruning
        topological semantics policy owner fixedOwner target view hstable term
        hrelevant).continuationLaw kept action).expect (view.term term).payoff
  · exact
      (nonrelevantTermMarginalCertificate pruning topological semantics policy
        owner fixedOwner target view term hrelevant).marginalLaw.expect
        (view.term term).payoff

/-- Edge-addition stability constructs the exact graph-free site-local utility
factorization while every other owner site remains fixed. -/
def siteLocalUtilityFactorsAt_of_edgeAdditionStableAt
    (pruning : Pruning diagram)
    [Fintype Node] [DecidableEq Player] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    [∀ node, DecidableEq (diagram.Value node)]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (semantics : Semantics diagram) (policy : pruning.ReducedPolicy)
    (owner : Player) (fixedOwner : pruning.ReducedOwnerPolicy owner)
    (target : DecisionSite diagram owner) (view : UtilityView semantics)
    (hstable :
      MAIDPruningFixpointGraph.UtilityView.IsEdgeAdditionStableAt view pruning
        target) :
    SiteLocalUtilityFactorsAt pruning semantics (pruning.expandPolicy policy)
      owner (pruning.expandOwnerPolicy owner fixedOwner) target := by
  classical
  let context := siteReplacementContextLawAt topological semantics
    (pruning.expandPolicy policy) owner
    (pruning.expandOwnerPolicy owner fixedOwner) target
  refine {
    context := context
    continuationValue := fun kept action => ∑ term : view.UtilitySite owner,
      siteTermContinuationValue pruning topological semantics policy owner
        fixedOwner target view hstable term kept action
    utility_eq := ?_ }
  intro rule
  let law := siteReplacementLaw semantics (pruning.expandPolicy policy) owner
    (pruning.expandOwnerPolicy owner fixedOwner) target rule
  let keep : FullContext target → KeptContext pruning target :=
    Config.restrict (diagram := diagram)
      (pruning.kept_sub_observed target.1)
  let joint := fullJoint context.contextLaw keep rule
  have hterm : ∀ term : view.UtilitySite owner,
      law.expect (view.term term).value =
        joint.expect (fun result =>
          siteTermContinuationValue pruning topological semantics policy owner
            fixedOwner target view hstable term result.1 result.2) := by
    intro term
    by_cases hrelevant :
        MAIDPruningFixpointGraph.UtilityView.IsRelevantUtilityTermUnder view
          (Pruning.restoreAllAt pruning target) target term
    · let termLaw :=
        relevantTermContinuationLawAt_of_edgeAdditionStableAt pruning
          topological semantics policy owner fixedOwner target view hstable
          term hrelevant
      calc
        law.expect (view.term term).value =
            (law.map (siteFullActionTermProjection view target term)).expect
              (fun result => (view.term term).payoff result.2) := by
                rw [FinDist.expect_map]
                rfl
        _ = (context.contextLaw.bind fun full =>
              (rule full).bind fun action =>
                (termLaw.continuationLaw (keep full) action).map
                  fun termValue => ((full, action), termValue)).expect
              (fun result => (view.term term).payoff result.2) := by
                rw [termLaw.joint_eq rule]
        _ = joint.expect (fun result =>
              siteTermContinuationValue pruning topological semantics policy
                owner fixedOwner target view hstable term result.1
                result.2) := by
                simp [joint, fullJoint, keep, FinDist.expect_bind,
                  FinDist.expect_map, siteTermContinuationValue, hrelevant,
                  termLaw]
    · let termLaw := nonrelevantTermMarginalCertificate pruning topological
        semantics policy owner fixedOwner target view term hrelevant
      calc
        law.expect (view.term term).value =
            (law.map fun assignment =>
              Assignment.restrict diagram assignment
                (view.term term).parents).expect
              (view.term term).payoff := by
                rw [FinDist.expect_map]
                rfl
        _ = termLaw.marginalLaw.expect (view.term term).payoff := by
              rw [termLaw.marginal_eq rule]
        _ = joint.expect (fun result =>
              siteTermContinuationValue pruning topological semantics policy
                owner fixedOwner target view hstable term result.1
                result.2) := by
                simp [joint, fullJoint, siteTermContinuationValue, hrelevant,
                  termLaw, FinDist.expect_const]
  unfold siteRuleExpectedUtility GameTheory.expectedUtility
  show law.expect (fun assignment => semantics.utility owner assignment) = _
  calc
    law.expect (fun assignment => semantics.utility owner assignment) =
        law.expect (fun assignment => ∑ term : view.UtilitySite owner,
          (view.term term).value assignment) := by
            apply FinDist.expect_congr
            intro assignment _
            exact view.utility_eq_sum owner assignment
    _ = ∑ term : view.UtilitySite owner,
          law.expect (view.term term).value :=
      (FinDist.expect_sum_comm law fun term assignment =>
        (view.term term).value assignment).symm
    _ = ∑ term : view.UtilitySite owner,
          joint.expect (fun result =>
            siteTermContinuationValue pruning topological semantics policy
              owner fixedOwner target view hstable term result.1 result.2) := by
      apply Finset.sum_congr rfl
      intro term _
      exact hterm term
    _ = joint.expect (fun result => ∑ term : view.UtilitySite owner,
          siteTermContinuationValue pruning topological semantics policy owner
            fixedOwner target view hstable term result.1 result.2) :=
      FinDist.expect_sum_comm joint fun term result =>
        siteTermContinuationValue pruning topological semantics policy owner
          fixedOwner target view hstable term result.1 result.2
    _ = context.contextLaw.expect (fun full =>
          (rule full).expect fun action =>
            ∑ term : view.UtilitySite owner,
              siteTermContinuationValue pruning topological semantics policy
                owner fixedOwner target view hstable term (keep full)
                action) := by
      simp [joint, fullJoint, FinDist.expect_bind, FinDist.expect_map]

/-- At an edge-addition-stable target, some optimal target rule depends only
on the observations retained by the pruning.  Other sites of the owner remain
at the supplied arbitrary reduced owner policy. -/
theorem exists_reduced_isOptimalSiteRule_of_edgeAdditionStableAt
    (pruning : Pruning diagram)
    [Fintype Node] [DecidableEq Player] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    [∀ node, DecidableEq (diagram.Value node)]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (semantics : Semantics diagram) (policy : pruning.ReducedPolicy)
    (owner : Player) (fixedOwner : pruning.ReducedOwnerPolicy owner)
    (target : DecisionSite diagram owner) (view : UtilityView semantics)
    (hstable :
      MAIDPruningFixpointGraph.UtilityView.IsEdgeAdditionStableAt view pruning
        target) :
    ∃ reducedRule : KeptContext pruning target →
        FinDist (diagram.Value target.1),
      IsOptimalSiteRule semantics (pruning.expandPolicy policy) owner
        (pruning.expandOwnerPolicy owner fixedOwner) target
        (expandKeptSiteRule pruning target reducedRule) :=
  exists_reduced_isOptimalSiteRule pruning topological semantics policy owner
    fixedOwner target
      (siteLocalUtilityFactorsAt_of_edgeAdditionStableAt pruning topological
        semantics policy owner fixedOwner target view hstable)

end GameTheory.Experimental.PostArchitecture.MAIDPruningSiteReduction
