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
  · letI : Fintype (TermConfig view term) := inferInstance
    let law :=
      (relevantTermContinuationLawAt_of_edgeAdditionStableAt pruning
        topological semantics policy owner fixedOwner target view hstable term
        hrelevant).continuationLaw kept action
    exact expect law (view.term term).payoff
      (payoffIntegrable_of_finite _ _)
  · letI : Fintype (TermConfig view term) := inferInstance
    let law :=
      (nonrelevantTermMarginalCertificate pruning topological semantics policy
        owner fixedOwner target view term hrelevant).marginalLaw
    exact expect law (view.term term).payoff
      (payoffIntegrable_of_finite _ _)

private theorem expect_taggedContinuation
    {Full Kept Action Term : Type*}
    [Fintype Full] [Fintype Kept] [Fintype Action] [Fintype Term]
    (outer : PMF Full) (keep : Full → Kept)
    (rule : Full → PMF Action) (kernel : Kept → Action → PMF Term)
    (payoff : Term → ℝ) :
    expect (outer.bind fun full =>
      (rule full).bind fun action =>
        (kernel (keep full) action).map fun term => ((full, action), term))
      (fun tagged => payoff tagged.2) (payoffIntegrable_of_finite _ _) =
    expect (fullJoint outer keep rule)
      (fun pair => expect (kernel pair.1 pair.2) payoff
        (payoffIntegrable_of_finite _ _))
      (payoffIntegrable_of_finite _ _) := by
  let value : Kept × Action → ℝ := fun pair =>
    expect (kernel pair.1 pair.2) payoff (payoffIntegrable_of_finite _ _)
  let tagged : Full → PMF ((Full × Action) × Term) := fun full =>
    (rule full).bind fun action =>
      (kernel (keep full) action).map fun term => ((full, action), term)
  have hmap (full : Full) (action : Action) :
      expect ((kernel (keep full) action).map fun term =>
          ((full, action), term))
        (fun tagged : (Full × Action) × Term => payoff tagged.2)
        (payoffIntegrable_of_finite _ _) =
        value (keep full, action) := by
    simpa only [value, Function.comp_def] using
      (expect_map (fun term : Term => ((full, action), term))
        (kernel (keep full) action)
        (fun tagged : (Full × Action) × Term => payoff tagged.2)
        (payoffIntegrable_of_finite _ _)
        (payoffIntegrable_of_finite _ _))
  have hinner (full : Full) :
      expect (tagged full) (fun tagged => payoff tagged.2)
        (payoffIntegrable_of_finite _ _) =
        expect (rule full) (fun action => value (keep full, action))
          (payoffIntegrable_of_finite _ _) := by
    calc
      _ = expect (rule full)
          (fun action => expect
            ((kernel (keep full) action).map fun term =>
              ((full, action), term))
            (fun tagged : (Full × Action) × Term => payoff tagged.2)
            (payoffIntegrable_of_finite _ _))
          (payoffIntegrable_of_finite _ _) := by
            exact expect_bind_tower (rule full)
              (fun action => (kernel (keep full) action).map fun term =>
                ((full, action), term))
              (fun tagged : (Full × Action) × Term => payoff tagged.2)
              (payoffIntegrable_of_finite _ _)
              (fun _ => payoffIntegrable_of_finite _ _)
      _ = _ := by
        apply expect_congr_on_support
        intro action _
        exact hmap full action
  have hjoint (full : Full) :
      expect ((rule full).map fun action => (keep full, action)) value
        (payoffIntegrable_of_finite _ _) =
        expect (rule full) (fun action => value (keep full, action))
          (payoffIntegrable_of_finite _ _) := by
    simpa only [Function.comp_def] using
      (expect_map (fun action => (keep full, action)) (rule full) value
        (payoffIntegrable_of_finite _ _)
        (payoffIntegrable_of_finite _ _))
  calc
    expect (outer.bind tagged) (fun tagged => payoff tagged.2)
        (payoffIntegrable_of_finite _ _) =
      expect outer (fun full => expect (tagged full)
        (fun tagged => payoff tagged.2) (payoffIntegrable_of_finite _ _))
        (payoffIntegrable_of_finite _ _) := by
          exact expect_bind_tower outer tagged
            (fun tagged => payoff tagged.2)
            (payoffIntegrable_of_finite _ _)
            (fun _ => payoffIntegrable_of_finite _ _)
    _ = expect outer
        (fun full => expect (rule full)
          (fun action => value (keep full, action))
          (payoffIntegrable_of_finite _ _))
        (payoffIntegrable_of_finite _ _) := by
          apply expect_congr_on_support
          intro full _
          exact hinner full
    _ = expect outer
        (fun full => expect ((rule full).map fun action =>
          (keep full, action)) value (payoffIntegrable_of_finite _ _))
        (payoffIntegrable_of_finite _ _) := by
          apply expect_congr_on_support
          intro full _
          exact (hjoint full).symm
    _ = expect (fullJoint outer keep rule) value
        (payoffIntegrable_of_finite _ _) := by
          exact (expect_bind_tower outer
            (fun full => (rule full).map fun action => (keep full, action))
            value (payoffIntegrable_of_finite _ _)
            (fun _ => payoffIntegrable_of_finite _ _)).symm
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
  let hsite : UtilityIntegrable
      (fun assignment who => semantics.utility who assignment) owner law :=
    payoffIntegrable_of_finite _ _
  let hjoint : PayoffIntegrable joint
      (fun pair => ∑ term : view.UtilitySite owner,
        siteTermContinuationValue pruning topological semantics policy owner
          fixedOwner target view hstable term pair.1 pair.2) :=
    payoffIntegrable_of_finite _ _
  refine ⟨hsite, hjoint, ?_⟩
  have hterm : ∀ term : view.UtilitySite owner,
      expect law (view.term term).value (payoffIntegrable_of_finite _ _) =
        expect joint (fun result =>
          siteTermContinuationValue pruning topological semantics policy owner
            fixedOwner target view hstable term result.1 result.2)
          (payoffIntegrable_of_finite _ _) := by
    intro term
    by_cases hrelevant :
        MAIDPruningFixpointGraph.UtilityView.IsRelevantUtilityTermUnder view
          (Pruning.restoreAllAt pruning target) target term
    · let termLaw :=
        relevantTermContinuationLawAt_of_edgeAdditionStableAt pruning
          topological semantics policy owner fixedOwner target view hstable
          term hrelevant
      let taggedLaw := context.contextLaw.bind fun full =>
        (rule full).bind fun action =>
          (termLaw.continuationLaw (keep full) action).map fun termValue =>
            ((full, action), termValue)
      have hlaw :
          law.map (siteFullActionTermProjection view target term) =
            taggedLaw := termLaw.joint_eq rule
      have hprojection :
          (fun result => (view.term term).payoff result.2) ∘
              siteFullActionTermProjection view target term =
            (view.term term).value := rfl
      calc
        expect law (view.term term).value
            (payoffIntegrable_of_finite _ _) =
          expect (law.map (siteFullActionTermProjection view target term))
            (fun result => (view.term term).payoff result.2)
            (payoffIntegrable_of_finite _ _) := by
              rw [← hprojection]
              exact (expect_map
                (siteFullActionTermProjection view target term) law
                (fun result => (view.term term).payoff result.2)
                (payoffIntegrable_of_finite _ _)
                (payoffIntegrable_of_finite _ _)).symm
        _ = expect taggedLaw
            (fun result => (view.term term).payoff result.2)
            (payoffIntegrable_of_finite _ _) :=
          expect_congr_law hlaw _ _ _
        _ = expect joint (fun result =>
              expect (termLaw.continuationLaw result.1 result.2)
                (view.term term).payoff (payoffIntegrable_of_finite _ _))
            (payoffIntegrable_of_finite _ _) :=
          expect_taggedContinuation context.contextLaw keep rule
            termLaw.continuationLaw (view.term term).payoff
        _ = expect joint (fun result =>
              siteTermContinuationValue pruning topological semantics policy
                owner fixedOwner target view hstable term result.1 result.2)
            (payoffIntegrable_of_finite _ _) := by
              apply expect_congr_on_support
              intro result _
              simp [siteTermContinuationValue, hrelevant, termLaw]
    · let termLaw := nonrelevantTermMarginalCertificate pruning topological
        semantics policy owner fixedOwner target view term hrelevant
      let projection := fun assignment : Assignment diagram =>
        Assignment.restrict diagram assignment (view.term term).parents
      let score := expect termLaw.marginalLaw (view.term term).payoff
        (payoffIntegrable_of_finite _ _)
      have hprojection :
          (view.term term).payoff ∘ projection =
            (view.term term).value := rfl
      have hlaw : law.map projection = termLaw.marginalLaw :=
        termLaw.marginal_eq rule
      calc
        expect law (view.term term).value
            (payoffIntegrable_of_finite _ _) =
          expect (law.map projection) (view.term term).payoff
            (payoffIntegrable_of_finite _ _) := by
              simpa only [hprojection] using
                (expect_map projection law (view.term term).payoff
                  (payoffIntegrable_of_finite _ _)
                  (payoffIntegrable_of_finite _ _)).symm
        _ = score := expect_congr_law hlaw _ _ _
        _ = expect joint (fun result =>
              siteTermContinuationValue pruning topological semantics policy
                owner fixedOwner target view hstable term result.1 result.2)
            (payoffIntegrable_of_finite _ _) := by
              have hvalue : (fun result : KeptContext pruning target ×
                  diagram.Value target.1 =>
                    siteTermContinuationValue pruning topological semantics
                      policy owner fixedOwner target view hstable term
                      result.1 result.2) = fun _ => score := by
                funext result
                simp [siteTermContinuationValue, hrelevant, termLaw, score]
              rw [hvalue]
              exact (expect_constant joint score
                (payoffIntegrable_of_finite _ _)).symm
  let value : view.UtilitySite owner →
      KeptContext pruning target × diagram.Value target.1 → ℝ :=
    fun term result =>
      siteTermContinuationValue pruning topological semantics policy owner
        fixedOwner target view hstable term result.1 result.2
  have hsum := expect_eq_sum_on_support law
    (fun term : view.UtilitySite owner => (view.term term).value)
    (fun assignment => semantics.utility owner assignment)
    (fun _ => payoffIntegrable_of_finite _ _) (by
      intro assignment _
      exact view.utility_eq_sum owner assignment)
  have hcomponent : ∀ term : view.UtilitySite owner,
      PayoffIntegrable joint (value term) :=
    fun _ => payoffIntegrable_of_finite _ _
  unfold siteRuleExpectedUtility GameTheory.expectedUtility
  calc
    expect law (fun assignment => semantics.utility owner assignment)
        hsite =
      ∑ term : view.UtilitySite owner,
        expect law (view.term term).value
          (payoffIntegrable_of_finite _ _) := hsum.2
    _ = ∑ term : view.UtilitySite owner,
          expect joint (value term) (hcomponent term) := by
      apply Finset.sum_congr rfl
      intro term _
      exact hterm term
    _ = expect joint (fun result => ∑ term : view.UtilitySite owner,
          value term result) hjoint := by
      simpa only [value] using (expect_sum joint value hcomponent).symm

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
        PMF (diagram.Value target.1),
      IsOptimalSiteRule semantics (pruning.expandPolicy policy) owner
        (pruning.expandOwnerPolicy owner fixedOwner) target
        (expandKeptSiteRule pruning target reducedRule) :=
  exists_reduced_isOptimalSiteRule pruning topological semantics policy owner
    fixedOwner target
      (siteLocalUtilityFactorsAt_of_edgeAdditionStableAt pruning topological
        semantics policy owner fixedOwner target view hstable)

end GameTheory.Experimental.PostArchitecture.MAIDPruningSiteReduction
