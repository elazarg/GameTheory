/-
# EXP-107: graph-free target-site observation reduction

This module isolates the semantic endpoint needed by target-site graphical
reasoning.  If every target rule has one expected-utility representation that
depends on its full context only through the kept context and chosen action,
then an optimal full-context rule can be averaged onto the kept context
without losing utility.  Other decision sites of the same owner remain fixed
at an arbitrary reduced owner policy.

No graph criterion, deviation coverage, or equilibrium claim is made here.
-/

import GameTheory.Experimental.PostArchitecture.MAIDKernelMarginalization
import GameTheory.Experimental.PostArchitecture.MAIDSiteOptimality

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.MAIDSiteLocalReduction

open GameTheory.Languages.MAID
open GameTheory.Languages.MAID.ObservationPruning
open GameTheory.Experimental.PostArchitecture.MAIDKernelMarginalization
open GameTheory.Experimental.PostArchitecture.MAIDReplacementInvariantUtility
open GameTheory.Experimental.PostArchitecture.MAIDSiteOptimality
open GameTheory.Experimental.PostArchitecture.MAIDSiteReplacementContext

universe uPlayer uNode uValue

variable {Player : Type uPlayer} {Node : Type uNode}
variable
  {diagram : Structure.{uPlayer, uNode, max uNode uValue} Player Node}

/-- Exact site-local utility data sufficient to forget observations at one
target.  The context law is the canonical pre-target law shared by every
target rule.  The utility identity is uniform over all behavioral target
rules, while every other rule of the owner remains fixed. -/
structure SiteLocalUtilityFactorsAt (pruning : Pruning diagram)
    [DecidableEq Player] [Fintype Node] [DecidableEq Node]
    (semantics : Semantics diagram) (base : Policy diagram)
    (owner : Player) (replacement : OwnerPolicy diagram owner)
    (target : DecisionSite diagram owner) where
  context :
    SiteReplacementContextLawAt semantics base owner replacement target
  continuationValue :
    KeptContext pruning target → diagram.Value target.1 → ℝ
  utility_eq : ∀ rule : FullContext target →
      GameTheory.Math.Probability.FinDist (diagram.Value target.1),
    siteRuleExpectedUtility semantics base owner replacement target rule =
      context.contextLaw.expect fun full =>
        (rule full).expect fun action =>
          continuationValue
            (Config.restrict (pruning.kept_sub_observed target.1) full)
            action

/-- Expand a target rule on the retained context back to the target's full
declared observation context. -/
def expandKeptSiteRule (pruning : Pruning diagram) {owner : Player}
    (target : DecisionSite diagram owner)
    (rule : KeptContext pruning target →
      GameTheory.Math.Probability.FinDist (diagram.Value target.1)) :
    FullContext target →
      GameTheory.Math.Probability.FinDist (diagram.Value target.1) :=
  fun full =>
    rule (Config.restrict (pruning.kept_sub_observed target.1) full)

/-- An optimal target rule exists in the image of retained-context expansion.
The full-context optimum is averaged conditionally on the retained context;
the shared continuation representation proves that this preserves its exact
expected utility.  The fixed policy at the owner's other sites is arbitrary
within the proposed pruning. -/
theorem exists_reduced_isOptimalSiteRule
    (pruning : Pruning diagram)
    [DecidableEq Player] [Fintype Node] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    [∀ node, DecidableEq (diagram.Value node)]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (semantics : Semantics diagram) (policy : pruning.ReducedPolicy)
    (owner : Player) (fixedOwner : pruning.ReducedOwnerPolicy owner)
    (target : DecisionSite diagram owner)
    (factors : SiteLocalUtilityFactorsAt pruning semantics
      (pruning.expandPolicy policy) owner
      (pruning.expandOwnerPolicy owner fixedOwner) target) :
    ∃ reducedRule : KeptContext pruning target →
        GameTheory.Math.Probability.FinDist (diagram.Value target.1),
      IsOptimalSiteRule semantics (pruning.expandPolicy policy) owner
        (pruning.expandOwnerPolicy owner fixedOwner) target
        (expandKeptSiteRule pruning target reducedRule) := by
  obtain ⟨best, hbest⟩ := exists_isOptimalSiteRule topological semantics
    (pruning.expandPolicy policy) owner
    (pruning.expandOwnerPolicy owner fixedOwner) target
  let keep : FullContext target → KeptContext pruning target :=
    Config.restrict (pruning.kept_sub_observed target.1)
  let reducedRule : KeptContext pruning target →
      GameTheory.Math.Probability.FinDist (diagram.Value target.1) :=
    averagedKernel factors.context.contextLaw keep best
  refine ⟨reducedRule, ?_⟩
  intro alternative
  calc
    siteRuleExpectedUtility semantics (pruning.expandPolicy policy) owner
        (pruning.expandOwnerPolicy owner fixedOwner) target alternative ≤
      siteRuleExpectedUtility semantics (pruning.expandPolicy policy) owner
        (pruning.expandOwnerPolicy owner fixedOwner) target best :=
      hbest alternative
    _ = factors.context.contextLaw.expect (fun full =>
          (best full).expect fun action =>
            factors.continuationValue (keep full) action) := by
      rw [factors.utility_eq best]
    _ = (factors.context.contextLaw.map keep).expect (fun kept =>
          (reducedRule kept).expect fun action =>
            factors.continuationValue kept action) := by
      exact expect_kernel_eq_averagedKernel factors.context.contextLaw keep
        best factors.continuationValue
    _ = factors.context.contextLaw.expect (fun full =>
          (expandKeptSiteRule pruning target reducedRule full).expect
            fun action => factors.continuationValue (keep full) action) := by
      rw [GameTheory.Math.Probability.FinDist.expect_map]
      rfl
    _ = siteRuleExpectedUtility semantics (pruning.expandPolicy policy) owner
        (pruning.expandOwnerPolicy owner fixedOwner) target
        (expandKeptSiteRule pruning target reducedRule) := by
      rw [factors.utility_eq]

end GameTheory.Experimental.PostArchitecture.MAIDSiteLocalReduction
