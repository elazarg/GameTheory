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

open GameTheory
open GameTheory.Math.Probability
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
      PMF (diagram.Value target.1),
    ∃ hsite : UtilityIntegrable
        (fun assignment who => semantics.utility who assignment) owner
        (siteReplacementLaw semantics base owner replacement target rule),
      ∃ hjoint : PayoffIntegrable
          (fullJoint context.contextLaw
            (Config.restrict (pruning.kept_sub_observed target.1)) rule)
          (fun pair => continuationValue pair.1 pair.2),
        siteRuleExpectedUtility semantics base owner replacement target
            rule hsite =
          expect (fullJoint context.contextLaw
            (Config.restrict (pruning.kept_sub_observed target.1)) rule)
            (fun pair => continuationValue pair.1 pair.2) hjoint

/-- Expand a target rule on the retained context back to the target's full
declared observation context. -/
def expandKeptSiteRule (pruning : Pruning diagram) {owner : Player}
    (target : DecisionSite diagram owner)
    (rule : KeptContext pruning target →
      PMF (diagram.Value target.1)) :
    FullContext target →
      PMF (diagram.Value target.1) :=
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
        PMF (diagram.Value target.1),
      IsOptimalSiteRule semantics (pruning.expandPolicy policy) owner
        (pruning.expandOwnerPolicy owner fixedOwner) target
        (expandKeptSiteRule pruning target reducedRule) := by
  obtain ⟨best, hbest⟩ := exists_isOptimalSiteRule topological semantics
    (pruning.expandPolicy policy) owner
    (pruning.expandOwnerPolicy owner fixedOwner) target
  let keep : FullContext target → KeptContext pruning target :=
    Config.restrict (pruning.kept_sub_observed target.1)
  let reducedRule : KeptContext pruning target →
      PMF (diagram.Value target.1) :=
    averagedKernel factors.context.contextLaw keep best
  refine ⟨reducedRule, ?_⟩
  intro alternative
  obtain ⟨hbestSite, haltSite, hle⟩ := hbest alternative
  obtain ⟨_, hbestJoint, hbestEq⟩ := factors.utility_eq best
  obtain ⟨hredSite, hredJoint, hredEq⟩ :=
    factors.utility_eq (expandKeptSiteRule pruning target reducedRule)
  have hjointLaw :
      fullJoint factors.context.contextLaw keep best =
        fullJoint factors.context.contextLaw keep
          (expandKeptSiteRule pruning target reducedRule) := by
    exact fullJoint_eq_fullJoint_averagedKernel
      factors.context.contextLaw keep best
  have hvalue :
      siteRuleExpectedUtility semantics (pruning.expandPolicy policy) owner
          (pruning.expandOwnerPolicy owner fixedOwner) target best hbestSite =
        siteRuleExpectedUtility semantics (pruning.expandPolicy policy) owner
          (pruning.expandOwnerPolicy owner fixedOwner) target
          (expandKeptSiteRule pruning target reducedRule) hredSite := by
    calc
      _ = expect (fullJoint factors.context.contextLaw keep best)
          (fun pair => factors.continuationValue pair.1 pair.2)
          hbestJoint := hbestEq
      _ = expect (fullJoint factors.context.contextLaw keep
            (expandKeptSiteRule pruning target reducedRule))
          (fun pair => factors.continuationValue pair.1 pair.2)
          hredJoint := expect_congr_law hjointLaw _ hbestJoint hredJoint
      _ = _ := hredEq.symm
  exact ⟨hredSite, haltSite, hle.trans hvalue.le⟩

end GameTheory.Experimental.PostArchitecture.MAIDSiteLocalReduction
