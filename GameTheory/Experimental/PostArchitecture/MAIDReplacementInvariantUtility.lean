/-
# EXP-105: replacement-invariant utility laws

This module isolates the graph-free distributional seam between utility-leaf
separation and local MAID observation reduction.  Its certificates refer only
to canonical native play under a full owner-policy replacement.  They contain
no reduced replacement witness, preference comparison, or coverage claim.
-/

import GameTheory.Experimental.PostArchitecture.MAIDLocalReduction
import GameTheory.Experimental.PostArchitecture.MAIDUtilityAugmentation

noncomputable section

open scoped BigOperators

namespace GameTheory.Experimental.PostArchitecture.MAIDReplacementInvariantUtility

open GameTheory
open GameTheory.Math.Probability
open GameTheory.Languages.MAID
open GameTheory.Languages.MAID.ObservationPruning
open GameTheory.Languages.MAID.Strategic
open GameTheory.Experimental.PostArchitecture.MAIDKernelMarginalization
open GameTheory.Experimental.PostArchitecture.MAIDLocalReduction
open GameTheory.Experimental.PostArchitecture.MAIDRequisiteObservation

universe uPlayer uNode

variable {Player : Type uPlayer} {Node : Type uNode}
variable {diagram : Structure Player Node} {semantics : Semantics diagram}

/-- Canonical native play after replacing one owner's complete policy. -/
def replacementLaw (pruning : Pruning diagram)
    [DecidableEq Player] [Fintype Node] [DecidableEq Node]
    (semantics : Semantics diagram) (policy : pruning.ReducedPolicy)
    (owner : Player) (replacement : OwnerPolicy diagram owner) :
    FinDist (Assignment diagram) :=
  (nativeBehavioralGameForm semantics).play
    (Profile.update (pruning.expandPolicy policy) owner replacement)

/-- The target's complete declared observation context. -/
abbrev FullContext {owner : Player}
    (target : DecisionSite diagram owner) :=
  Config diagram (diagram.observedParents target.1)

/-- The target context retained by a pruning. -/
abbrev KeptContext {owner : Player} (pruning : Pruning diagram)
    (target : DecisionSite diagram owner) :=
  Config diagram (pruning.kept target.1)

/-- The exact finite configuration consumed by one utility term. -/
abbrev TermConfig (view : UtilityView semantics) {owner : Player}
    (term : view.UtilitySite owner) :=
  Config diagram (view.term term).parents

/-- One context law works for every owner replacement, and the target action
is drawn from exactly the replacement kernel at that full context. -/
structure ReplacementContextLawAt (pruning : Pruning diagram)
    [DecidableEq Player] [Fintype Node] [DecidableEq Node]
    (semantics : Semantics diagram) (policy : pruning.ReducedPolicy)
    (owner : Player) (target : DecisionSite diagram owner) where
  contextLaw : FinDist (FullContext target)
  contextAction_eq : ∀ replacement : OwnerPolicy diagram owner,
    (replacementLaw pruning semantics policy owner replacement).map
        (fun assignment =>
          (Assignment.restrict diagram assignment
            (diagram.observedParents target.1), assignment target.1)) =
      contextLaw.bind fun context =>
        (replacement target context).map fun action => (context, action)

/-- A term's joint law factors through the retained context and target action,
using one continuation kernel uniformly over all owner replacements. -/
structure TermContinuationLawAt (pruning : Pruning diagram)
    [DecidableEq Player] [Fintype Node] [DecidableEq Node]
    (semantics : Semantics diagram) (policy : pruning.ReducedPolicy)
    (owner : Player) (target : DecisionSite diagram owner)
    (view : UtilityView semantics)
    (context : ReplacementContextLawAt pruning semantics policy owner target)
    (term : view.UtilitySite owner) where
  continuationLaw : KeptContext pruning target →
    diagram.Value target.1 → FinDist (TermConfig view term)
  joint_eq : ∀ replacement : OwnerPolicy diagram owner,
    (replacementLaw pruning semantics policy owner replacement).map
        (fun assignment =>
          (Assignment.restrict diagram assignment
              (diagram.observedParents target.1),
            (assignment target.1,
              Assignment.restrict diagram assignment
                (view.term term).parents))) =
      context.contextLaw.bind fun full =>
        (replacement target full).bind fun action =>
          (continuationLaw
            (Config.restrict (pruning.kept_sub_observed target.1) full)
            action).map fun termConfig => (full, (action, termConfig))

/-- A term unaffected by the target replacement has one exact marginal law
for its typed parent configuration. -/
structure ReplacementInvariantTermMarginalAt (pruning : Pruning diagram)
    [DecidableEq Player] [Fintype Node] [DecidableEq Node]
    (semantics : Semantics diagram) (policy : pruning.ReducedPolicy)
    (owner : Player) (view : UtilityView semantics)
    (term : view.UtilitySite owner) where
  marginalLaw : FinDist (TermConfig view term)
  marginal_eq : ∀ replacement : OwnerPolicy diagram owner,
    (replacementLaw pruning semantics policy owner replacement).map
        (fun assignment => Assignment.restrict diagram assignment
          (view.term term).parents) =
      marginalLaw

/-- Exact replacement-invariant distributional data for every distinct
utility term, split by directed relevance to the target decision. -/
structure ReplacementInvariantUtilityLawAt (pruning : Pruning diagram)
    [DecidableEq Player] [Fintype Node] [DecidableEq Node]
    (semantics : Semantics diagram) (policy : pruning.ReducedPolicy)
    (owner : Player) (target : DecisionSite diagram owner)
    (view : UtilityView semantics) where
  context : ReplacementContextLawAt pruning semantics policy owner target
  relevant : ∀ term : view.UtilitySite owner,
    view.IsRelevantUtilityTerm target term →
      TermContinuationLawAt pruning semantics policy owner target view
        context term
  nonrelevant : ∀ term : view.UtilitySite owner,
    ¬ view.IsRelevantUtilityTerm target term →
      ReplacementInvariantTermMarginalAt pruning semantics policy owner view
        term

private noncomputable def termContinuationValue (pruning : Pruning diagram)
    [DecidableEq Player] [Fintype Node] [DecidableEq Node]
    (semantics : Semantics diagram) (policy : pruning.ReducedPolicy)
    (owner : Player) (target : DecisionSite diagram owner)
    (view : UtilityView semantics)
    (certificate : ReplacementInvariantUtilityLawAt pruning semantics policy
      owner target view)
    (term : view.UtilitySite owner) (kept : KeptContext pruning target)
    (action : diagram.Value target.1) : ℝ := by
  classical
  by_cases hrelevant : view.IsRelevantUtilityTerm target term
  · exact ((certificate.relevant term hrelevant).continuationLaw kept action).expect
      (view.term term).payoff
  · exact (certificate.nonrelevant term hrelevant).marginalLaw.expect
      (view.term term).payoff

/-- Replacement-invariant term laws assemble into the existing graph-free
local utility factorization.  No one-site shape or value finiteness is needed
at this boundary. -/
theorem localUtilityFactorsAt_of_replacementInvariantUtilityLawAt
    (pruning : Pruning diagram)
    [DecidableEq Player] [Fintype Node] [DecidableEq Node]
    (semantics : Semantics diagram) (policy : pruning.ReducedPolicy)
    (owner : Player) (target : DecisionSite diagram owner)
    (view : UtilityView semantics)
    (certificate : ReplacementInvariantUtilityLawAt pruning semantics policy
      owner target view) :
    LocalUtilityFactorsAt pruning semantics policy owner target := by
  classical
  refine ⟨certificate.context.contextLaw,
    fun kept action => ∑ term : view.UtilitySite owner,
      termContinuationValue pruning semantics policy owner target view
        certificate term kept action, ?_⟩
  intro replacement
  let law := replacementLaw pruning semantics policy owner replacement
  let keep : FullContext target → KeptContext pruning target :=
    Config.restrict (diagram := diagram)
      (pruning.kept_sub_observed target.1)
  let joint := fullJoint certificate.context.contextLaw keep
    (replacement target)
  have hterm : ∀ term : view.UtilitySite owner,
      law.expect (view.term term).value =
        joint.expect (fun result =>
          termContinuationValue pruning semantics policy owner target view
            certificate term result.1 result.2) := by
    intro term
    by_cases hrelevant : view.IsRelevantUtilityTerm target term
    · let termLaw := certificate.relevant term hrelevant
      calc
        law.expect (view.term term).value =
            (law.map fun assignment =>
              (Assignment.restrict diagram assignment
                  (diagram.observedParents target.1),
                (assignment target.1,
                  Assignment.restrict diagram assignment
                    (view.term term).parents))).expect
              (fun result => (view.term term).payoff result.2.2) := by
                rw [FinDist.expect_map]
                rfl
        _ = (certificate.context.contextLaw.bind fun full =>
              (replacement target full).bind fun action =>
                (termLaw.continuationLaw (keep full) action).map
                  fun termConfig => (full, (action, termConfig))).expect
              (fun result => (view.term term).payoff result.2.2) := by
                rw [termLaw.joint_eq replacement]
        _ = joint.expect (fun result =>
              termContinuationValue pruning semantics policy owner target view
                certificate term result.1 result.2) := by
                simp [joint, fullJoint, keep, FinDist.expect_bind,
                  FinDist.expect_map, termContinuationValue, hrelevant,
                  termLaw]
    · let termLaw := certificate.nonrelevant term hrelevant
      calc
        law.expect (view.term term).value =
            (law.map fun assignment =>
              Assignment.restrict diagram assignment
                (view.term term).parents).expect
              (view.term term).payoff := by
                rw [FinDist.expect_map]
                rfl
        _ = termLaw.marginalLaw.expect (view.term term).payoff := by
              rw [termLaw.marginal_eq replacement]
        _ = joint.expect (fun result =>
              termContinuationValue pruning semantics policy owner target view
                certificate term result.1 result.2) := by
                simp [joint, fullJoint, termContinuationValue, hrelevant,
                  termLaw, FinDist.expect_const]
  change law.expect (fun assignment => semantics.utility owner assignment) = _
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
            termContinuationValue pruning semantics policy owner target view
              certificate term result.1 result.2) := by
      apply Finset.sum_congr rfl
      intro term _
      exact hterm term
    _ = joint.expect (fun result => ∑ term : view.UtilitySite owner,
          termContinuationValue pruning semantics policy owner target view
            certificate term result.1 result.2) :=
      FinDist.expect_sum_comm joint fun term result =>
        termContinuationValue pruning semantics policy owner target view
          certificate term result.1 result.2

end GameTheory.Experimental.PostArchitecture.MAIDReplacementInvariantUtility
