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
    PMF (Assignment diagram) :=
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
  contextLaw : PMF (FullContext target)
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
    diagram.Value target.1 → PMF (TermConfig view term)
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
  marginalLaw : PMF (TermConfig view term)
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

private theorem relevantTermLaw_eq_jointBind
    (pruning : Pruning diagram)
    [DecidableEq Player] [Fintype Node] [DecidableEq Node]
    (semantics : Semantics diagram) (policy : pruning.ReducedPolicy)
    (owner : Player) (target : DecisionSite diagram owner)
    (view : UtilityView semantics)
    (certificate : ReplacementInvariantUtilityLawAt pruning semantics policy
      owner target view)
    (replacement : OwnerPolicy diagram owner)
    (term : view.UtilitySite owner)
    (hrelevant : view.IsRelevantUtilityTerm target term) :
    (replacementLaw pruning semantics policy owner replacement).map
        (fun assignment => Assignment.restrict diagram assignment
          (view.term term).parents) =
      (fullJoint certificate.context.contextLaw
        (Config.restrict (pruning.kept_sub_observed target.1))
        (replacement target)).bind fun result =>
          (certificate.relevant term hrelevant).continuationLaw
            result.1 result.2 := by
  let termLaw := certificate.relevant term hrelevant
  let law := replacementLaw pruning semantics policy owner replacement
  let keep : FullContext target → KeptContext pruning target :=
    Config.restrict (pruning.kept_sub_observed target.1)
  let triple := fun assignment : Assignment diagram =>
    (Assignment.restrict diagram assignment
        (diagram.observedParents target.1),
      (assignment target.1,
        Assignment.restrict diagram assignment (view.term term).parents))
  have htriple := termLaw.joint_eq replacement
  calc
    law.map (fun assignment => Assignment.restrict diagram assignment
        (view.term term).parents) =
        (law.map triple).map (fun result => result.2.2) := by
      rw [PMF.map_comp]
      rfl
    _ = (certificate.context.contextLaw.bind fun full =>
          (replacement target full).bind fun action =>
            (termLaw.continuationLaw (keep full) action).map
              fun termConfig => (full, (action, termConfig))).map
              (fun result => result.2.2) := by
      rw [htriple]
    _ = (fullJoint certificate.context.contextLaw keep
          (replacement target)).bind fun result =>
            termLaw.continuationLaw result.1 result.2 := by
      simp [fullJoint, PMF.map_bind, PMF.bind_bind, PMF.map_comp,
        Function.comp_def]
      apply bind_congr_on_support
      intro full _
      apply bind_congr_on_support
      intro action _
      simpa only [show (fun x : TermConfig view term => x) = id from rfl]
        using (PMF.map_id (termLaw.continuationLaw (keep full) action))

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
  · let law := (certificate.relevant term hrelevant).continuationLaw kept action
    exact if h : PayoffIntegrable law (view.term term).payoff then
      expect law (view.term term).payoff h else 0
  · let law := (certificate.nonrelevant term hrelevant).marginalLaw
    exact if h : PayoffIntegrable law (view.term term).payoff then
      expect law (view.term term).payoff h else 0

private theorem expectedTerm_eq_jointValue
    (pruning : Pruning diagram)
    [DecidableEq Player] [Fintype Node] [DecidableEq Node]
    (semantics : Semantics diagram) (policy : pruning.ReducedPolicy)
    (owner : Player) (target : DecisionSite diagram owner)
    (view : UtilityView semantics)
    (certificate : ReplacementInvariantUtilityLawAt pruning semantics policy
      owner target view)
    (replacement : OwnerPolicy diagram owner)
    (term : view.UtilitySite owner)
    (hterm : PayoffIntegrable
      (replacementLaw pruning semantics policy owner replacement)
      (view.term term).value) :
    ∃ hvalue : PayoffIntegrable
      (fullJoint certificate.context.contextLaw
        (Config.restrict (pruning.kept_sub_observed target.1))
        (replacement target))
      (fun result => termContinuationValue pruning semantics policy owner
        target view certificate term result.1 result.2),
      expect (replacementLaw pruning semantics policy owner replacement)
          (view.term term).value hterm =
        expect (fullJoint certificate.context.contextLaw
          (Config.restrict (pruning.kept_sub_observed target.1))
          (replacement target))
          (fun result => termContinuationValue pruning semantics policy owner
            target view certificate term result.1 result.2) hvalue := by
  classical
  let law := replacementLaw pruning semantics policy owner replacement
  let keep : FullContext target → KeptContext pruning target :=
    Config.restrict (pruning.kept_sub_observed target.1)
  let joint := fullJoint certificate.context.contextLaw keep
    (replacement target)
  let projection := fun assignment : Assignment diagram =>
    Assignment.restrict diagram assignment (view.term term).parents
  have hcomp : (view.term term).payoff ∘ projection =
      (view.term term).value := rfl
  have hmap : PayoffIntegrable (law.map projection)
      (view.term term).payoff := by
    apply (payoffIntegrable_map_iff projection law
      (view.term term).payoff).mpr
    simpa only [hcomp, law] using hterm
  have hmapValue :
      expect law (view.term term).value hterm =
        expect (law.map projection) (view.term term).payoff hmap := by
    simpa only [hcomp] using
      (expect_map projection law (view.term term).payoff hterm hmap).symm
  by_cases hrelevant : view.IsRelevantUtilityTerm target term
  · let termLaw := certificate.relevant term hrelevant
    let kernel := fun result : KeptContext pruning target ×
        diagram.Value target.1 =>
      termLaw.continuationLaw result.1 result.2
    have hlaw : law.map projection = joint.bind kernel :=
      relevantTermLaw_eq_jointBind pruning semantics policy owner target view
        certificate replacement term hrelevant
    have hbind : PayoffIntegrable (joint.bind kernel)
        (view.term term).payoff := payoffIntegrable_congr_law hlaw hmap
    let value := fun result : KeptContext pruning target ×
        diagram.Value target.1 =>
      termContinuationValue pruning semantics policy owner target view
        certificate term result.1 result.2
    have hagree : ∀ (result) (hresult : result ∈ joint.support),
        value result = expect (kernel result) (view.term term).payoff
          (payoffIntegrable_bind_conditional_on_support joint kernel
            (view.term term).payoff hbind result hresult) := by
      intro result hresult
      have hbranch := payoffIntegrable_bind_conditional_on_support joint
        kernel (view.term term).payoff hbind result hresult
      simp [value, termContinuationValue, hrelevant, kernel, termLaw,
        hbranch]
    have hvalue := payoffIntegrable_bind_conditionalValue_on_support joint
      kernel (view.term term).payoff hbind value hagree
    refine ⟨hvalue, ?_⟩
    calc
      expect law (view.term term).value hterm =
          expect (law.map projection) (view.term term).payoff hmap := hmapValue
      _ = expect (joint.bind kernel) (view.term term).payoff hbind :=
        expect_congr_law hlaw _ hmap hbind
      _ = expect joint value hvalue :=
        expect_bind_tower_on_support joint kernel (view.term term).payoff
          hbind value hagree
  · let termLaw := certificate.nonrelevant term hrelevant
    have hlaw : law.map projection = termLaw.marginalLaw :=
      termLaw.marginal_eq replacement
    have hmarg : PayoffIntegrable termLaw.marginalLaw
        (view.term term).payoff := payoffIntegrable_congr_law hlaw hmap
    let score := expect termLaw.marginalLaw (view.term term).payoff hmarg
    let value := fun result : KeptContext pruning target ×
        diagram.Value target.1 =>
      termContinuationValue pruning semantics policy owner target view
        certificate term result.1 result.2
    have hvalueEq : value = fun _ => score := by
      funext result
      simp [value, termContinuationValue, hrelevant, score, termLaw, hmarg]
    have hvalue : PayoffIntegrable joint value := by
      rw [hvalueEq]
      exact payoffIntegrable_constant joint score
    refine ⟨hvalue, ?_⟩
    calc
      expect law (view.term term).value hterm =
          expect (law.map projection) (view.term term).payoff hmap := hmapValue
      _ = score := expect_congr_law hlaw _ hmap hmarg
      _ = expect joint value hvalue := by
        let hconst := payoffIntegrable_constant joint score
        calc
          score = expect joint (fun _ => score) hconst :=
            (expect_constant joint score hconst).symm
          _ = expect joint value hvalue :=
            expect_congr_on_support
              (fun result _ => (congrFun hvalueEq result).symm)
              hconst hvalue

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
      owner target view)
    (hterm : ∀ (replacement : OwnerPolicy diagram owner)
      (term : view.UtilitySite owner),
      PayoffIntegrable (replacementLaw pruning semantics policy owner replacement)
        (view.term term).value)
    (hother : ∀ (other : Player), other ≠ owner →
      ∀ replacement : OwnerPolicy diagram other,
        UtilityIntegrable
          (fun assignment who => semantics.utility who assignment) other
          (replacementLaw pruning semantics policy other replacement)) :
    LocalUtilityFactorsAt pruning semantics policy owner target := by
  classical
  refine ⟨certificate.context.contextLaw,
    fun kept action => ∑ term : view.UtilitySite owner,
      termContinuationValue pruning semantics policy owner target view
        certificate term kept action, ?_, hother⟩
  intro replacement
  let law := replacementLaw pruning semantics policy owner replacement
  let keep : FullContext target → KeptContext pruning target :=
    Config.restrict (diagram := diagram)
      (pruning.kept_sub_observed target.1)
  let joint := fullJoint certificate.context.contextLaw keep
    (replacement target)
  let value := fun term : view.UtilitySite owner =>
    fun result : KeptContext pruning target × diagram.Value target.1 =>
      termContinuationValue pruning semantics policy owner target view
        certificate term result.1 result.2
  have hcomponent : ∀ term : view.UtilitySite owner,
      PayoffIntegrable joint (value term) := by
    intro term
    exact (expectedTerm_eq_jointValue pruning semantics policy owner target
      view certificate replacement term (hterm replacement term)).choose
  have heach : ∀ term : view.UtilitySite owner,
      expect law (view.term term).value (hterm replacement term) =
        expect joint (value term) (hcomponent term) := by
    intro term
    exact (expectedTerm_eq_jointValue pruning semantics policy owner target
      view certificate replacement term (hterm replacement term)).choose_spec
  have hsum := expect_eq_sum_on_support law
    (fun term : view.UtilitySite owner => (view.term term).value)
    (fun assignment => semantics.utility owner assignment)
    (hterm replacement) (by
      intro assignment _
      exact view.utility_eq_sum owner assignment)
  let hplay : UtilityIntegrable
      (fun assignment who => semantics.utility who assignment) owner law :=
    hsum.1
  let hjoint := payoffIntegrable_sum joint value hcomponent
  refine ⟨hplay, hjoint, ?_⟩
  calc
    expectedUtility (fun assignment who => semantics.utility who assignment)
        owner law hplay =
      ∑ term : view.UtilitySite owner,
        expect law (view.term term).value (hterm replacement term) := hsum.2
    _ = ∑ term : view.UtilitySite owner,
          expect joint (value term) (hcomponent term) := by
      apply Finset.sum_congr rfl
      intro term _
      exact heach term
    _ = expect joint (fun result => ∑ term : view.UtilitySite owner,
          value term result) hjoint :=
      (expect_sum joint value hcomponent).symm

end GameTheory.Experimental.PostArchitecture.MAIDReplacementInvariantUtility
