/-
# EXP-105: replacement-uniform relevant utility continuation

This module constructs one relevant-term continuation from the fixed-policy
graphical conditional-independence result.  The continuation is chosen from a
constant-action replacement and is then reused for every owner replacement.
-/

import GameTheory.Experimental.PostArchitecture.MAIDTargetSurgery
import GameTheory.Experimental.PostArchitecture.MAIDUtilityContinuationFromCI

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.MAIDRelevantUtilityContinuation

open GameTheory
open GameTheory.Math.Probability
open GameTheory.Languages.MAID
open GameTheory.Languages.MAID.ObservationPruning
open GameTheory.Languages.MAID.Strategic
open GameTheory.Experimental.PostArchitecture.FiniteConditionalContinuation
open GameTheory.Experimental.PostArchitecture.MAIDReplacementContext
open GameTheory.Experimental.PostArchitecture.MAIDReplacementInvariantUtility
open GameTheory.Experimental.PostArchitecture.MAIDRequisiteObservation
open GameTheory.Experimental.PostArchitecture.MAIDTargetSurgery
open GameTheory.Experimental.PostArchitecture.MAIDUtilityAugmentation
open GameTheory.Experimental.PostArchitecture.MAIDUtilityContinuationFromCI
open GameTheory.Experimental.PostArchitecture.MAIDUtilityFactorization

universe uPlayer uNode

variable {Player : Type uPlayer} {Node : Type uNode}
variable {diagram : Structure Player Node} {semantics : Semantics diagram}

/-- The whole set removed from the target observation context by a pruning. -/
def removedObservations [DecidableEq Node]
    (pruning : Pruning diagram) {owner : Player}
    (target : DecisionSite diagram owner) : Finset Node :=
  diagram.observedParents target.1 \ pruning.kept target.1

/-- Recode a pruning-kept context and target action as the fixed-policy CI
module's kept-action value, without transporting configuration types. -/
def pruningKeptAction [DecidableEq Node] (pruning : Pruning diagram)
    {owner : Player} (target : DecisionSite diagram owner)
    (kept : KeptContext pruning target) (action : diagram.Value target.1) :
    KeptAction target (removedObservations pruning target) :=
  ((fun node => kept ⟨node.1, by
      have hobserved := (Finset.mem_sdiff.mp node.2).1
      have hnotRemoved := (Finset.mem_sdiff.mp node.2).2
      by_contra hnotKept
      apply hnotRemoved
      change node.1 ∈ diagram.observedParents target.1 \
        pruning.kept target.1
      exact Finset.mem_sdiff.mpr ⟨hobserved, hnotKept⟩⟩),
    action)

private theorem pruningKeptAction_restrict [DecidableEq Node]
    (pruning : Pruning diagram) {owner : Player}
    (target : DecisionSite diagram owner) (full : FullContext target)
    (action : diagram.Value target.1) :
    pruningKeptAction pruning target
        (Config.restrict (pruning.kept_sub_observed target.1) full) action =
      keepFullAction target (removedObservations pruning target)
        (full, action) := by
  apply Prod.ext
  · funext node
    rfl
  · rfl

/-- The replacement-independent continuation selected from the canonical law
under the constant target action. -/
def constantActionContinuation
    (pruning : Pruning diagram)
    [DecidableEq Player] [Fintype Node] [DecidableEq Node]
    (semantics : Semantics diagram) (policy : pruning.ReducedPolicy)
    (owner : Player) (target : DecisionSite diagram owner)
    (hunique : ∀ site : DecisionSite diagram owner, site = target)
    (view : UtilityView semantics) (term : view.UtilitySite owner)
    (kept : KeptContext pruning target) (action : diagram.Value target.1) :
    FinDist (MAIDReplacementInvariantUtility.TermConfig view term) :=
  let constantOwner := constantActionOwnerPolicy target hunique action
  let constantPolicy :=
    Profile.update (sig := nativeBehavioralSignature diagram)
      (pruning.expandPolicy policy) owner constantOwner
  continuation (augmentedLaw view owner constantPolicy)
    (fullAction view target) (termConfig view term)
    (keepFullAction target (removedObservations pruning target))
    (pruningKeptAction pruning target kept action)

private theorem bind_tagged_prob
    {First Second : Type*} (outer : FinDist First)
    (kernel : First → FinDist Second) (first : First) (second : Second) :
    (outer.bind fun candidate =>
      (kernel candidate).map fun value => (candidate, value)).prob
        (first, second) =
      outer.prob first * (kernel first).prob second := by
  classical
  rw [FinDist.prob_bind]
  calc
    outer.expect (fun candidate =>
        ((kernel candidate).map fun value => (candidate, value)).prob
          (first, second)) =
        outer.expect (fun candidate =>
          if first = candidate then (kernel first).prob second else 0) := by
      apply FinDist.expect_congr
      intro candidate _
      by_cases heq : first = candidate
      · subst candidate
        rw [if_pos rfl]
        exact FinDist.prob_map_of_injective
          (fun value => (first, value)) (fun _ _ h => (Prod.mk.inj h).2)
          (kernel first) second
      · rw [if_neg heq, FinDist.prob_eq_zero_iff]
        intro hsupport
        rw [FinDist.support_map] at hsupport
        obtain ⟨value, _, hvalue⟩ := hsupport
        exact heq (congrArg Prod.fst hvalue).symm
    _ = outer.prob first * (kernel first).prob second := by
      rw [FinDist.expect_ite_eq]

private theorem nested_bind_tagged_prob
    {Full Action Term Kept : Type*}
    (outer : FinDist Full) (rule : Full → FinDist Action)
    (keep : Full → Kept) (kernel : Kept → Action → FinDist Term)
    (full : Full) (action : Action) (term : Term) :
    (outer.bind fun candidate =>
      (rule candidate).bind fun chosen =>
        (kernel (keep candidate) chosen).map fun termValue =>
          (candidate, (chosen, termValue))).prob (full, (action, term)) =
      outer.prob full * (rule full).prob action *
        (kernel (keep full) action).prob term := by
  have hrepacked :
      outer.bind (fun candidate =>
          (rule candidate).bind fun chosen =>
            (kernel (keep candidate) chosen).map fun termValue =>
              (candidate, (chosen, termValue))) =
        outer.bind fun candidate =>
          ((rule candidate).bind fun chosen =>
            (kernel (keep candidate) chosen).map fun termValue =>
              (chosen, termValue)).map fun pair => (candidate, pair) := by
    apply FinDist.bind_congr
    intro candidate _
    rw [FinDist.map_bind]
    apply FinDist.bind_congr
    intro chosen _
    rw [FinDist.map_comp]
    rfl
  rw [hrepacked, bind_tagged_prob]
  rw [bind_tagged_prob]
  ring

private theorem augmented_joint_eq_native_joint
    [Fintype Node] [DecidableEq Node]
    (view : UtilityView semantics) (owner : Player) (policy : Policy diagram)
    (target : DecisionSite diagram owner) (term : view.UtilitySite owner) :
    (augmentedLaw view owner policy).map
        (fun assignment =>
          (fullAction view target assignment,
            termConfig view term assignment)) =
      ((nativeBehavioralGameForm semantics).play policy).map
        (fun assignment =>
          ((Assignment.restrict diagram assignment
              (diagram.observedParents target.1), assignment target.1),
            Assignment.restrict diagram assignment
              (view.term term).parents)) := by
  unfold augmentedLaw
  rw [FinDist.map_comp]
  apply congrArg
    (fun observable =>
      ((nativeBehavioralGameForm semantics).play policy).map observable)
  funext assignment
  rfl

private theorem augmented_fullAction_eq_native_contextAction
    [Fintype Node] [DecidableEq Node]
    (view : UtilityView semantics) (owner : Player) (policy : Policy diagram)
    (target : DecisionSite diagram owner) :
    (augmentedLaw view owner policy).map (fullAction view target) =
      ((nativeBehavioralGameForm semantics).play policy).map
        (fun assignment =>
          (Assignment.restrict diagram assignment
            (diagram.observedParents target.1), assignment target.1)) := by
  unfold augmentedLaw
  rw [FinDist.map_comp]
  apply congrArg
    (fun observable =>
      ((nativeBehavioralGameForm semantics).play policy).map observable)
  funext assignment
  rfl

private theorem native_associated_prob_eq_augmented_joint_prob
    [Fintype Node] [DecidableEq Node]
    [∀ node, DecidableEq (diagram.Value node)]
    (view : UtilityView semantics) (owner : Player) (policy : Policy diagram)
    (target : DecisionSite diagram owner) (term : view.UtilitySite owner)
    (context : FullContext target) (action : diagram.Value target.1)
    (termValue : MAIDReplacementInvariantUtility.TermConfig view term) :
    (((nativeBehavioralGameForm semantics).play policy).map
      (contextActionTermProjection view target term)).prob
        (context, (action, termValue)) =
      ((augmentedLaw view owner policy).map
        (fun assignment =>
          (fullAction view target assignment,
            termConfig view term assignment))).prob
        ((context, action), termValue) := by
  classical
  let nativeLaw := (nativeBehavioralGameForm semantics).play policy
  let unassociated := fun assignment : Assignment diagram =>
    ((Assignment.restrict diagram assignment
        (diagram.observedParents target.1), assignment target.1),
      Assignment.restrict diagram assignment (view.term term).parents)
  let associator := Equiv.prodAssoc (FullContext target)
    (diagram.Value target.1)
    (MAIDReplacementInvariantUtility.TermConfig view term)
  have hfunctions :
      contextActionTermProjection view target term =
        associator ∘ unassociated := by
    funext assignment
    rfl
  have hlaws :
      nativeLaw.map (contextActionTermProjection view target term) =
        (nativeLaw.map unassociated).map associator := by
    calc
      nativeLaw.map (contextActionTermProjection view target term) =
          nativeLaw.map (associator ∘ unassociated) :=
        congrArg (fun observable => nativeLaw.map observable) hfunctions
      _ = (nativeLaw.map unassociated).map associator :=
        (FinDist.map_comp associator unassociated nativeLaw).symm
  calc
    (nativeLaw.map (contextActionTermProjection view target term)).prob
        (context, (action, termValue)) =
        ((nativeLaw.map unassociated).map associator).prob
          (associator ((context, action), termValue)) := by
      rw [hlaws]
      simp [associator]
    _ = (nativeLaw.map unassociated).prob ((context, action), termValue) :=
      FinDist.prob_map_of_injective associator associator.injective
        (nativeLaw.map unassociated) ((context, action), termValue)
    _ = ((augmentedLaw view owner policy).map
        (fun assignment =>
          (fullAction view target assignment,
            termConfig view term assignment))).prob
          ((context, action), termValue) := by
      rw [augmented_joint_eq_native_joint view owner policy target term]

private theorem fixedPolicy_associated_prob_eq
    [Fintype Node] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    [∀ node, DecidableEq (diagram.Value node)]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (view : UtilityView semantics) (owner : Player) (policy : Policy diagram)
    (target : DecisionSite diagram owner) (removed : Finset Node)
    (hignore : view.AreGraphicallyIgnorable target removed)
    (term : view.UtilitySite owner)
    (hrelevant : view.IsRelevantUtilityTerm target term)
    (context : FullContext target) (action : diagram.Value target.1)
    (termValue : MAIDReplacementInvariantUtility.TermConfig view term) :
    (((nativeBehavioralGameForm semantics).play policy).map
      (contextActionTermProjection view target term)).prob
        (context, (action, termValue)) =
      (((nativeBehavioralGameForm semantics).play policy).map
        (fun assignment =>
          (Assignment.restrict diagram assignment
            (diagram.observedParents target.1), assignment target.1))).prob
          (context, action) *
        (continuation (augmentedLaw view owner policy)
          (fullAction view target) (termConfig view term)
          (keepFullAction target removed)
          (keepFullAction target removed (context, action))).prob termValue := by
  have hfixed := fixedPolicy_jointLaw_eq_bind_continuation topological view
    owner policy target removed hignore term hrelevant
  have hpoint := congrArg
    (fun law => law.prob ((context, action), termValue)) hfixed
  rw [bind_tagged_prob] at hpoint
  calc
    (((nativeBehavioralGameForm semantics).play policy).map
        (contextActionTermProjection view target term)).prob
          (context, (action, termValue)) =
        ((augmentedLaw view owner policy).map
          (fun assignment =>
            (fullAction view target assignment,
              termConfig view term assignment))).prob
            ((context, action), termValue) :=
      native_associated_prob_eq_augmented_joint_prob view owner policy target
        term context action termValue
    _ = ((augmentedLaw view owner policy).map
          (fullAction view target)).prob (context, action) *
        (continuation (augmentedLaw view owner policy)
          (fullAction view target) (termConfig view term)
          (keepFullAction target removed)
          (keepFullAction target removed (context, action))).prob termValue :=
      hpoint
    _ = (((nativeBehavioralGameForm semantics).play policy).map
          (fun assignment =>
            (Assignment.restrict diagram assignment
              (diagram.observedParents target.1), assignment target.1))).prob
            (context, action) *
        (continuation (augmentedLaw view owner policy)
          (fullAction view target) (termConfig view term)
          (keepFullAction target removed)
          (keepFullAction target removed (context, action))).prob termValue := by
      rw [augmented_fullAction_eq_native_contextAction view owner policy target]

/-- A graphically ignorable set gives one relevant-term continuation that is
chosen before, and works uniformly for, every owner replacement. -/
def relevantTermContinuationLawAt_of_unique_site
    (pruning : Pruning diagram)
    [DecidableEq Player] [Fintype Node] [DecidableEq Node]
    [∀ node, Fintype (diagram.Value node)]
    [∀ node, DecidableEq (diagram.Value node)]
    (semantics : Semantics diagram) (policy : pruning.ReducedPolicy)
    (owner : Player) (target : DecisionSite diagram owner)
    (hunique : ∀ site : DecisionSite diagram owner, site = target)
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (view : UtilityView semantics)
    (hignore : view.AreGraphicallyIgnorable target
      (removedObservations pruning target))
    (term : view.UtilitySite owner)
    (hrelevant : view.IsRelevantUtilityTerm target term) :
    TermContinuationLawAt pruning semantics policy owner target view
      (replacementContextLawAt_of_unique_site pruning semantics policy owner
        target hunique) term := by
  let context := replacementContextLawAt_of_unique_site pruning semantics
    policy owner target hunique
  refine {
    continuationLaw := constantActionContinuation pruning semantics policy
      owner target hunique view term
    joint_eq := ?_ }
  intro replacement
  apply FinDist.ext_of_prob
  rintro ⟨full, action, termValue⟩
  let constantOwner := constantActionOwnerPolicy target hunique action
  let constantPolicy :=
    Profile.update (sig := nativeBehavioralSignature diagram)
      (pruning.expandPolicy policy) owner constantOwner
  have hfixed := fixedPolicy_associated_prob_eq topological view owner
    constantPolicy target (removedObservations pruning target) hignore term
      hrelevant full action termValue
  have hfixedReplacement :
      ((replacementLaw pruning semantics policy owner constantOwner).map
        (contextActionTermProjection view target term)).prob
          (full, (action, termValue)) =
        ((replacementLaw pruning semantics policy owner constantOwner).map
          (fun assignment =>
            (Assignment.restrict diagram assignment
              (diagram.observedParents target.1), assignment target.1))).prob
            (full, action) *
          (continuation (augmentedLaw view owner constantPolicy)
            (fullAction view target) (termConfig view term)
            (keepFullAction target (removedObservations pruning target))
            (keepFullAction target (removedObservations pruning target)
              (full, action))).prob termValue := by
    simpa [replacementLaw, constantOwner, constantPolicy] using hfixed
  have hcontextPoint := congrArg (fun law => law.prob (full, action))
    (context.contextAction_eq constantOwner)
  rw [bind_tagged_prob] at hcontextPoint
  have hconstantContext :
      ((replacementLaw pruning semantics policy owner constantOwner).map
        (fun assignment =>
          (Assignment.restrict diagram assignment
            (diagram.observedParents target.1), assignment target.1))).prob
          (full, action) = context.contextLaw.prob full := by
    simpa [constantOwner] using hcontextPoint
  have hcontinuation :
      constantActionContinuation pruning semantics policy owner target
          hunique view term
          (Config.restrict (pruning.kept_sub_observed target.1) full) action =
        continuation (augmentedLaw view owner constantPolicy)
          (fullAction view target) (termConfig view term)
          (keepFullAction target (removedObservations pruning target))
          (keepFullAction target (removedObservations pruning target)
            (full, action)) := by
    unfold constantActionContinuation
    rw [pruningKeptAction_restrict]
  have hright := nested_bind_tagged_prob context.contextLaw
    (fun full => replacement target full)
    (fun full =>
      Config.restrict (pruning.kept_sub_observed target.1) full)
    (constantActionContinuation pruning semantics policy owner target
      hunique view term) full action termValue
  change
    ((replacementLaw pruning semantics policy owner replacement).map
      (contextActionTermProjection view target term)).prob
        (full, (action, termValue)) = _
  rw [replacementLaw_contextActionTerm_prob_eq_kernel_mul_constant pruning
    semantics policy owner target hunique view term replacement full action
      termValue]
  rw [hfixedReplacement, hconstantContext, ← hcontinuation]
  rw [hright]
  ring

end GameTheory.Experimental.PostArchitecture.MAIDRelevantUtilityContinuation
