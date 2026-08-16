/-
# EXP-105: canonical target-node surgery

This module isolates one target decision in canonical serialized MAID
execution.  The resulting point-mass identity uses neither conditioning nor
division, so it applies unchanged at unsupported contexts.
-/

import GameTheory.Experimental.PostArchitecture.MAIDReplacementContext

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.MAIDTargetSurgery

open GameTheory
open GameTheory.Math.Probability
open GameTheory.Languages.MAID
open GameTheory.Languages.MAID.Order
open GameTheory.Languages.MAID.FrontierEquivalence
open GameTheory.Languages.MAID.ObservationPruning
open GameTheory.Languages.MAID.Strategic
open GameTheory.Experimental.PostArchitecture.MAIDFactorization
open GameTheory.Experimental.PostArchitecture.MAIDReplacementContext
open GameTheory.Experimental.PostArchitecture.MAIDReplacementInvariantUtility
open GameTheory.Experimental.PostArchitecture.MAIDRequisiteObservation

universe uPlayer uNode

variable {Player : Type uPlayer} {Node : Type uNode}
variable {diagram : Structure Player Node}
variable {semantics : Semantics diagram}

/-- When an owner has one decision site, this owner policy chooses the supplied
target action at every context. -/
def constantActionOwnerPolicy {owner : Player}
    (target : DecisionSite diagram owner)
    (hunique : ∀ site : DecisionSite diagram owner, site = target)
    (action : diagram.Value target.1) : OwnerPolicy diagram owner :=
  fun site _ => by
    have hsite := hunique site
    subst site
    exact FinDist.pure action

@[simp]
theorem constantActionOwnerPolicy_apply {owner : Player}
    (target : DecisionSite diagram owner)
    (hunique : ∀ site : DecisionSite diagram owner, site = target)
    (action : diagram.Value target.1) (context : FullContext target) :
    constantActionOwnerPolicy target hunique action target context =
      FinDist.pure action := by
  rfl

/-- Replacing the unique target owner changes only the target draw: the prefix
and every action-indexed suffix are those of the unchanged base policy. -/
theorem assignmentRun_target_surgery_eq
    [DecidableEq Player] [DecidableEq Node]
    (semantics : Semantics diagram) (base : Policy diagram)
    (owner : Player) (target : DecisionSite diagram owner)
    (hunique : ∀ site : DecisionSite diagram owner, site = target)
    (before after : List Node) (htargetBefore : target.1 ∉ before)
    (htargetAfter : target.1 ∉ after)
    (replacement : OwnerPolicy diagram owner)
    (initial : Assignment diagram) :
    assignmentRun semantics
        (Profile.update (sig := nativeBehavioralSignature diagram)
          base owner replacement)
        (before ++ target.1 :: after) initial =
      (assignmentRun semantics base before initial).bind fun state =>
        (replacement target
          (Assignment.restrict diagram state
            (diagram.observedParents target.1))).bind fun action =>
          assignmentRun semantics base after
            (ToEFG.Stage.Assignment.setOne state ⟨target.1, action⟩) := by
  rw [assignmentRun_append]
  rw [assignmentRun_prefix_update_eq_of_unique_site semantics base owner
    target hunique before htargetBefore replacement (base owner) initial]
  rw [Profile.update_eq_self
    (sig := nativeBehavioralSignature diagram) base owner]
  apply FinDist.bind_congr
  intro state _
  simp only [assignmentRun]
  unfold assignmentStep
  rw [FinDist.bind_map]
  have htargetLaw :
      assignmentNodeLaw semantics
          (Profile.update (sig := nativeBehavioralSignature diagram)
            base owner replacement)
          state target.1 =
        replacement target
          (Assignment.restrict diagram state
            (diagram.observedParents target.1)) := by
    unfold assignmentNodeLaw
    split
    · rename_i hchance
      rw [target.2] at hchance
      contradiction
    · rename_i siteOwner hdecision
      have howner : siteOwner = owner :=
        NodeKind.decision.inj (hdecision.symm.trans target.2)
      subst siteOwner
      simp only [Profile.update_same]
      have hsite :
          (⟨target.1, hdecision⟩ : DecisionSite diagram owner) = target :=
        Subtype.ext (by rfl)
      cases hsite
      rfl
  rw [htargetLaw]
  apply FinDist.bind_congr
  intro action _
  calc
    assignmentRun semantics
        (Profile.update (sig := nativeBehavioralSignature diagram)
          base owner replacement) after
        (ToEFG.Stage.Assignment.setOne state ⟨target.1, action⟩) =
      assignmentRun semantics
        (Profile.update (sig := nativeBehavioralSignature diagram)
          base owner (base owner)) after
        (ToEFG.Stage.Assignment.setOne state ⟨target.1, action⟩) :=
      assignmentRun_prefix_update_eq_of_unique_site semantics base owner
        target hunique after htargetAfter replacement (base owner)
          (ToEFG.Stage.Assignment.setOne state ⟨target.1, action⟩)
    _ = assignmentRun semantics base after
          (ToEFG.Stage.Assignment.setOne state ⟨target.1, action⟩) := by
      rw [Profile.update_eq_self
        (sig := nativeBehavioralSignature diagram) base owner]

/-- The context, target action, and one arbitrary utility-term configuration
read from a complete assignment. -/
def contextActionTermProjection (view : UtilityView semantics)
    {targetOwner termOwner : Player}
    (target : DecisionSite diagram targetOwner)
    (term : view.UtilitySite termOwner) (assignment : Assignment diagram) :
    FullContext target × (diagram.Value target.1 × TermConfig view term) :=
  (Assignment.restrict diagram assignment
      (diagram.observedParents target.1),
    (assignment target.1,
      Assignment.restrict diagram assignment (view.term term).parents))

private theorem prob_bind_eq_chosen_mul
    {Action Output : Type*} (law : FinDist Action)
    (continuation : Action → FinDist Output)
    (chosen : Action) (output : Output)
    (hoffTarget : ∀ action ∈ law.support, action ≠ chosen →
      (continuation action).prob output = 0) :
    (law.bind continuation).prob output =
      law.prob chosen * (continuation chosen).prob output := by
  classical
  rw [FinDist.prob_bind, FinDist.expect_eq_sum_support]
  by_cases hchosen : chosen ∈ law.support
  · rw [Finset.sum_eq_single chosen]
    · intro action haction hne
      rw [hoffTarget action (FinDist.mem_supportFinset.mp haction) hne,
        mul_zero]
    · intro hnot
      exact absurd (FinDist.mem_supportFinset.mpr hchosen) hnot
  · rw [FinDist.prob_eq_zero_iff.mpr hchosen, zero_mul]
    apply Finset.sum_eq_zero
    intro action haction
    have hsupport := FinDist.mem_supportFinset.mp haction
    have hne : action ≠ chosen := by
      intro heq
      subst action
      exact hchosen hsupport
    rw [hoffTarget action hsupport hne, mul_zero]

private theorem suffix_prob_eq_zero_of_action_ne
    [DecidableEq Node]
    (semantics : Semantics diagram) (base : Policy diagram)
    {owner termOwner : Player} (target : DecisionSite diagram owner)
    (view : UtilityView semantics) (term : view.UtilitySite termOwner)
    (after : List Node) (htargetAfter : target.1 ∉ after)
    (state : Assignment diagram) (chosen queried : diagram.Value target.1)
    (context : FullContext target) (termConfig : TermConfig view term)
    (hne : chosen ≠ queried) :
    ((assignmentRun semantics base after
        (ToEFG.Stage.Assignment.setOne state ⟨target.1, chosen⟩)).map
      (contextActionTermProjection view target term)).prob
        (context, (queried, termConfig)) = 0 := by
  apply FinDist.prob_eq_zero_iff.mpr
  intro houtput
  rw [FinDist.support_map] at houtput
  obtain ⟨result, hresult, hprojection⟩ := houtput
  have hpreserved := assignmentRun_support_preserves_of_not_mem
    semantics base after
    (ToEFG.Stage.Assignment.setOne state ⟨target.1, chosen⟩)
    result target.1 htargetAfter hresult
  have hchosen : result target.1 = chosen := by
    simpa [ToEFG.Stage.Assignment.setOne, Assignment.resolve] using hpreserved
  have hqueried : result target.1 = queried :=
    congrArg (fun output => output.2.1) hprojection
  exact hne (hchosen.symm.trans hqueried)

private theorem suffix_prob_eq_zero_of_context_ne
    [DecidableEq Node]
    (semantics : Semantics diagram) (base : Policy diagram)
    {owner termOwner : Player} (target : DecisionSite diagram owner)
    (view : UtilityView semantics) (term : view.UtilitySite termOwner)
    (after : List Node)
    (hobservedAfter : ∀ node ∈ diagram.observedParents target.1,
      node ∉ after)
    (state : Assignment diagram) (chosen queried : diagram.Value target.1)
    (context : FullContext target) (termConfig : TermConfig view term)
    (hne : Assignment.restrict diagram state
      (diagram.observedParents target.1) ≠ context) :
    ((assignmentRun semantics base after
        (ToEFG.Stage.Assignment.setOne state ⟨target.1, chosen⟩)).map
      (contextActionTermProjection view target term)).prob
        (context, (queried, termConfig)) = 0 := by
  apply FinDist.prob_eq_zero_iff.mpr
  intro houtput
  rw [FinDist.support_map] at houtput
  obtain ⟨result, hresult, hprojection⟩ := houtput
  have hsuffix :
      Assignment.restrict diagram result
          (diagram.observedParents target.1) =
        Assignment.restrict diagram
          (ToEFG.Stage.Assignment.setOne state ⟨target.1, chosen⟩)
          (diagram.observedParents target.1) := by
    funext node
    exact assignmentRun_support_preserves_of_not_mem semantics base after
      (ToEFG.Stage.Assignment.setOne state ⟨target.1, chosen⟩)
      result node.1 (hobservedAfter node.1 node.2) hresult
  have htargetNotObserved :
      target.1 ∉ diagram.observedParents target.1 := by
    intro hself
    apply diagram.acyclic target.1
    exact Relation.TransGen.single (diagram.observed_sub target.1 hself)
  have hset := restrict_setOne_of_not_mem state
    (diagram.observedParents target.1) chosen htargetNotObserved
  have hresultContext :
      Assignment.restrict diagram state
          (diagram.observedParents target.1) =
        Assignment.restrict diagram result
          (diagram.observedParents target.1) :=
    hset.symm.trans hsuffix.symm
  have hprojected :
      Assignment.restrict diagram result
          (diagram.observedParents target.1) = context :=
    congrArg Prod.fst hprojection
  exact hne (hresultContext.trans hprojected)

/-- At an exact context/action/term point, an arbitrary target rule contributes
only its mass on that action.  The remaining mass is the canonical law under
the constant-action target rule, including at zero-mass contexts. -/
theorem replacementLaw_contextActionTerm_prob_eq_kernel_mul_constant
    (pruning : Pruning diagram)
    [DecidableEq Player] [Fintype Node] [DecidableEq Node]
    (semantics : Semantics diagram) (policy : pruning.ReducedPolicy)
    (owner : Player) (target : DecisionSite diagram owner)
    (hunique : ∀ site : DecisionSite diagram owner, site = target)
    (view : UtilityView semantics) {termOwner : Player}
    (term : view.UtilitySite termOwner)
    (replacement : OwnerPolicy diagram owner)
    (context : FullContext target) (action : diagram.Value target.1)
    (termConfig : TermConfig view term) :
    ((replacementLaw pruning semantics policy owner replacement).map
      (contextActionTermProjection view target term)).prob
        (context, (action, termConfig)) =
      (replacement target context).prob action *
        ((replacementLaw pruning semantics policy owner
          (constantActionOwnerPolicy target hunique action)).map
            (contextActionTermProjection view target term)).prob
          (context, (action, termConfig)) := by
  let topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents :=
    (GameTheory.Math.DAG.topologicalOrder_of_acyclic diagram.acyclic).some
  obtain ⟨before, after, horder⟩ :=
    List.mem_iff_append.mp (topological.complete target.1)
  have hnodup : (before ++ target.1 :: after).Nodup := by
    rw [← horder]
    exact topological.nodup
  have htargetBefore : target.1 ∉ before := by
    intro htarget
    exact (List.nodup_append.mp hnodup).2.2 target.1 htarget
      target.1 (by simp) rfl
  have htargetAfter : target.1 ∉ after :=
    (List.nodup_cons.mp (List.nodup_append.mp hnodup).2.1).1
  have hordered :
      (before ++ target.1 :: after).Pairwise
        (fun earlier later => later ∉ diagram.parents earlier) := by
    rw [← horder]
    exact topological_pairwise topological
  have htargetOrder : ∀ node ∈ after,
      node ∉ diagram.parents target.1 :=
    (List.pairwise_cons.mp
      (List.pairwise_append.mp hordered).2.1).1
  have hobservedAfter : ∀ node ∈ diagram.observedParents target.1,
      node ∉ after := by
    intro node hobserved hafter
    exact htargetOrder node hafter
      (diagram.observed_sub target.1 hobserved)
  let base := pruning.expandPolicy policy
  have hreplacement :
      (replacementLaw pruning semantics policy owner replacement).map
          (contextActionTermProjection view target term) =
        (assignmentRun semantics base before semantics.defaultValue).bind
          fun state =>
            (replacement target
              (Assignment.restrict diagram state
                (diagram.observedParents target.1))).bind fun chosen =>
              (assignmentRun semantics base after
                (ToEFG.Stage.Assignment.setOne state
                  ⟨target.1, chosen⟩)).map
                (contextActionTermProjection view target term) := by
    unfold replacementLaw
    rw [nativeBehavioralGameForm_play,
      map_values_nativeRun_eq_assignmentRun topological semantics
        (Profile.update (sig := nativeBehavioralSignature diagram)
          base owner replacement), horder]
    rw [assignmentRun_target_surgery_eq semantics base owner target hunique
      before after htargetBefore htargetAfter replacement]
    simp only [FinDist.map_bind]
  have hconstant :
      (replacementLaw pruning semantics policy owner
          (constantActionOwnerPolicy target hunique action)).map
          (contextActionTermProjection view target term) =
        (assignmentRun semantics base before semantics.defaultValue).bind
          fun state =>
            (assignmentRun semantics base after
              (ToEFG.Stage.Assignment.setOne state
                ⟨target.1, action⟩)).map
              (contextActionTermProjection view target term) := by
    unfold replacementLaw
    rw [nativeBehavioralGameForm_play,
      map_values_nativeRun_eq_assignmentRun topological semantics
        (Profile.update (sig := nativeBehavioralSignature diagram) base owner
          (constantActionOwnerPolicy target hunique action)), horder]
    rw [assignmentRun_target_surgery_eq semantics base owner target hunique
      before after htargetBefore htargetAfter
        (constantActionOwnerPolicy target hunique action)]
    simp only [FinDist.map_bind, constantActionOwnerPolicy_apply,
      FinDist.pure_bind]
  rw [hreplacement, hconstant]
  rw [FinDist.prob_bind]
  rw [FinDist.prob_bind
    (assignmentRun semantics base before semantics.defaultValue)]
  rw [← FinDist.expect_smul]
  apply FinDist.expect_congr
  intro state _
  by_cases hcontext : Assignment.restrict diagram state
      (diagram.observedParents target.1) = context
  · have hfactor := prob_bind_eq_chosen_mul
      (replacement target
        (Assignment.restrict diagram state
          (diagram.observedParents target.1)))
      (fun chosen =>
        (assignmentRun semantics base after
          (ToEFG.Stage.Assignment.setOne state ⟨target.1, chosen⟩)).map
            (contextActionTermProjection view target term))
      action (context, (action, termConfig)) (by
        intro chosen _ hne
        exact suffix_prob_eq_zero_of_action_ne semantics base target view term
          after htargetAfter state chosen action context termConfig hne)
    simpa only [hcontext] using hfactor
  · have hconstantZero := suffix_prob_eq_zero_of_context_ne semantics base
      target view term after hobservedAfter state action action context
      termConfig hcontext
    have harbitraryZero :
        ((replacement target
          (Assignment.restrict diagram state
            (diagram.observedParents target.1))).bind fun chosen =>
            (assignmentRun semantics base after
              (ToEFG.Stage.Assignment.setOne state
                ⟨target.1, chosen⟩)).map
              (contextActionTermProjection view target term)).prob
            (context, (action, termConfig)) = 0 := by
      rw [FinDist.prob_bind]
      have hbranches :
          (fun chosen =>
            ((assignmentRun semantics base after
              (ToEFG.Stage.Assignment.setOne state
                ⟨target.1, chosen⟩)).map
              (contextActionTermProjection view target term)).prob
                (context, (action, termConfig))) = fun _ => 0 := by
        funext chosen
        exact suffix_prob_eq_zero_of_context_ne semantics base target view
          term after hobservedAfter state chosen action context termConfig
            hcontext
      rw [hbranches, FinDist.expect_const]
    rw [harbitraryZero, hconstantZero, mul_zero]

end GameTheory.Experimental.PostArchitecture.MAIDTargetSurgery
