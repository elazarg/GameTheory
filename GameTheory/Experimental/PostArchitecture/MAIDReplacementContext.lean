/-
# EXP-105: canonical replacement-context law

This module derives the replacement-context certificate directly from the
canonical serialized MAID evaluator.  The argument uses no conditional law,
positivity assumption, or finite enumeration of node-value fibres.
-/

import GameTheory.Experimental.PostArchitecture.MAIDFactorization
import GameTheory.Experimental.PostArchitecture.MAIDReplacementInvariantUtility

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.MAIDReplacementContext

open GameTheory
open GameTheory.Math.Probability
open GameTheory.Languages.MAID
open GameTheory.Languages.MAID.Order
open GameTheory.Languages.MAID.FrontierEquivalence
open GameTheory.Languages.MAID.ObservationPruning
open GameTheory.Languages.MAID.Strategic
open GameTheory.Experimental.PostArchitecture.MAIDFactorization
open GameTheory.Experimental.PostArchitecture.MAIDReplacementInvariantUtility

universe uPlayer uNode

variable {Player : Type uPlayer} {Node : Type uNode}
variable {diagram : Structure Player Node}

/-- Serialized execution is unchanged when its node laws agree throughout the
executed list. -/
theorem assignmentRun_eq_of_nodeLaws_eq [DecidableEq Node]
    (semantics : Semantics diagram)
    (firstPolicy secondPolicy : Policy diagram) (nodes : List Node)
    (hlaws : ∀ assignment node, node ∈ nodes →
      assignmentNodeLaw semantics firstPolicy assignment node =
        assignmentNodeLaw semantics secondPolicy assignment node)
    (initial : Assignment diagram) :
    assignmentRun semantics firstPolicy nodes initial =
      assignmentRun semantics secondPolicy nodes initial := by
  induction nodes generalizing initial with
  | nil => rfl
  | cons head tail ih =>
      simp only [assignmentRun]
      unfold assignmentStep
      rw [hlaws initial head (by simp)]
      apply FinDist.bind_congr
      intro afterHead _
      apply ih
      intro assignment node hnode
      exact hlaws assignment node (by simp [hnode])

/-- A suffix omitting the target and its observations cannot alter their
joint projection on any supported execution branch. -/
private theorem map_assignmentRun_contextAction_eq_pure
    [DecidableEq Node]
    (semantics : Semantics diagram) (policy : Policy diagram)
    {owner : Player} (target : DecisionSite diagram owner)
    (nodes : List Node) (htarget : target.1 ∉ nodes)
    (hobserved : ∀ node ∈ diagram.observedParents target.1,
      node ∉ nodes)
    (initial : Assignment diagram) :
    (assignmentRun semantics policy nodes initial).map
        (fun result =>
          (Assignment.restrict diagram result
            (diagram.observedParents target.1), result target.1)) =
      FinDist.pure
        (Assignment.restrict diagram initial
          (diagram.observedParents target.1), initial target.1) := by
  apply FinDist.eq_pure_of_support_subset_singleton
  intro projected hprojected
  rw [FinDist.support_map] at hprojected
  obtain ⟨result, hresult, rfl⟩ := hprojected
  apply Set.mem_singleton_iff.mpr
  apply Prod.ext
  · funext node
    exact assignmentRun_support_preserves_of_not_mem semantics policy nodes
      initial result node.1 (hobserved node.1 node.2) hresult
  · exact assignmentRun_support_preserves_of_not_mem semantics policy nodes
      initial result target.1 htarget hresult

/-- In canonical serialized execution, the target context comes from the
prefix and the target action is drawn from exactly its policy kernel. -/
theorem assignmentRun_contextAction_eq [DecidableEq Node]
    (semantics : Semantics diagram) (policy : Policy diagram)
    {owner : Player} (target : DecisionSite diagram owner)
    (before after : List Node) (htargetAfter : target.1 ∉ after)
    (hobservedAfter : ∀ node ∈ diagram.observedParents target.1,
      node ∉ after)
    (initial : Assignment diagram) :
    (assignmentRun semantics policy
        (before ++ target.1 :: after) initial).map
        (fun result =>
          (Assignment.restrict diagram result
            (diagram.observedParents target.1), result target.1)) =
      ((assignmentRun semantics policy before initial).map
        (fun state =>
          Assignment.restrict diagram state
            (diagram.observedParents target.1))).bind fun context =>
        (policy owner target context).map fun action => (context, action) := by
  rw [assignmentRun_append, FinDist.map_bind, FinDist.bind_map]
  apply FinDist.bind_congr
  intro state _
  simp only [assignmentRun]
  unfold assignmentStep
  rw [FinDist.map_bind, FinDist.bind_map]
  have htargetLaw :
      assignmentNodeLaw semantics policy state target.1 =
        policy owner target
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
      rfl
  rw [htargetLaw]
  rw [FinDist.map_eq_bind
    (fun action =>
      (Assignment.restrict diagram state
        (diagram.observedParents target.1), action))]
  apply FinDist.bind_congr
  intro action _
  rw [map_assignmentRun_contextAction_eq_pure semantics policy target after
    htargetAfter hobservedAfter]
  apply congrArg FinDist.pure
  apply Prod.ext
  · apply restrict_setOne_of_not_mem
    intro hself
    apply diagram.acyclic target.1
    exact Relation.TransGen.single
      (diagram.observed_sub target.1 hself)
  · simp [ToEFG.Stage.Assignment.setOne, Assignment.resolve]

/-- If an owner has only the target decision site, replacing that owner's
policy cannot change execution before the target. -/
theorem assignmentRun_prefix_update_eq_of_unique_site
    [DecidableEq Player] [DecidableEq Node]
    (semantics : Semantics diagram) (base : Policy diagram)
    (owner : Player) (target : DecisionSite diagram owner)
    (hunique : ∀ site : DecisionSite diagram owner, site = target)
    (before : List Node) (htarget : target.1 ∉ before)
    (first second : OwnerPolicy diagram owner)
    (initial : Assignment diagram) :
    assignmentRun semantics
        (Profile.update (sig := nativeBehavioralSignature diagram)
          base owner first) before initial =
      assignmentRun semantics
        (Profile.update (sig := nativeBehavioralSignature diagram)
          base owner second) before initial := by
  apply assignmentRun_eq_of_nodeLaws_eq
  intro assignment node hnode
  unfold assignmentNodeLaw
  split
  · rfl
  · rename_i siteOwner hkind
    by_cases hsame : siteOwner = owner
    · subst siteOwner
      have hsite := hunique (⟨node, hkind⟩ : DecisionSite diagram owner)
      have hnodeTarget : node = target.1 := congrArg Subtype.val hsite
      subst node
      exact (htarget hnode).elim
    · rw [Profile.update_of_ne
          (sig := nativeBehavioralSignature diagram) base first hsame,
        Profile.update_of_ne
          (sig := nativeBehavioralSignature diagram) base second hsame]

/-- The canonical replacement law has one target-context distribution for all
owner replacements when that owner has exactly the target decision site. -/
def replacementContextLawAt_of_unique_site
    (pruning : Pruning diagram)
    [DecidableEq Player] [Fintype Node] [DecidableEq Node]
    (semantics : Semantics diagram) (policy : pruning.ReducedPolicy)
    (owner : Player) (target : DecisionSite diagram owner)
    (hunique : ∀ site : DecisionSite diagram owner, site = target) :
    ReplacementContextLawAt pruning semantics policy owner target := by
  let topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents :=
    (GameTheory.Math.DAG.topologicalOrder_of_acyclic diagram.acyclic).some
  let targetIndex := topological.order.idxOf target.1
  have htargetIndex : targetIndex < topological.order.length :=
    List.idxOf_lt_length_of_mem (topological.complete target.1)
  let before := topological.order.take targetIndex
  let after := topological.order.drop (targetIndex + 1)
  have htargetGet : topological.order[targetIndex] = target.1 :=
    List.getElem_idxOf htargetIndex
  have horder : before ++ target.1 :: after = topological.order := by
    unfold before after
    calc
      topological.order.take targetIndex ++
          target.1 :: topological.order.drop (targetIndex + 1) =
          (topological.order.take targetIndex ++ [target.1]) ++
            topological.order.drop (targetIndex + 1) := by simp
      _ = topological.order.take (targetIndex + 1) ++
            topological.order.drop (targetIndex + 1) := by
        rw [← htargetGet]
        rw [List.take_append_getElem htargetIndex]
      _ = topological.order := List.take_append_drop _ _
  have hnodup : (before ++ target.1 :: after).Nodup := by
    rw [horder]
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
    rw [horder]
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
  refine {
    contextLaw :=
      (assignmentRun semantics base before semantics.defaultValue).map
        (fun state => Assignment.restrict diagram state
          (diagram.observedParents target.1))
    contextAction_eq := ?_ }
  intro replacement
  unfold replacementLaw
  rw [nativeBehavioralGameForm_play,
    map_values_nativeRun_eq_assignmentRun topological semantics
      (Profile.update (sig := nativeBehavioralSignature diagram)
        base owner replacement), ← horder]
  rw [assignmentRun_contextAction_eq semantics _ target before after
    htargetAfter hobservedAfter]
  rw [assignmentRun_prefix_update_eq_of_unique_site semantics base owner
    target hunique before htargetBefore replacement (base owner)
    semantics.defaultValue]
  simp

end GameTheory.Experimental.PostArchitecture.MAIDReplacementContext
