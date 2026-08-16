/-
# Shared target context under site-local MAID replacement

Fix an owner's rules at every site except one target.  Varying only the target
rule leaves the pre-target context law unchanged, even when the owner controls
other typed decision sites.
-/

import GameTheory.Experimental.PostArchitecture.MAIDSitePolicySurgery
import GameTheory.Experimental.PostArchitecture.MAIDReplacementContext

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.MAIDSiteReplacementContext

open GameTheory
open GameTheory.Math.Probability
open GameTheory.Languages.MAID
open GameTheory.Languages.MAID.Order
open GameTheory.Languages.MAID.ToEFG
open GameTheory.Languages.MAID.Strategic
open GameTheory.Languages.MAID.FrontierEquivalence
open GameTheory.Experimental.PostArchitecture.MAIDReplacementContext
open GameTheory.Experimental.PostArchitecture.MAIDSitePolicySurgery

universe uPlayer uNode uValue

variable {Player : Type uPlayer} {Node : Type uNode}
variable {diagram : Structure Player Node}

/-- Canonical native play after holding an owner's other site rules fixed and
replacing only the target rule. -/
def siteReplacementLaw [DecidableEq Player] [Fintype Node]
    [DecidableEq Node] (semantics : Semantics diagram)
    (base : Policy diagram) (owner : Player)
    (replacement : OwnerPolicy diagram owner)
    (target : DecisionSite diagram owner)
    (rule : Config diagram (diagram.observedParents target.1) →
      FinDist (diagram.Value target.1)) : FinDist (Assignment diagram) :=
  (nativeBehavioralGameForm semantics).play
    (Profile.update (sig := nativeBehavioralSignature diagram)
      base owner (replaceSiteRule replacement target rule))

/-- One pre-target context law serves every target rule while all other rules
in the owner's replacement remain fixed. -/
structure SiteReplacementContextLawAt
    [DecidableEq Player] [Fintype Node] [DecidableEq Node]
    (semantics : Semantics diagram) (base : Policy diagram)
    (owner : Player) (replacement : OwnerPolicy diagram owner)
    (target : DecisionSite diagram owner) where
  contextLaw :
    FinDist (Config diagram (diagram.observedParents target.1))
  contextAction_eq :
    ∀ rule : Config diagram (diagram.observedParents target.1) →
        FinDist (diagram.Value target.1),
      (siteReplacementLaw semantics base owner replacement target rule).map
          (fun assignment =>
            (Assignment.restrict diagram assignment
              (diagram.observedParents target.1), assignment target.1)) =
        contextLaw.bind fun context =>
          (rule context).map fun action => (context, action)

/-- An accepted topological serialization constructs the shared context law.
Only target-rule variation is quantified; the rest of a multi-site owner
replacement is arbitrary but fixed. -/
def siteReplacementContextLawAt
    [DecidableEq Player] [Fintype Node] [DecidableEq Node]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (semantics : Semantics diagram) (base : Policy diagram)
    (owner : Player) (replacement : OwnerPolicy diagram owner)
    (target : DecisionSite diagram owner) :
    SiteReplacementContextLawAt semantics base owner replacement target := by
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
  let fixedPolicy : Policy diagram :=
    Profile.update (sig := nativeBehavioralSignature diagram)
      base owner replacement
  refine {
    contextLaw :=
      (assignmentRun semantics fixedPolicy before semantics.defaultValue).map
        (fun state => Assignment.restrict diagram state
          (diagram.observedParents target.1))
    contextAction_eq := ?_ }
  intro rule
  let surgeryPolicy : Policy diagram :=
    Profile.update (sig := nativeBehavioralSignature diagram)
      base owner (replaceSiteRule replacement target rule)
  unfold siteReplacementLaw
  rw [nativeBehavioralGameForm_play,
    map_values_nativeRun_eq_assignmentRun topological semantics surgeryPolicy,
    ← horder]
  rw [assignmentRun_contextAction_eq semantics surgeryPolicy target before
    after htargetAfter hobservedAfter]
  have hprefix :
      assignmentRun semantics surgeryPolicy before semantics.defaultValue =
        assignmentRun semantics fixedPolicy before semantics.defaultValue :=
    assignmentRun_update_replaceSiteRule_eq_of_not_mem semantics base owner
      replacement target rule before htargetBefore semantics.defaultValue
  rw [hprefix]
  simp [surgeryPolicy, fixedPolicy, replaceSiteRule_same]

namespace TwoSiteControl

open MAIDSitePolicySurgery.TwoSiteControl

def falseRule :
    Config controlDiagram (controlDiagram.observedParents bitSite.1) →
      FinDist (controlDiagram.Value bitSite.1) :=
  fun _ => FinDist.pure false

def certificate :
    SiteReplacementContextLawAt semantics base () replacement bitSite :=
  siteReplacementContextLawAt topologicalParents semantics base ()
    replacement bitSite

/-- The same context law handles the first target rule while the heterogeneous
second site remains fixed. -/
theorem true_rule_joint :
    (siteReplacementLaw semantics base () replacement bitSite trueRule).map
        (fun assignment =>
          (Assignment.restrict controlDiagram assignment
            (controlDiagram.observedParents bitSite.1),
            assignment bitSite.1)) =
      certificate.contextLaw.bind fun context =>
        (trueRule context).map fun action => (context, action) :=
  certificate.contextAction_eq trueRule

/-- The certificate is genuinely uniform over a different target rule. -/
theorem false_rule_joint :
    (siteReplacementLaw semantics base () replacement bitSite falseRule).map
        (fun assignment =>
          (Assignment.restrict controlDiagram assignment
            (controlDiagram.observedParents bitSite.1),
            assignment bitSite.1)) =
      certificate.contextLaw.bind fun context =>
        (falseRule context).map fun action => (context, action) :=
  certificate.contextAction_eq falseRule

end TwoSiteControl

end GameTheory.Experimental.PostArchitecture.MAIDSiteReplacementContext
