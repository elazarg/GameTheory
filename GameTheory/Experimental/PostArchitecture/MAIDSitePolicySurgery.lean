/-
# Site-local policy surgery for typed MAIDs

This module changes one rule inside an owner's dependent family while keeping
every other site rule fixed.  The canonical MAID node law and serialized runner
remain the only execution semantics.
-/

import GameTheory.Languages.MAID.Strategic

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.MAIDSitePolicySurgery

open GameTheory
open GameTheory.Math.Probability
open GameTheory.Languages.MAID
open GameTheory.Languages.MAID.Order
open GameTheory.Languages.MAID.ToEFG
open GameTheory.Languages.MAID.Strategic
open GameTheory.Languages.MAID.FrontierEquivalence

universe uPlayer uNode uValue

variable {Player : Type uPlayer} {Node : Type uNode}
variable {diagram : Structure Player Node}

/-- Replace exactly one site rule inside an owner's complete dependent policy
family. -/
def replaceSiteRule [DecidableEq Node] {owner : Player}
    (policy : OwnerPolicy diagram owner)
    (target : DecisionSite diagram owner)
    (rule : Config diagram (diagram.observedParents target.1) →
      FinDist (diagram.Value target.1)) :
    OwnerPolicy diagram owner :=
  fun site => by
    by_cases hsite : site = target
    · subst site
      exact rule
    · exact policy site

@[simp]
theorem replaceSiteRule_same [DecidableEq Node] {owner : Player}
    (policy : OwnerPolicy diagram owner)
    (target : DecisionSite diagram owner)
    (rule : Config diagram (diagram.observedParents target.1) →
      FinDist (diagram.Value target.1)) :
    replaceSiteRule policy target rule target = rule := by
  simp [replaceSiteRule]

theorem replaceSiteRule_of_ne [DecidableEq Node] {owner : Player}
    (policy : OwnerPolicy diagram owner)
    (target site : DecisionSite diagram owner)
    (rule : Config diagram (diagram.observedParents target.1) →
      FinDist (diagram.Value target.1)) (hne : site ≠ target) :
    replaceSiteRule policy target rule site = policy site := by
  simp [replaceSiteRule, hne]

@[simp]
theorem replaceSiteRule_self [DecidableEq Node] {owner : Player}
    (policy : OwnerPolicy diagram owner)
    (target : DecisionSite diagram owner) :
    replaceSiteRule policy target (policy target) = policy := by
  funext site
  by_cases hsite : site = target
  · subst site
    exact replaceSiteRule_same policy target (policy target)
  · exact replaceSiteRule_of_ne policy target site (policy target) hsite

/-- At the replaced decision node, the canonical node law is exactly the new
rule applied to the assignment's declared observation context. -/
theorem assignmentNodeLaw_update_replaceSiteRule_target
    [DecidableEq Player] [DecidableEq Node]
    (semantics : Semantics diagram) (base : Policy diagram)
    (owner : Player) (replacement : OwnerPolicy diagram owner)
    (target : DecisionSite diagram owner)
    (rule : Config diagram (diagram.observedParents target.1) →
      FinDist (diagram.Value target.1)) (assignment : Assignment diagram) :
    assignmentNodeLaw semantics
        (Profile.update (sig := nativeBehavioralSignature diagram)
          base owner (replaceSiteRule replacement target rule))
        assignment target.1 =
      rule (Assignment.restrict diagram assignment
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
    simp [replaceSiteRule, hsite]

/-- Away from the target node, site surgery leaves the canonical node law
unchanged, including at other decision sites of the same owner. -/
theorem assignmentNodeLaw_update_replaceSiteRule_of_ne
    [DecidableEq Player] [DecidableEq Node]
    (semantics : Semantics diagram) (base : Policy diagram)
    (owner : Player) (replacement : OwnerPolicy diagram owner)
    (target : DecisionSite diagram owner)
    (rule : Config diagram (diagram.observedParents target.1) →
      FinDist (diagram.Value target.1)) (assignment : Assignment diagram)
    (node : Node) (hne : node ≠ target.1) :
    assignmentNodeLaw semantics
        (Profile.update (sig := nativeBehavioralSignature diagram)
          base owner (replaceSiteRule replacement target rule))
        assignment node =
      assignmentNodeLaw semantics
        (Profile.update (sig := nativeBehavioralSignature diagram)
          base owner replacement) assignment node := by
  unfold assignmentNodeLaw
  split
  · rfl
  · rename_i siteOwner hdecision
    by_cases howner : siteOwner = owner
    · subst siteOwner
      simp only [Profile.update_same]
      apply congrFun
      apply replaceSiteRule_of_ne
      intro hsite
      exact hne (congrArg Subtype.val hsite)
    · rw [Profile.update_of_ne
          (sig := nativeBehavioralSignature diagram) base _ howner,
        Profile.update_of_ne
          (sig := nativeBehavioralSignature diagram) base replacement howner]

/-- Serialized execution on a list omitting the target is invariant under
site surgery. -/
theorem assignmentRun_update_replaceSiteRule_eq_of_not_mem
    [DecidableEq Player] [DecidableEq Node]
    (semantics : Semantics diagram) (base : Policy diagram)
    (owner : Player) (replacement : OwnerPolicy diagram owner)
    (target : DecisionSite diagram owner)
    (rule : Config diagram (diagram.observedParents target.1) →
      FinDist (diagram.Value target.1)) (nodes : List Node)
    (htarget : target.1 ∉ nodes) (initial : Assignment diagram) :
    assignmentRun semantics
        (Profile.update (sig := nativeBehavioralSignature diagram)
          base owner (replaceSiteRule replacement target rule))
        nodes initial =
      assignmentRun semantics
        (Profile.update (sig := nativeBehavioralSignature diagram)
          base owner replacement) nodes initial := by
  induction nodes generalizing initial with
  | nil => rfl
  | cons head tail ih =>
      simp only [assignmentRun]
      unfold assignmentStep
      have hhead : head ≠ target.1 := by
        intro heq
        subst head
        exact htarget (by simp)
      rw [assignmentNodeLaw_update_replaceSiteRule_of_ne semantics base owner
        replacement target rule initial head hhead]
      apply FinDist.bind_congr
      intro afterHead _
      apply ih
      intro htargetTail
      exact htarget (by simp [htargetTail])

/-- Exact multi-site target surgery: the prefix and suffix use the fixed whole
owner replacement, while the target draw alone uses the supplied new rule. -/
theorem assignmentRun_site_surgery_eq
    [DecidableEq Player] [DecidableEq Node]
    (semantics : Semantics diagram) (base : Policy diagram)
    (owner : Player) (replacement : OwnerPolicy diagram owner)
    (target : DecisionSite diagram owner)
    (rule : Config diagram (diagram.observedParents target.1) →
      FinDist (diagram.Value target.1))
    (before after : List Node) (htargetBefore : target.1 ∉ before)
    (htargetAfter : target.1 ∉ after) (initial : Assignment diagram) :
    assignmentRun semantics
        (Profile.update (sig := nativeBehavioralSignature diagram)
          base owner (replaceSiteRule replacement target rule))
        (before ++ target.1 :: after) initial =
      (assignmentRun semantics
        (Profile.update (sig := nativeBehavioralSignature diagram)
          base owner replacement) before initial).bind fun state =>
        (rule (Assignment.restrict diagram state
          (diagram.observedParents target.1))).bind fun action =>
          assignmentRun semantics
            (Profile.update (sig := nativeBehavioralSignature diagram)
              base owner replacement) after
            (Stage.Assignment.setOne state ⟨target.1, action⟩) := by
  rw [assignmentRun_append]
  rw [assignmentRun_update_replaceSiteRule_eq_of_not_mem semantics base owner
    replacement target rule before htargetBefore initial]
  apply FinDist.bind_congr
  intro state _
  simp only [assignmentRun]
  unfold assignmentStep
  rw [FinDist.bind_map]
  rw [assignmentNodeLaw_update_replaceSiteRule_target semantics base owner
    replacement target rule state]
  apply FinDist.bind_congr
  intro action _
  exact assignmentRun_update_replaceSiteRule_eq_of_not_mem semantics base owner
    replacement target rule after htargetAfter
      (Stage.Assignment.setOne state ⟨target.1, action⟩)

namespace TwoSiteControl

inductive ControlNode
  | bit
  | tri
  deriving DecidableEq, Fintype

def parents (_ : ControlNode) : Finset ControlNode := ∅

def topologicalParents : GameTheory.Math.DAG.TopologicalOrder parents where
  order := [.bit, .tri]
  nodup := by decide
  complete node := by cases node <;> simp
  respects := by
    intro _ _ hparent
    simp [parents] at hparent

def kind (_ : ControlNode) : NodeKind Unit := .decision ()

@[reducible]
def controlDiagram : Structure Unit ControlNode where
  kind := kind
  parents := parents
  observedParents := parents
  Value
    | .bit => Bool
    | .tri => Fin 3
  observed_sub _ _ hmember := hmember
  observed_eq_of_chance _ hchance := by
    simp [kind] at hchance
  acyclic := GameTheory.Math.DAG.acyclic_of_topologicalOrder
    topologicalParents

def bitSite : DecisionSite controlDiagram () := ⟨.bit, rfl⟩

def triSite : DecisionSite controlDiagram () := ⟨.tri, rfl⟩

def replacement : OwnerPolicy controlDiagram () :=
  fun site _ => by
    rcases site with ⟨node, _⟩
    cases node with
    | bit => exact FinDist.pure false
    | tri => exact FinDist.pure 0

def trueRule :
    Config controlDiagram (controlDiagram.observedParents bitSite.1) →
      FinDist (controlDiagram.Value bitSite.1) :=
  fun _ => FinDist.pure true

theorem target_rule_replaced
    (context : Config controlDiagram
      (controlDiagram.observedParents bitSite.1)) :
    replaceSiteRule replacement bitSite trueRule bitSite context =
      FinDist.pure true := by
  rw [replaceSiteRule_same]
  rfl

theorem heterogeneous_other_rule_preserved
    (context : Config controlDiagram
      (controlDiagram.observedParents triSite.1)) :
    replaceSiteRule replacement bitSite trueRule triSite context =
      FinDist.pure (0 : Fin 3) := by
  rw [replaceSiteRule_of_ne replacement bitSite triSite trueRule (by
    intro hsite
    cases congrArg Subtype.val hsite)]
  rfl

def defaultValue : (node : ControlNode) → controlDiagram.Value node
  | .bit => false
  | .tri => 0

def semantics : Semantics controlDiagram where
  defaultValue := defaultValue
  chanceLaw _ hchance := by
    simp [kind] at hchance
  utility _ _ := 0

def base : Policy controlDiagram := fun _ => replacement

/-- The `Fin 3` site executes identically when the distinct `Bool` site is
surgically replaced. -/
theorem heterogeneous_other_run_preserved
    (initial : Assignment controlDiagram) :
    assignmentRun semantics
        (Profile.update (sig := nativeBehavioralSignature controlDiagram)
          base () (replaceSiteRule replacement bitSite trueRule))
        [.tri] initial =
      assignmentRun semantics
        (Profile.update (sig := nativeBehavioralSignature controlDiagram)
          base () replacement) [.tri] initial :=
  assignmentRun_update_replaceSiteRule_eq_of_not_mem semantics base ()
    replacement bitSite trueRule [.tri] (by simp [bitSite]) initial

end TwoSiteControl

end GameTheory.Experimental.PostArchitecture.MAIDSitePolicySurgery
