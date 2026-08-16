/-
# Canonical MAID finite-BN factorization

This experiment connects canonical typed MAID execution to the local factor
algebra in `FiniteBNGlobalMarkov`.  It reuses `assignmentRun` and its exact
native-execution equivalence; no second evaluator is introduced.
-/

import GameTheory.Experimental.PostArchitecture.FiniteBNGlobalMarkov
import GameTheory.Experimental.PostArchitecture.MAIDRequisiteObservation
import GameTheory.Languages.MAID.Strategic

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.MAIDFactorization

open GameTheory
open GameTheory.Math.Probability
open GameTheory.Languages.MAID
open GameTheory.Languages.MAID.Order
open GameTheory.Languages.MAID.FrontierEquivalence
open GameTheory.Languages.MAID.Strategic
open GameTheory.Experimental.PostArchitecture.FiniteBNGlobalMarkov
open GameTheory.Experimental.PostArchitecture.MAIDRequisiteObservation

universe uPlayer uNode uValue

variable {Player : Type uPlayer} {Node : Type uNode}
variable {diagram : Structure Player Node}

/-- The canonical chance or decision kernel, indexed by the effective parents
used by the corresponding MAID factor. -/
def effectiveKernels (semantics : Semantics diagram) (policy : Policy diagram) :
    LocalKernels diagram.Value (effectiveParents diagram) :=
  fun node configuration => by
    match hkind : diagram.kind node with
    | .chance =>
        exact semantics.chanceLaw node hkind
          (fun parent => configuration
            ⟨parent.1, by simp [effectiveParents, hkind] at parent ⊢⟩)
    | .decision owner =>
        exact policy owner ⟨node, hkind⟩
          (fun parent => configuration
            ⟨parent.1, by simp [effectiveParents, hkind] at parent ⊢⟩)

/-- Reading an effective local kernel from a complete assignment is exactly
the node law used by canonical serialized execution. -/
theorem effectiveKernels_parentConfiguration
    (semantics : Semantics diagram) (policy : Policy diagram)
    (assignment : Assignment diagram) (node : Node) :
    effectiveKernels semantics policy node
        (parentConfiguration diagram.Value (effectiveParents diagram)
          assignment node) =
      assignmentNodeLaw semantics policy assignment node := by
  unfold effectiveKernels assignmentNodeLaw
  split <;> split
  · rename_i hfirst hsecond
    apply congrArg (semantics.chanceLaw node hfirst)
    funext parent
    rfl
  · rename_i hchance owner hdecision
    rw [hchance] at hdecision
    contradiction
  · rename_i owner hdecision hchance
    rw [hdecision] at hchance
    contradiction
  · rename_i firstOwner hfirst secondOwner hsecond
    have howner : firstOwner = secondOwner :=
      NodeKind.decision.inj (hfirst.symm.trans hsecond)
    subst secondOwner
    apply congrArg (policy firstOwner ⟨node, hfirst⟩)
    funext parent
    rfl

private theorem prob_bind_eq_mul_of_off_target_zero
    {α β : Type*} (μ : FinDist α) (continuation : α → FinDist β)
    (chosen : α) (target : β)
    (hoffTarget : ∀ value ∈ μ.support, value ≠ chosen →
      (continuation value).prob target = 0) :
    (μ.bind continuation).prob target =
      μ.prob chosen * (continuation chosen).prob target := by
  classical
  rw [FinDist.prob_bind, FinDist.expect_eq_sum_support]
  by_cases hchosen : chosen ∈ μ.support
  · rw [Finset.sum_eq_single chosen]
    · intro value hvalue hne
      rw [hoffTarget value (FinDist.mem_supportFinset.mp hvalue) hne,
        mul_zero]
    · intro hnot
      exact absurd (FinDist.mem_supportFinset.mpr hchosen) hnot
  · rw [FinDist.prob_eq_zero_iff.mpr hchosen, zero_mul]
    apply Finset.sum_eq_zero
    intro value hvalue
    have hsupport := FinDist.mem_supportFinset.mp hvalue
    have hne : value ≠ chosen := by
      intro heq
      subst value
      exact hchosen hsupport
    rw [hoffTarget value hsupport hne, mul_zero]

/-- Executing nodes other than `fixed` leaves the `fixed` coordinate unchanged
on every supported result. -/
theorem assignmentRun_support_preserves_of_not_mem [DecidableEq Node]
    (semantics : Semantics diagram) (policy : Policy diagram)
    (nodes : List Node) (assignment result : Assignment diagram)
    (fixed : Node) (hfixed : fixed ∉ nodes)
    (hresult : result ∈
      (assignmentRun semantics policy nodes assignment).support) :
    result fixed = assignment fixed := by
  induction nodes generalizing assignment result with
  | nil =>
      rw [assignmentRun, FinDist.mem_support_pure] at hresult
      subst result
      rfl
  | cons head tail ih =>
      have hhead : fixed ≠ head := by
        intro heq
        exact hfixed (by simp [heq])
      have htail : fixed ∉ tail := by
        intro hmem
        exact hfixed (by simp [hmem])
      rw [assignmentRun, FinDist.support_bind] at hresult
      simp only [Set.mem_iUnion] at hresult
      obtain ⟨afterHead, hafterHead, hresult⟩ := hresult
      unfold assignmentStep at hafterHead
      rw [FinDist.support_map] at hafterHead
      obtain ⟨value, _, rfl⟩ := hafterHead
      calc
        result fixed =
            ToEFG.Stage.Assignment.setOne assignment ⟨head, value⟩ fixed :=
          ih (ToEFG.Stage.Assignment.setOne assignment ⟨head, value⟩)
            result htail hresult
        _ = assignment fixed := by
          simp [ToEFG.Stage.Assignment.setOne,
            GameTheory.Languages.MAID.Assignment.resolve, hhead]

/-- At a fresh head node, the point mass of a serialized run splits into the
head-node mass and the point mass of the forced target branch. -/
theorem assignmentRun_cons_prob [DecidableEq Node]
    (semantics : Semantics diagram) (policy : Policy diagram)
    (head : Node) (tail : List Node) (hhead : head ∉ tail)
    (assignment target : Assignment diagram) :
    (assignmentRun semantics policy (head :: tail) assignment).prob target =
      (assignmentNodeLaw semantics policy assignment head).prob (target head) *
        (assignmentRun semantics policy tail
          (ToEFG.Stage.Assignment.setOne assignment
            ⟨head, target head⟩)).prob target := by
  rw [assignmentRun]
  unfold assignmentStep
  rw [FinDist.bind_map]
  apply prob_bind_eq_mul_of_off_target_zero
  intro value _ hne
  apply FinDist.prob_eq_zero_iff.mpr
  intro hresult
  have hcoordinate := assignmentRun_support_preserves_of_not_mem
    semantics policy tail
    (ToEFG.Stage.Assignment.setOne assignment ⟨head, value⟩)
    target head hhead hresult
  have heq : target head = value := by
    simpa [ToEFG.Stage.Assignment.setOne,
      GameTheory.Languages.MAID.Assignment.resolve] using hcoordinate
  exact hne heq.symm

theorem assignmentNodeLaw_eq_of_eq_on_effectiveParents
    (semantics : Semantics diagram) (policy : Policy diagram)
    (first second : Assignment diagram) (node : Node)
    (hagree : ∀ parent ∈ effectiveParents diagram node,
      first parent = second parent) :
    assignmentNodeLaw semantics policy first node =
      assignmentNodeLaw semantics policy second node := by
  rw [← effectiveKernels_parentConfiguration semantics policy first node,
    ← effectiveKernels_parentConfiguration semantics policy second node]
  apply congrArg (effectiveKernels semantics policy node)
  funext parent
  exact hagree parent.1 parent.2

/-- A dependency-compatible pending list factorizes when every already-resolved
coordinate agrees with the target assignment.  This is the induction invariant
behind the full topological-order result. -/
theorem assignmentRun_prob_eq_factorProduct_of_agree_outside
    [DecidableEq Node]
    (semantics : Semantics diagram) (policy : Policy diagram) :
    ∀ (nodes : List Node), nodes.Nodup →
      nodes.Pairwise
        (fun earlier later => later ∉ diagram.parents earlier) →
      ∀ (assignment target : Assignment diagram),
        (∀ node, node ∉ nodes → assignment node = target node) →
        (assignmentRun semantics policy nodes assignment).prob target =
          factorProduct diagram.Value (effectiveParents diagram)
            (effectiveKernels semantics policy) nodes.toFinset target := by
  classical
  intro nodes
  induction nodes with
  | nil =>
      intro _ _ assignment target hagree
      have heq : assignment = target := by
        funext node
        exact hagree node (by simp)
      subst assignment
      simp [assignmentRun, factorProduct]
  | cons head tail ih =>
      intro hnodup hordered assignment target hagree
      have hheadTail : head ∉ tail := (List.nodup_cons.mp hnodup).1
      have htailNodup : tail.Nodup := (List.nodup_cons.mp hnodup).2
      have hheadOrdered : ∀ later ∈ tail,
          later ∉ diagram.parents head :=
        (List.pairwise_cons.mp hordered).1
      have htailOrdered : tail.Pairwise
          (fun earlier later => later ∉ diagram.parents earlier) :=
        (List.pairwise_cons.mp hordered).2
      have hparents : ∀ parent ∈ effectiveParents diagram head,
          assignment parent = target parent := by
        intro parent hparent
        apply hagree parent
        simp only [List.mem_cons, not_or]
        constructor
        · intro heq
          subst parent
          apply diagram.acyclic head
          apply Relation.TransGen.single
          unfold effectiveParents at hparent
          split at hparent
          · exact hparent
          · exact diagram.observed_sub head hparent
        · intro htail
          apply hheadOrdered parent htail
          unfold effectiveParents at hparent
          split at hparent
          · exact hparent
          · exact diagram.observed_sub head hparent
      have hlaw : assignmentNodeLaw semantics policy assignment head =
          assignmentNodeLaw semantics policy target head :=
        assignmentNodeLaw_eq_of_eq_on_effectiveParents
          semantics policy assignment target head hparents
      have hnext : ∀ node, node ∉ tail →
          ToEFG.Stage.Assignment.setOne assignment
              ⟨head, target head⟩ node = target node := by
        intro node hnotTail
        by_cases hnode : node = head
        · subst node
          simp [ToEFG.Stage.Assignment.setOne,
            GameTheory.Languages.MAID.Assignment.resolve]
        · have houtside : assignment node = target node :=
            hagree node (by simp [hnode, hnotTail])
          simpa [ToEFG.Stage.Assignment.setOne,
            GameTheory.Languages.MAID.Assignment.resolve, hnode] using houtside
      calc
        (assignmentRun semantics policy (head :: tail) assignment).prob target =
            (assignmentNodeLaw semantics policy assignment head).prob
                (target head) *
              (assignmentRun semantics policy tail
                (ToEFG.Stage.Assignment.setOne assignment
                  ⟨head, target head⟩)).prob target :=
          assignmentRun_cons_prob semantics policy head tail hheadTail
            assignment target
        _ = (assignmentNodeLaw semantics policy target head).prob
                (target head) *
              factorProduct diagram.Value (effectiveParents diagram)
                (effectiveKernels semantics policy) tail.toFinset target := by
          rw [hlaw, ih htailNodup htailOrdered _ target hnext]
        _ = localFactor diagram.Value (effectiveParents diagram)
                (effectiveKernels semantics policy) target head *
              factorProduct diagram.Value (effectiveParents diagram)
                (effectiveKernels semantics policy) tail.toFinset target := by
          rw [localFactor,
            effectiveKernels_parentConfiguration semantics policy target head]
        _ = factorProduct diagram.Value (effectiveParents diagram)
              (effectiveKernels semantics policy) (head :: tail).toFinset target := by
          simp [factorProduct, hheadTail]

/-- Every accepted topological serialization has exactly the effective-parent
factor product as its assignment point mass. -/
theorem assignmentRun_topological_prob_eq_factorProduct
    [DecidableEq Node]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (semantics : Semantics diagram) (policy : Policy diagram)
    (initial target : Assignment diagram) :
    (assignmentRun semantics policy topological.order initial).prob target =
      factorProduct diagram.Value (effectiveParents diagram)
        (effectiveKernels semantics policy) topological.order.toFinset target := by
  apply assignmentRun_prob_eq_factorProduct_of_agree_outside
    semantics policy topological.order topological.nodup
      (topological_pairwise topological) initial target
  intro node hnot
  exact absurd (topological.complete node) hnot

/-- The order-free native evaluator has the same effective-parent factor
product.  The topological order is used only as a proof certificate. -/
theorem native_play_prob_eq_factorProduct
    [Fintype Node] [DecidableEq Node]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (semantics : Semantics diagram)
    (policy : Profile (nativeBehavioralSignature diagram))
    (target : Assignment diagram) :
    ((nativeBehavioralGameForm semantics).play policy).prob target =
      factorProduct diagram.Value (effectiveParents diagram)
        (effectiveKernels semantics policy) topological.order.toFinset target := by
  rw [nativeBehavioralGameForm_play,
    map_values_nativeRun_eq_assignmentRun topological semantics policy]
  exact assignmentRun_topological_prob_eq_factorProduct
    topological semantics policy semantics.defaultValue target

theorem topological_toFinset_eq_univ
    [Fintype Node] [DecidableEq Node]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents) :
    topological.order.toFinset = (Finset.univ : Finset Node) := by
  apply Finset.eq_univ_of_forall
  intro node
  simpa using topological.complete node

/-- Point-mass factorization in the `Finset.univ` form consumed by finite-BN
marginalization theorems. -/
theorem native_play_prob_eq_factorProduct_univ
    [Fintype Node] [DecidableEq Node]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (semantics : Semantics diagram)
    (policy : Profile (nativeBehavioralSignature diagram))
    (target : Assignment diagram) :
    ((nativeBehavioralGameForm semantics).play policy).prob target =
      factorProduct diagram.Value (effectiveParents diagram)
        (effectiveKernels semantics policy) Finset.univ target := by
  rw [← topological_toFinset_eq_univ topological]
  exact native_play_prob_eq_factorProduct topological semantics policy target

namespace ThreeNodeControl

def policy : Policy Nonrequisite.model :=
  fun _ _ _ => FinDist.pure false

def allFalse : Assignment Nonrequisite.model :=
  fun _ => false

/-- A typed signal/decision/reward MAID consumes the generic native theorem
without an auxiliary evaluator or a flattened value type. -/
theorem native_allFalse_prob_factorizes :
    ((nativeBehavioralGameForm Nonrequisite.semantics).play policy).prob
        allFalse =
      factorProduct Nonrequisite.model.Value
        (effectiveParents Nonrequisite.model)
        (effectiveKernels Nonrequisite.semantics policy)
        Finset.univ allFalse :=
  native_play_prob_eq_factorProduct_univ Nonrequisite.topologicalParents
    Nonrequisite.semantics policy allFalse

end ThreeNodeControl

end GameTheory.Experimental.PostArchitecture.MAIDFactorization
