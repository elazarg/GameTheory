/-
# EXP-041: serialized/native typed MAID equivalence

The last serialization gate compares a dependent finite product over a native
frontier with sequential draws of the same node laws. This file keeps that
probability algebra separate from both evaluators.
-/

import GameTheory.Experimental.PostArchitecture.TypedMAIDOrder

noncomputable section

namespace GameTheory.Experimental.TypedMAID.FrontierEquivalence

open GameTheory.Probability
open GameTheory.Experimental.TypedMAID.ToEFG
open GameTheory.Experimental.TypedMAID.Order

universe uPlayer uNode uValue uIndex

variable {Player : Type uPlayer} {Node : Type uNode}
variable {diagram : TypedMAID.Structure Player Node}

/-- A dependent finite product is invariant under reindexing its coordinates
by an equivalence. -/
theorem finDist_pi_reindex
    {ι κ : Type uIndex} [Fintype ι] [Fintype κ]
    (A : ι → Type uValue) (equiv : κ ≃ ι)
    (laws : (i : ι) → FinDist (A i)) :
    FinDist.map (Equiv.piCongrLeft A equiv).symm
        (FinDist.pi laws) =
      FinDist.pi (fun k => laws (equiv k)) := by
  classical
  apply FinDist.ext_of_prob
  intro target
  let functionEquiv := Equiv.piCongrLeft A equiv
  have htarget :
      target = functionEquiv.symm (functionEquiv target) :=
    (functionEquiv.symm_apply_apply target).symm
  conv_lhs => rw [htarget]
  rw [FinDist.prob_map_of_injective functionEquiv.symm
      functionEquiv.symm.injective,
    FinDist.prob_pi, FinDist.prob_pi,
    ← equiv.prod_comp
      (g := fun i => (laws i).prob (functionEquiv target i))]
  apply Finset.prod_congr rfl
  intro k _
  simp [functionEquiv]

/-- Sequentially draw a fixed node-law family and replace each listed
coordinate. -/
def fixedAssignmentRun [DecidableEq Node]
    (laws : (node : Node) → FinDist (diagram.Value node)) :
    List Node → TypedMAID.Assignment diagram →
      FinDist (TypedMAID.Assignment diagram)
  | [], assignment => FinDist.pure assignment
  | node :: rest, assignment =>
      (laws node).bind fun value =>
        fixedAssignmentRun laws rest
          (Stage.Assignment.setOne assignment ⟨node, value⟩)

/-- Drawing a duplicate-free node list sequentially is the same law as drawing
the corresponding dependent product and resolving all listed coordinates at
once. -/
theorem fixedAssignmentRun_eq_pi [DecidableEq Node]
    (laws : (node : Node) → FinDist (diagram.Value node)) :
    ∀ (nodes : List Node), nodes.Nodup →
      ∀ assignment : TypedMAID.Assignment diagram,
        fixedAssignmentRun laws nodes assignment =
          FinDist.map
            (TypedMAID.Assignment.resolve diagram assignment
              nodes.toFinset)
            (FinDist.pi fun node : {node // node ∈ nodes.toFinset} =>
              laws node.1) := by
  intro nodes
  induction nodes with
  | nil =>
      intro _ assignment
      let emptyDraw :
          (node : {node : Node //
            node ∈ ([] : List Node).toFinset}) →
            diagram.Value node.1 :=
        fun node => by
          exfalso
          have hmem := node.2
          exact List.not_mem_nil (List.mem_toFinset.mp hmem)
      have hlaws :
          (fun node :
              {node : Node // node ∈ ([] : List Node).toFinset} =>
            laws node.1) =
            fun node => FinDist.pure (emptyDraw node) := by
        funext node
        exfalso
        have hmem := node.2
        exact List.not_mem_nil (List.mem_toFinset.mp hmem)
      rw [fixedAssignmentRun, hlaws, FinDist.pi_pure,
        FinDist.map_pure]
      apply congrArg FinDist.pure
      funext node
      simp [TypedMAID.Assignment.resolve]
  | cons head tail ih =>
      intro hnodup assignment
      have hheadNotMem : head ∉ tail :=
        (List.nodup_cons.mp hnodup).1
      have htailNodup : tail.Nodup :=
        (List.nodup_cons.mp hnodup).2
      have hheadNotFinset : head ∉ tail.toFinset := by
        simpa using hheadNotMem
      let full := {node : Node // node ∈ (head :: tail).toFinset}
      let headIndex : full := ⟨head, by simp⟩
      let remaining := {node : full // node ≠ headIndex}
      let tailIndex := {node : Node // node ∈ tail.toFinset}
      let remainingEquiv : tailIndex ≃ remaining :=
        { toFun := fun node => ⟨⟨node.1, by simp [node.2]⟩, by
          intro heq
          have hnodeValue :
              node.1 = head := by
            simpa [headIndex] using
              congrArg (fun value : full => value.1) heq
          have hheadFinset : head ∈ tail.toFinset := by
            rw [← hnodeValue]
            exact node.2
          exact hheadNotMem (by simpa using hheadFinset)⟩
          invFun := fun node => ⟨node.1.1, by
            have hmem : node.1.1 = head ∨
                node.1.1 ∈ tail.toFinset := by
              simpa using node.1.2
            rcases hmem with hhead | htail
            · exfalso
              apply node.2
              apply Subtype.ext
              exact hhead
            · exact htail⟩
          left_inv := fun node => by
            apply Subtype.ext
            rfl
          right_inv := fun node => by
            apply Subtype.ext
            rfl }
      let remainingValue (node : remaining) :=
        diagram.Value node.1.1
      let remainingLaws (node : remaining) :
          FinDist (remainingValue node) :=
        laws node.1.1
      have hreindex :
          FinDist.map
              (Equiv.piCongrLeft remainingValue remainingEquiv).symm
              (FinDist.pi remainingLaws) =
            FinDist.pi
              (fun node : tailIndex => laws node.1) := by
        simpa [remainingEquiv, remainingValue, remainingLaws,
          tailIndex] using
          finDist_pi_reindex remainingValue remainingEquiv
            remainingLaws
      have hresolve
          (value : diagram.Value head) :
          FinDist.map
              (fun draw : (node : remaining) →
                  remainingValue node =>
                TypedMAID.Assignment.resolve diagram assignment
                  (head :: tail).toFinset
                  ((Equiv.piSplitAt headIndex
                    (fun node : full =>
                      diagram.Value node.1)).symm
                    (value, draw)))
              (FinDist.pi remainingLaws) =
            FinDist.map
              (TypedMAID.Assignment.resolve diagram
                (Stage.Assignment.setOne assignment ⟨head, value⟩)
                tail.toFinset)
              (FinDist.pi
                (fun node : tailIndex => laws node.1)) := by
        rw [← hreindex, FinDist.map_comp]
        apply congrArg (fun f =>
          FinDist.map f (FinDist.pi remainingLaws))
        funext draw node
        by_cases hnodeHead : node = head
        · subst node
          simp [TypedMAID.Assignment.resolve,
            Stage.Assignment.setOne, headIndex, full,
            remainingEquiv, hheadNotFinset]
        · by_cases hnodeTail : node ∈ tail.toFinset
          · simp [TypedMAID.Assignment.resolve,
              Stage.Assignment.setOne, hnodeHead, hnodeTail,
              headIndex, full, remainingEquiv,
              remainingValue, tailIndex]
          · simp [TypedMAID.Assignment.resolve,
              Stage.Assignment.setOne, hnodeHead, hnodeTail]
      rw [fixedAssignmentRun]
      simp_rw [ih htailNodup]
      let fullLaws : (node : full) →
          FinDist (diagram.Value node.1) :=
        fun node => laws node.1
      rw [show (fun node :
          {node : Node // node ∈ (head :: tail).toFinset} =>
            laws node.1) = fullLaws by rfl,
        FinDist.pi_eq_map_product headIndex fullLaws,
        FinDist.map_comp]
      unfold FinDist.product
      rw [FinDist.map_bind]
      apply FinDist.bind_congr
      intro value _
      refine (hresolve value).symm.trans ?_
      rw [FinDist.map_comp]
      apply congrArg (fun f =>
        FinDist.map f (FinDist.pi remainingLaws))
      funext draw
      rfl

/-- A native frontier node uses exactly the global-assignment kernel exposed by
the serialized evaluator. -/
theorem assignmentNodeLaw_eq_nodeLaw
    [Fintype Node] [DecidableEq Node]
    (semantics : TypedMAID.Semantics diagram)
    (policy : TypedMAID.Policy diagram)
    (state : TypedMAID.FrontierState diagram)
    (node : {node // node ∈ state.frontier}) :
    assignmentNodeLaw semantics policy state.values node.1 =
      TypedMAID.nodeLaw diagram semantics policy state node := by
  unfold assignmentNodeLaw TypedMAID.nodeLaw
  simp only [TypedMAID.FrontierState.configOf]
  split <;> split
  · rfl
  · rename_i hchance owner hdecision
    have himpossible :
        TypedMAID.NodeKind.chance =
          TypedMAID.NodeKind.decision owner :=
      hchance.symm.trans hdecision
    cases himpossible
  · rename_i owner hdecision hchance
    have himpossible :
        TypedMAID.NodeKind.decision owner =
          TypedMAID.NodeKind.chance :=
      hdecision.symm.trans hchance
    cases himpossible
  · rename_i firstOwner hfirst secondOwner hsecond
    have howner : firstOwner = secondOwner :=
      TypedMAID.NodeKind.decision.inj (hfirst.symm.trans hsecond)
    subst secondOwner
    rfl

/-- No node in a native frontier is a parent of another node in that same
frontier. -/
theorem not_parent_of_mem_frontier
    [Fintype Node] [DecidableEq Node]
    (state : TypedMAID.FrontierState diagram)
    {first second : Node}
    (hfirst : first ∈ state.frontier)
    (hsecond : second ∈ state.frontier) :
    first ∉ diagram.parents second := by
  intro hparent
  have hresolved : first ∈ state.resolved :=
    state.frontier_parents_resolved hsecond hparent
  exact ((state.mem_frontier_iff first).mp hfirst).1 hresolved

/-- If the laws of a dependency-independent list agree at the starting
assignment, the dynamic serialized runner equals the runner with those laws
held fixed. -/
theorem assignmentRun_eq_fixed_of_pairwise [DecidableEq Node]
    (semantics : TypedMAID.Semantics diagram)
    (policy : TypedMAID.Policy diagram)
    (laws : (node : Node) → FinDist (diagram.Value node)) :
    ∀ (nodes : List Node),
      nodes.Pairwise
        (fun earlier later => earlier ∉ diagram.parents later) →
      ∀ assignment : TypedMAID.Assignment diagram,
        (∀ node ∈ nodes,
          assignmentNodeLaw semantics policy assignment node =
            laws node) →
        assignmentRun semantics policy nodes assignment =
          fixedAssignmentRun laws nodes assignment := by
  intro nodes
  induction nodes with
  | nil =>
      intro _ assignment _
      rfl
  | cons head tail ih =>
      intro hpairwise assignment hlaws
      have hhead :
          assignmentNodeLaw semantics policy assignment head =
            laws head :=
        hlaws head (by simp)
      have hheadTail :
          ∀ node ∈ tail, head ∉ diagram.parents node :=
        (List.pairwise_cons.mp hpairwise).1
      have htailPairwise :
          tail.Pairwise
            (fun earlier later => earlier ∉ diagram.parents later) :=
        (List.pairwise_cons.mp hpairwise).2
      simp only [assignmentRun, assignmentStep, fixedAssignmentRun]
      rw [FinDist.bind_map, hhead]
      apply FinDist.bind_congr
      intro value _
      apply ih htailPairwise
      intro node hnode
      rw [assignmentNodeLaw_setOne_of_not_parent semantics policy
        assignment value (hheadTail node hnode)]
      exact hlaws node (by simp [hnode])

/-- The serialized runner over one native frontier is the fixed-law product
runner for that frontier. -/
theorem assignmentRun_frontier_eq_fixed
    [Fintype Node] [DecidableEq Node]
    (semantics : TypedMAID.Semantics diagram)
    (policy : TypedMAID.Policy diagram)
    (state : TypedMAID.FrontierState diagram) :
    assignmentRun semantics policy state.frontier.toList state.values =
      fixedAssignmentRun
        (fun node => assignmentNodeLaw semantics policy state.values node)
        state.frontier.toList state.values := by
  apply assignmentRun_eq_fixed_of_pairwise
  · have hpairwise :
        ∀ (nodes : List Node),
          (∀ node ∈ nodes, node ∈ state.frontier) →
          nodes.Pairwise
            (fun earlier later => earlier ∉ diagram.parents later) := by
      intro nodes hnodes
      induction nodes with
      | nil =>
          simp
      | cons head tail ih =>
          rw [List.pairwise_cons]
          constructor
          · intro node hnode
            exact not_parent_of_mem_frontier state
              (hnodes head (by simp))
              (hnodes node (by simp [hnode]))
          · apply ih
            intro node hnode
            exact hnodes node (by simp [hnode])
    apply hpairwise
    intro node hnode
    exact Finset.mem_toList.mp hnode
  · intro node hnode
    rfl

/-- One native simultaneous-frontier step and one serialized pass over that
frontier induce the same law on assignments. -/
theorem map_values_step_eq_assignmentRun
    [Fintype Node] [DecidableEq Node]
    (semantics : TypedMAID.Semantics diagram)
    (policy : TypedMAID.Policy diagram)
    (state : TypedMAID.FrontierState diagram) :
    FinDist.map (fun reached => reached.values)
        (TypedMAID.step diagram semantics policy state) =
      assignmentRun semantics policy state.frontier.toList state.values := by
  rw [assignmentRun_frontier_eq_fixed,
    fixedAssignmentRun_eq_pi _ state.frontier.toList
      state.frontier.nodup_toList state.values,
    Finset.toList_toFinset]
  unfold TypedMAID.step TypedMAID.frontierLaw
  rw [FinDist.map_comp]
  have hlaws :
      (fun node : {node // node ∈ state.frontier} =>
        assignmentNodeLaw semantics policy state.values node.1) =
        fun node : {node // node ∈ state.frontier} =>
          TypedMAID.nodeLaw diagram semantics policy state node := by
    funext node
    exact assignmentNodeLaw_eq_nodeLaw semantics policy state node
  rw [hlaws]
  apply congrArg (fun f =>
    FinDist.map f
      (FinDist.pi fun node : {node // node ∈ state.frontier} =>
        TypedMAID.nodeLaw diagram semantics policy state node))
  funext draw
  rfl

end GameTheory.Experimental.TypedMAID.FrontierEquivalence
