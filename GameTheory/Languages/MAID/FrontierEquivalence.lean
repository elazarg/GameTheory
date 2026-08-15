/-
# Serialized/native typed MAID equivalence

The serialization theorem compares a dependent finite product over a native
frontier with sequential draws of the same node laws. This file keeps that
probability algebra separate from both evaluators.
-/

import GameTheory.Languages.MAID.Order

noncomputable section

namespace GameTheory.Languages.MAID.FrontierEquivalence

open GameTheory.Math.Probability
open GameTheory.Languages.MAID.ToEFG
open GameTheory.Languages.MAID.Order

universe uPlayer uNode uValue uIndex

variable {Player : Type uPlayer} {Node : Type uNode}
variable {diagram : GameTheory.Languages.MAID.Structure Player Node}

/-- Sequentially draw a fixed node-law family and replace each listed
coordinate. -/
def fixedAssignmentRun [DecidableEq Node]
    (laws : (node : Node) → FinDist (diagram.Value node)) :
    List Node → GameTheory.Languages.MAID.Assignment diagram →
      FinDist (GameTheory.Languages.MAID.Assignment diagram)
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
      ∀ assignment : GameTheory.Languages.MAID.Assignment diagram,
        fixedAssignmentRun laws nodes assignment =
          FinDist.map
            (GameTheory.Languages.MAID.Assignment.resolve diagram assignment
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
      simp [GameTheory.Languages.MAID.Assignment.resolve]
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
        simpa [remainingEquiv, remainingValue, remainingLaws, tailIndex] using
          FinDist.pi_reindex remainingValue remainingEquiv remainingLaws
      have hresolve
          (value : diagram.Value head) :
          FinDist.map
              (fun draw : (node : remaining) →
                  remainingValue node =>
                GameTheory.Languages.MAID.Assignment.resolve diagram assignment
                  (head :: tail).toFinset
                  ((Equiv.piSplitAt headIndex
                    (fun node : full =>
                      diagram.Value node.1)).symm
                    (value, draw)))
              (FinDist.pi remainingLaws) =
            FinDist.map
              (GameTheory.Languages.MAID.Assignment.resolve diagram
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
          simp [GameTheory.Languages.MAID.Assignment.resolve,
            Stage.Assignment.setOne, headIndex, full,
            remainingEquiv, hheadNotFinset]
        · by_cases hnodeTail : node ∈ tail.toFinset
          · simp [GameTheory.Languages.MAID.Assignment.resolve,
              Stage.Assignment.setOne, hnodeHead, hnodeTail,
              headIndex, full, remainingEquiv,
              remainingValue, tailIndex]
          · simp [GameTheory.Languages.MAID.Assignment.resolve,
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
    (semantics : GameTheory.Languages.MAID.Semantics diagram)
    (policy : GameTheory.Languages.MAID.Policy diagram)
    (state : GameTheory.Languages.MAID.FrontierState diagram)
    (node : {node // node ∈ state.frontier}) :
    assignmentNodeLaw semantics policy state.values node.1 =
      GameTheory.Languages.MAID.nodeLaw diagram semantics policy state node := by
  unfold assignmentNodeLaw GameTheory.Languages.MAID.nodeLaw
  simp only [GameTheory.Languages.MAID.FrontierState.configOf]
  split <;> split
  · rfl
  · rename_i hchance owner hdecision
    have himpossible :
        GameTheory.Languages.MAID.NodeKind.chance =
          GameTheory.Languages.MAID.NodeKind.decision owner :=
      hchance.symm.trans hdecision
    cases himpossible
  · rename_i owner hdecision hchance
    have himpossible :
        GameTheory.Languages.MAID.NodeKind.decision owner =
          GameTheory.Languages.MAID.NodeKind.chance :=
      hdecision.symm.trans hchance
    cases himpossible
  · rename_i firstOwner hfirst secondOwner hsecond
    have howner : firstOwner = secondOwner :=
      GameTheory.Languages.MAID.NodeKind.decision.inj (hfirst.symm.trans hsecond)
    subst secondOwner
    rfl

/-- No node in a native frontier is a parent of another node in that same
frontier. -/
theorem not_parent_of_mem_frontier
    [Fintype Node] [DecidableEq Node]
    (state : GameTheory.Languages.MAID.FrontierState diagram)
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
    (semantics : GameTheory.Languages.MAID.Semantics diagram)
    (policy : GameTheory.Languages.MAID.Policy diagram)
    (laws : (node : Node) → FinDist (diagram.Value node)) :
    ∀ (nodes : List Node),
      nodes.Pairwise
        (fun earlier later => earlier ∉ diagram.parents later) →
      ∀ assignment : GameTheory.Languages.MAID.Assignment diagram,
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
    (semantics : GameTheory.Languages.MAID.Semantics diagram)
    (policy : GameTheory.Languages.MAID.Policy diagram)
    (state : GameTheory.Languages.MAID.FrontierState diagram) :
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
    (semantics : GameTheory.Languages.MAID.Semantics diagram)
    (policy : GameTheory.Languages.MAID.Policy diagram)
    (state : GameTheory.Languages.MAID.FrontierState diagram) :
    FinDist.map (fun reached => reached.values)
        (GameTheory.Languages.MAID.step diagram semantics policy state) =
      assignmentRun semantics policy state.frontier.toList state.values := by
  rw [assignmentRun_frontier_eq_fixed,
    fixedAssignmentRun_eq_pi _ state.frontier.toList
      state.frontier.nodup_toList state.values,
    Finset.toList_toFinset]
  unfold GameTheory.Languages.MAID.step GameTheory.Languages.MAID.frontierLaw
  rw [FinDist.map_comp]
  have hlaws :
      (fun node : {node // node ∈ state.frontier} =>
        assignmentNodeLaw semantics policy state.values node.1) =
        fun node : {node // node ∈ state.frontier} =>
          GameTheory.Languages.MAID.nodeLaw diagram semantics policy state node := by
    funext node
    exact assignmentNodeLaw_eq_nodeLaw semantics policy state node
  rw [hlaws]
  apply congrArg (fun f =>
    FinDist.map f
      (FinDist.pi fun node : {node // node ∈ state.frontier} =>
        GameTheory.Languages.MAID.nodeLaw diagram semantics policy state node))
  funext draw
  rfl

/-- The nodes of a topological order that are not yet resolved. -/
def unresolvedOrder
    (topological :
      GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    [DecidableEq Node]
    (state : GameTheory.Languages.MAID.FrontierState diagram) : List Node :=
  topological.order.filter fun node => node ∉ state.resolved

/-- The nodes left after resolving the state's entire current frontier. -/
def remainingOrder
    (topological :
      GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    [Fintype Node] [DecidableEq Node]
    (state : GameTheory.Languages.MAID.FrontierState diagram) : List Node :=
  topological.order.filter fun node =>
    node ∉ state.resolved ∪ state.frontier

theorem unresolvedOrder_nodup
    (topological :
      GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    [DecidableEq Node]
    (state : GameTheory.Languages.MAID.FrontierState diagram) :
    (unresolvedOrder topological state).Nodup :=
  topological.nodup.filter _

theorem unresolvedOrder_pairwise
    (topological :
      GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    [DecidableEq Node]
    (state : GameTheory.Languages.MAID.FrontierState diagram) :
    (unresolvedOrder topological state).Pairwise
      (fun earlier later => later ∉ diagram.parents earlier) :=
  (topological_pairwise topological).filter _

theorem remainingOrder_nodup
    (topological :
      GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    [Fintype Node] [DecidableEq Node]
    (state : GameTheory.Languages.MAID.FrontierState diagram) :
    (remainingOrder topological state).Nodup :=
  topological.nodup.filter _

theorem remainingOrder_pairwise
    (topological :
      GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    [Fintype Node] [DecidableEq Node]
    (state : GameTheory.Languages.MAID.FrontierState diagram) :
    (remainingOrder topological state).Pairwise
      (fun earlier later => later ∉ diagram.parents earlier) :=
  (topological_pairwise topological).filter _

/-- Resolving a frontier changes only the values, so its remaining-order list
is the unresolved-order list of every possible extended state. -/
theorem unresolvedOrder_extend
    (topological :
      GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    [Fintype Node] [DecidableEq Node]
    (state : GameTheory.Languages.MAID.FrontierState diagram)
    (draw : (node : {node // node ∈ state.frontier}) →
      diagram.Value node.1) :
    unresolvedOrder topological (state.extend draw) =
      remainingOrder topological state :=
  rfl

/-- A current frontier followed by the nodes remaining after that frontier is
a duplicate-free permutation of the current unresolved topological order. -/
theorem frontier_append_remaining_perm
    (topological :
      GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    [Fintype Node] [DecidableEq Node]
    (state : GameTheory.Languages.MAID.FrontierState diagram) :
    (state.frontier.toList ++ remainingOrder topological state).Perm
      (unresolvedOrder topological state) := by
  have happendNodup :
      (state.frontier.toList ++
        remainingOrder topological state).Nodup := by
    rw [List.nodup_append]
    refine ⟨state.frontier.nodup_toList,
      remainingOrder_nodup topological state, ?_⟩
    intro first hfirst second hsecond heq
    subst second
    have hfrontier : first ∈ state.frontier :=
      Finset.mem_toList.mp hfirst
    have hremaining :
        first ∉ state.resolved ∪ state.frontier := by
      simpa [remainingOrder] using
        (List.mem_filter.mp hsecond).2
    exact hremaining (Finset.mem_union_right _ hfrontier)
  apply (List.perm_ext_iff_of_nodup happendNodup
    (unresolvedOrder_nodup topological state)).mpr
  intro node
  constructor
  · intro hnode
    rcases List.mem_append.mp hnode with hfrontier | hremaining
    · have hfrontierMem : node ∈ state.frontier :=
        Finset.mem_toList.mp hfrontier
      have hunresolved : node ∉ state.resolved :=
        ((state.mem_frontier_iff node).mp hfrontierMem).1
      simp [unresolvedOrder, topological.complete node, hunresolved]
    · have hfiltered :
          node ∈ topological.order ∧
            node ∉ state.resolved ∪ state.frontier := by
        simpa [remainingOrder] using hremaining
      have hunresolved : node ∉ state.resolved := by
        intro hresolved
        exact hfiltered.2 (Finset.mem_union_left _ hresolved)
      simp [unresolvedOrder, hfiltered.1, hunresolved]
  · intro hnode
    have hfiltered :
        node ∈ topological.order ∧ node ∉ state.resolved := by
      simpa [unresolvedOrder] using hnode
    by_cases hfrontier : node ∈ state.frontier
    · exact List.mem_append_left _
        (Finset.mem_toList.mpr hfrontier)
    · apply List.mem_append_right
      simp [remainingOrder, hfiltered.1, hfiltered.2, hfrontier]

theorem frontier_append_remaining_pairwise
    (topological :
      GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    [Fintype Node] [DecidableEq Node]
    (state : GameTheory.Languages.MAID.FrontierState diagram) :
    (state.frontier.toList ++ remainingOrder topological state).Pairwise
      (fun earlier later => later ∉ diagram.parents earlier) := by
  rw [List.pairwise_append]
  refine ⟨?_, remainingOrder_pairwise topological state, ?_⟩
  · have hpairwise :
        ∀ (nodes : List Node),
          (∀ node ∈ nodes, node ∈ state.frontier) →
          nodes.Pairwise
            (fun earlier later => later ∉ diagram.parents earlier) := by
      intro nodes hnodes
      induction nodes with
      | nil =>
          simp
      | cons head tail ih =>
          rw [List.pairwise_cons]
          constructor
          · intro node hnode
            exact not_parent_of_mem_frontier state
              (hnodes node (by simp [hnode]))
              (hnodes head (by simp))
          · apply ih
            intro node hnode
            exact hnodes node (by simp [hnode])
    apply hpairwise
    intro node hnode
    exact Finset.mem_toList.mp hnode
  · intro first hfirst second hsecond hparent
    have hfrontier : first ∈ state.frontier :=
      Finset.mem_toList.mp hfirst
    have hremaining :
        second ∉ state.resolved ∪ state.frontier := by
      simpa [remainingOrder] using
        (List.mem_filter.mp hsecond).2
    have hresolved : second ∈ state.resolved :=
      state.frontier_parents_resolved hfrontier hparent
    exact hremaining (Finset.mem_union_left _ hresolved)

/-- Serialized assignment execution composes over list concatenation. -/
theorem assignmentRun_append [DecidableEq Node]
    (semantics : GameTheory.Languages.MAID.Semantics diagram)
    (policy : GameTheory.Languages.MAID.Policy diagram) :
    ∀ (first second : List Node)
      (assignment : GameTheory.Languages.MAID.Assignment diagram),
      assignmentRun semantics policy (first ++ second) assignment =
        (assignmentRun semantics policy first assignment).bind
          (assignmentRun semantics policy second) := by
  intro first
  induction first with
  | nil =>
      intro second assignment
      simp [assignmentRun]
  | cons head tail ih =>
      intro second assignment
      simp only [List.cons_append, assignmentRun]
      rw [FinDist.bind_bind]
      apply FinDist.bind_congr
      intro afterHead _
      exact ih second afterHead

/-- The serialized unresolved-node runner factors into the current frontier
and the nodes remaining after that frontier. -/
theorem assignmentRun_unresolved_eq_frontier_bind_remaining
    (topological :
      GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    [Fintype Node] [DecidableEq Node]
    (semantics : GameTheory.Languages.MAID.Semantics diagram)
    (policy : GameTheory.Languages.MAID.Policy diagram)
    (state : GameTheory.Languages.MAID.FrontierState diagram) :
    assignmentRun semantics policy
        (unresolvedOrder topological state) state.values =
      (assignmentRun semantics policy state.frontier.toList
        state.values).bind
        (assignmentRun semantics policy
          (remainingOrder topological state)) := by
  rw [← assignmentRun_append]
  exact assignmentRun_eq_of_perm semantics policy
    (unresolvedOrder topological state)
    (state.frontier.toList ++ remainingOrder topological state)
    (frontier_append_remaining_perm topological state).symm
    (unresolvedOrder_nodup topological state)
    (unresolvedOrder_pairwise topological state)
    (frontier_append_remaining_pairwise topological state)
    state.values

/-- With the standard one-step-per-node fuel bound, the native frontier runner
has exactly the assignment law of serialized evaluation over every unresolved
node in any supplied topological order. -/
theorem map_values_run_eq_assignmentRun_unresolved
    (topological :
      GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    [Fintype Node] [DecidableEq Node]
    (semantics : GameTheory.Languages.MAID.Semantics diagram)
    (policy : GameTheory.Languages.MAID.Policy diagram) :
    ∀ (fuel : ℕ) (state : GameTheory.Languages.MAID.FrontierState diagram),
      Fintype.card Node - state.resolved.card ≤ fuel →
      FinDist.map (fun reached => reached.values)
          (GameTheory.Languages.MAID.run diagram semantics policy fuel state) =
        assignmentRun semantics policy
          (unresolvedOrder topological state) state.values := by
  intro fuel
  induction fuel with
  | zero =>
      intro state hbound
      have hcardLe :
          state.resolved.card ≤ Fintype.card Node :=
        Finset.card_le_univ state.resolved
      have hcard :
          state.resolved.card = Fintype.card Node := by
        omega
      have hcomplete : state.IsComplete :=
        state.resolved.card_eq_iff_eq_univ.mp hcard
      have hremaining :
          unresolvedOrder topological state = [] := by
        simp [unresolvedOrder, hcomplete]
      rw [GameTheory.Languages.MAID.run, FinDist.map_pure, hremaining,
        assignmentRun]
  | succ fuel ih =>
      intro state hbound
      by_cases hcomplete : state.IsComplete
      · have hremaining :
            unresolvedOrder topological state = [] := by
          simp [unresolvedOrder, hcomplete]
        rw [GameTheory.Languages.MAID.run, if_pos hcomplete, FinDist.map_pure,
          hremaining, assignmentRun]
      · rw [GameTheory.Languages.MAID.run, if_neg hcomplete, FinDist.map_bind]
        calc
          (GameTheory.Languages.MAID.step diagram semantics policy state).bind
              (fun next =>
                FinDist.map (fun reached => reached.values)
                  (GameTheory.Languages.MAID.run diagram semantics policy fuel next)) =
            (GameTheory.Languages.MAID.step diagram semantics policy state).bind
              (fun next =>
                assignmentRun semantics policy
                  (unresolvedOrder topological next) next.values) := by
              apply FinDist.bind_congr
              intro next hnext
              obtain ⟨draw, rfl⟩ :=
                GameTheory.Languages.MAID.eq_extend_of_mem_support_step
                  diagram semantics policy state next hnext
              have hcardGrowth :
                  state.resolved.card <
                    (state.extend draw).resolved.card :=
                Finset.card_lt_card
                  (state.resolved_ssubset_extend_of_incomplete
                    hcomplete draw)
              have hstateCardLe :
                  state.resolved.card ≤ Fintype.card Node :=
                Finset.card_le_univ state.resolved
              have hnextCardLe :
                  (state.extend draw).resolved.card ≤
                    Fintype.card Node :=
                Finset.card_le_univ (state.extend draw).resolved
              have hnextBound :
                  Fintype.card Node -
                      (state.extend draw).resolved.card ≤ fuel := by
                omega
              exact ih (state.extend draw) hnextBound
          _ =
            (GameTheory.Languages.MAID.step diagram semantics policy state).bind
              (fun next =>
                assignmentRun semantics policy
                  (remainingOrder topological state) next.values) := by
              apply FinDist.bind_congr
              intro next hnext
              obtain ⟨draw, rfl⟩ :=
                GameTheory.Languages.MAID.eq_extend_of_mem_support_step
                  diagram semantics policy state next hnext
              rw [unresolvedOrder_extend]
          _ =
            (FinDist.map (fun next => next.values)
              (GameTheory.Languages.MAID.step diagram semantics policy state)).bind
                (assignmentRun semantics policy
                  (remainingOrder topological state)) := by
              rw [FinDist.bind_map]
          _ =
            (assignmentRun semantics policy state.frontier.toList
              state.values).bind
                (assignmentRun semantics policy
                  (remainingOrder topological state)) := by
              rw [map_values_step_eq_assignmentRun]
          _ =
            assignmentRun semantics policy
              (unresolvedOrder topological state) state.values :=
              (assignmentRun_unresolved_eq_frontier_bind_remaining
                topological semantics policy state).symm

/-- A complete native frontier run from the initial state equals serialized
assignment execution at any topological order. -/
theorem map_values_nativeRun_eq_assignmentRun
    (topological :
      GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    [Fintype Node] [DecidableEq Node]
    (semantics : GameTheory.Languages.MAID.Semantics diagram)
    (policy : GameTheory.Languages.MAID.Policy diagram) :
    FinDist.map (fun reached => reached.values)
        (GameTheory.Languages.MAID.run diagram semantics policy
          (Fintype.card Node)
          (GameTheory.Languages.MAID.FrontierState.initial semantics)) =
      assignmentRun semantics policy topological.order
        semantics.defaultValue := by
  rw [map_values_run_eq_assignmentRun_unresolved
    topological semantics policy (Fintype.card Node)
      (GameTheory.Languages.MAID.FrontierState.initial semantics) (by
        simp [GameTheory.Languages.MAID.FrontierState.initial])]
  simp [unresolvedOrder, GameTheory.Languages.MAID.FrontierState.initial]

/-- The native frontier evaluator and the explicit serialized stage evaluator
produce the same complete typed-assignment law. -/
theorem nativeRun_eq_serialRun
    (topological :
      GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    [Fintype Player] [DecidableEq Player]
    [Fintype Node] [DecidableEq Node]
    (semantics : GameTheory.Languages.MAID.Semantics diagram)
    (policy : GameTheory.Languages.MAID.Policy diagram) :
    FinDist.map (fun reached => reached.values)
        (GameTheory.Languages.MAID.run diagram semantics policy
          (Fintype.card Node)
          (GameTheory.Languages.MAID.FrontierState.initial semantics)) =
      FinDist.map (Stage.assignment topological semantics)
        (serialRun topological semantics policy
          topological.order.length (Stage.initial topological)) := by
  rw [map_values_nativeRun_eq_assignmentRun topological semantics policy,
    map_assignment_serialRun topological semantics policy
      topological.order.length (Stage.initial topological)
      (by simp [Stage.initial])]
  simp [Stage.initial, Stage.assignment]

/-- The native simultaneous-frontier evaluator and
the compiled EFG's actual behavioral runner have the same complete
typed-assignment law. -/
theorem nativeRun_eq_compiledBehavioralRun
    (topological :
      GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    [Fintype Player] [DecidableEq Player]
    [Fintype Node] [DecidableEq Node]
    (semantics : GameTheory.Languages.MAID.Semantics diagram)
    (policy : GameTheory.Languages.MAID.Policy diagram) :
    FinDist.map (fun reached => reached.values)
        (GameTheory.Languages.MAID.run diagram semantics policy
          (Fintype.card Node)
          (GameTheory.Languages.MAID.FrontierState.initial semantics)) =
      FinDist.map
        (fun history =>
          Stage.assignment topological semantics history.state)
        ((information topological semantics).runBehavioral
          (behavioralProfile topological semantics policy)
          topological.order.length) := by
  have hstate :=
    map_state_runBehavioralFrom_eq_serialRun topological semantics
      policy topological.order.length
      (execution topological semantics).initHistory
  have hassignment :=
    congrArg (FinDist.map (Stage.assignment topological semantics))
      hstate
  rw [FinDist.map_comp] at hassignment
  calc
    _ =
        FinDist.map (Stage.assignment topological semantics)
          (serialRun topological semantics policy
            topological.order.length (Stage.initial topological)) :=
      nativeRun_eq_serialRun topological semantics policy
    _ = _ := by
      simpa [
        GameTheory.Protocol.InformationModel.runBehavioral,
        Function.comp_def] using hassignment.symm

end GameTheory.Languages.MAID.FrontierEquivalence
