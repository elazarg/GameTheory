/-
# EXP-041: typed MAID order algebra

This file isolates the order-independence payload from the EFG compiler.
Node kernels act on the typed total assignment, and independent kernels commute
without exposing a swap certificate or an implementation-specific state type.
The adjacent-kernel proof shape is adapted from the pinned
`GameTheory/Languages/MAID/FoldEval.lean` at commit
`a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`; the typed carrier, direct global
theorem, and compiler bridge are new.
-/

import GameTheory.Experimental.PostArchitecture.TypedMAIDToEFG

noncomputable section

namespace GameTheory.Experimental.TypedMAID.Order

open GameTheory.Probability
open GameTheory.Experimental.TypedMAID.ToEFG

universe uPlayer uNode uValue

variable {Player : Type uPlayer} {Node : Type uNode}
variable {diagram : TypedMAID.Structure Player Node}

/-- The source law for one node, viewed directly as a kernel on complete typed
assignments. Topological validity is imposed by the caller's node order. -/
def assignmentNodeLaw
    (semantics : TypedMAID.Semantics diagram)
    (policy : TypedMAID.Policy diagram)
    (assignment : TypedMAID.Assignment diagram)
    (node : Node) : FinDist (diagram.Value node) := by
  match hkind : diagram.kind node with
  | .chance =>
      exact semantics.chanceLaw node hkind
        (TypedMAID.Assignment.restrict diagram assignment
          (diagram.parents node))
  | .decision owner =>
      exact policy owner ⟨node, hkind⟩
        (TypedMAID.Assignment.restrict diagram assignment
          (diagram.observedParents node))

/-- Draw one node and replace exactly its coordinate. -/
def assignmentStep [DecidableEq Node]
    (semantics : TypedMAID.Semantics diagram)
    (policy : TypedMAID.Policy diagram)
    (assignment : TypedMAID.Assignment diagram)
    (node : Node) : FinDist (TypedMAID.Assignment diagram) :=
  FinDist.map
    (fun value =>
      Stage.Assignment.setOne assignment ⟨node, value⟩)
    (assignmentNodeLaw semantics policy assignment node)

theorem setOne_comm [DecidableEq Node]
    (assignment : TypedMAID.Assignment diagram)
    {first second : Node}
    (firstValue : diagram.Value first)
    (secondValue : diagram.Value second)
    (hne : first ≠ second) :
    Stage.Assignment.setOne
        (Stage.Assignment.setOne assignment ⟨first, firstValue⟩)
        ⟨second, secondValue⟩ =
      Stage.Assignment.setOne
        (Stage.Assignment.setOne assignment ⟨second, secondValue⟩)
        ⟨first, firstValue⟩ := by
  funext node
  by_cases hfirst : node = first
  · subst node
    simp [Stage.Assignment.setOne, TypedMAID.Assignment.resolve, hne]
  · by_cases hsecond : node = second
    · subst node
      simp [Stage.Assignment.setOne, TypedMAID.Assignment.resolve,
        hfirst]
    · simp [Stage.Assignment.setOne, TypedMAID.Assignment.resolve,
        hfirst, hsecond]

theorem restrict_setOne_of_not_mem [DecidableEq Node]
    (assignment : TypedMAID.Assignment diagram)
    (nodes : Finset Node)
    {changed : Node} (value : diagram.Value changed)
    (hchanged : changed ∉ nodes) :
    TypedMAID.Assignment.restrict diagram
        (Stage.Assignment.setOne assignment ⟨changed, value⟩)
        nodes =
      TypedMAID.Assignment.restrict diagram assignment nodes := by
  funext node
  have hne : node.1 ≠ changed := by
    intro heq
    subst changed
    exact hchanged node.2
  simp [TypedMAID.Assignment.restrict, Stage.Assignment.setOne,
    TypedMAID.Assignment.resolve, hne]

theorem assignmentNodeLaw_setOne_of_not_parent [DecidableEq Node]
    (semantics : TypedMAID.Semantics diagram)
    (policy : TypedMAID.Policy diagram)
    (assignment : TypedMAID.Assignment diagram)
    {changed node : Node} (value : diagram.Value changed)
    (hnotParent : changed ∉ diagram.parents node) :
    assignmentNodeLaw semantics policy
        (Stage.Assignment.setOne assignment ⟨changed, value⟩) node =
      assignmentNodeLaw semantics policy assignment node := by
  unfold assignmentNodeLaw
  split
  next =>
    rw [restrict_setOne_of_not_mem assignment
      (diagram.parents node) value hnotParent]
  next owner _ =>
    have hnotObserved : changed ∉ diagram.observedParents node := by
      intro hobserved
      exact hnotParent (diagram.observed_sub node hobserved)
    rw [restrict_setOne_of_not_mem assignment
      (diagram.observedParents node) value hnotObserved]

/-- The mathematical core of topological-order independence: two distinct
nodes with no direct causal edge in either direction commute as assignment
kernels. -/
theorem assignmentStep_comm [DecidableEq Node]
    (semantics : TypedMAID.Semantics diagram)
    (policy : TypedMAID.Policy diagram)
    (assignment : TypedMAID.Assignment diagram)
    (first second : Node)
    (hne : first ≠ second)
    (hfirstSecond : first ∉ diagram.parents second)
    (hsecondFirst : second ∉ diagram.parents first) :
    (assignmentStep semantics policy assignment first).bind
        (fun afterFirst =>
          assignmentStep semantics policy afterFirst second) =
      (assignmentStep semantics policy assignment second).bind
        (fun afterSecond =>
          assignmentStep semantics policy afterSecond first) := by
  unfold assignmentStep
  rw [FinDist.bind_map, FinDist.bind_map]
  simp_rw [assignmentNodeLaw_setOne_of_not_parent semantics policy
    assignment _ hfirstSecond]
  simp_rw [assignmentNodeLaw_setOne_of_not_parent semantics policy
    assignment _ hsecondFirst]
  simp_rw [FinDist.map_eq_bind]
  rw [FinDist.bind_comm]
  apply FinDist.bind_congr
  intro secondValue _
  apply FinDist.bind_congr
  intro firstValue _
  rw [setOne_comm assignment firstValue secondValue hne]

/-- Sequentially execute a node list on a typed assignment. -/
def assignmentRun [DecidableEq Node]
    (semantics : TypedMAID.Semantics diagram)
    (policy : TypedMAID.Policy diagram) :
    List Node → TypedMAID.Assignment diagram →
      FinDist (TypedMAID.Assignment diagram)
  | [], assignment => FinDist.pure assignment
  | node :: rest, assignment =>
      (assignmentStep semantics policy assignment node).bind
        (assignmentRun semantics policy rest)

/-- Adjacent independent nodes may be exchanged under any already-resolved
prefix and before any common continuation. -/
theorem assignmentRun_swap_adjacent [DecidableEq Node]
    (semantics : TypedMAID.Semantics diagram)
    (policy : TypedMAID.Policy diagram)
    (before after : List Node)
    (first second : Node)
    (hne : first ≠ second)
    (hfirstSecond : first ∉ diagram.parents second)
    (hsecondFirst : second ∉ diagram.parents first)
    (assignment : TypedMAID.Assignment diagram) :
    assignmentRun semantics policy
        (before ++ first :: second :: after) assignment =
      assignmentRun semantics policy
        (before ++ second :: first :: after) assignment := by
  induction before generalizing assignment with
  | nil =>
      simp only [List.nil_append, assignmentRun]
      rw [← FinDist.bind_bind, ← FinDist.bind_bind,
        assignmentStep_comm semantics policy assignment first second
          hne hfirstSecond hsecondFirst]
  | cons node rest ih =>
      simp only [List.cons_append, assignmentRun]
      apply FinDist.bind_congr
      intro afterNode _
      exact ih afterNode

/-- Move one node left through a list of nodes independent of it. -/
theorem assignmentRun_move_left [DecidableEq Node]
    (semantics : TypedMAID.Semantics diagram)
    (policy : TypedMAID.Policy diagram)
    (before after : List Node)
    (node : Node)
    (hindependent : ∀ other ∈ before,
      node ≠ other ∧
      node ∉ diagram.parents other ∧
      other ∉ diagram.parents node)
    (assignment : TypedMAID.Assignment diagram) :
    assignmentRun semantics policy
        (before ++ node :: after) assignment =
      assignmentRun semantics policy
        (node :: before ++ after) assignment := by
  induction before generalizing assignment with
  | nil => rfl
  | cons other rest ih =>
      have hother := hindependent other (by simp)
      have hrest : ∀ candidate ∈ rest,
          node ≠ candidate ∧
          node ∉ diagram.parents candidate ∧
          candidate ∉ diagram.parents node := by
        intro candidate hcandidate
        exact hindependent candidate (by simp [hcandidate])
      calc
        assignmentRun semantics policy
            ((other :: rest) ++ node :: after) assignment =
          (assignmentStep semantics policy assignment other).bind
            (fun afterOther =>
              assignmentRun semantics policy
                (rest ++ node :: after) afterOther) := rfl
        _ =
          (assignmentStep semantics policy assignment other).bind
            (fun afterOther =>
              assignmentRun semantics policy
                (node :: rest ++ after) afterOther) := by
            apply FinDist.bind_congr
            intro afterOther _
            exact ih hrest afterOther
        _ =
          assignmentRun semantics policy
            (other :: node :: rest ++ after) assignment := rfl
        _ =
          assignmentRun semantics policy
            (node :: other :: rest ++ after) assignment := by
            exact assignmentRun_swap_adjacent semantics policy
              [] (rest ++ after) other node hother.1.symm
                hother.2.2 hother.2.1 assignment

/-- Two duplicate-free dependency-compatible permutations induce the same
assignment law. The proof removes the first node of the left list after
bubbling its occurrence leftward in the right list. -/
theorem assignmentRun_eq_of_perm
    [DecidableEq Node]
    (semantics : TypedMAID.Semantics diagram)
    (policy : TypedMAID.Policy diagram) :
    ∀ (first second : List Node),
      first.Perm second →
      first.Nodup →
      first.Pairwise
        (fun earlier later => later ∉ diagram.parents earlier) →
      second.Pairwise
        (fun earlier later => later ∉ diagram.parents earlier) →
      ∀ assignment : TypedMAID.Assignment diagram,
        assignmentRun semantics policy first assignment =
          assignmentRun semantics policy second assignment := by
  intro first
  induction first with
  | nil =>
      intro second hperm _ _ _ assignment
      have hnil : second = [] := hperm.nil_eq.symm
      subst second
      rfl
  | cons node rest ih =>
      intro second hperm hnodup hfirstOrder hsecondOrder assignment
      have hnodeSecond : node ∈ second :=
        hperm.mem_iff.mp (by simp)
      obtain ⟨before, after, hsecond⟩ :=
        List.mem_iff_append.mp hnodeSecond
      subst second
      have hsecondNodup :
          (before ++ node :: after).Nodup :=
        hperm.nodup_iff.mp hnodup
      have hrestPerm :
          rest.Perm (before ++ after) := by
        exact (hperm.trans List.perm_middle).cons_inv
      have hrestNodup : rest.Nodup :=
        (List.nodup_cons.mp hnodup).2
      have hrestOrder :
          rest.Pairwise
            (fun earlier later =>
              later ∉ diagram.parents earlier) :=
        (List.pairwise_cons.mp hfirstOrder).2
      have hremainingSublist :
          (before ++ after).Sublist
            (before ++ node :: after) :=
        List.Sublist.append (List.Sublist.refl before)
          (List.sublist_cons_self node after)
      have hremainingOrder :
          (before ++ after).Pairwise
            (fun earlier later =>
              later ∉ diagram.parents earlier) :=
        hsecondOrder.sublist hremainingSublist
      have hheadOrder :
          ∀ other ∈ rest,
            other ∉ diagram.parents node :=
        (List.pairwise_cons.mp hfirstOrder).1
      have hrightCross :
          ∀ other ∈ before,
            node ∉ diagram.parents other := by
        intro other hother
        exact (List.pairwise_append.mp hsecondOrder).2.2
          other hother node (by simp)
      have hindependent : ∀ other ∈ before,
          node ≠ other ∧
          node ∉ diagram.parents other ∧
          other ∉ diagram.parents node := by
        intro other hother
        have hotherRemaining : other ∈ before ++ after := by
          exact List.mem_append_left after hother
        have hotherRest : other ∈ rest :=
          hrestPerm.mem_iff.mpr hotherRemaining
        have hdistinct : other ≠ node :=
          (List.nodup_append.mp hsecondNodup).2.2
            other hother node (by simp)
        exact ⟨hdistinct.symm, hrightCross other hother,
          hheadOrder other hotherRest⟩
      symm
      calc
        assignmentRun semantics policy
            (before ++ node :: after) assignment =
          assignmentRun semantics policy
            (node :: before ++ after) assignment :=
          assignmentRun_move_left semantics policy before after
            node hindependent assignment
        _ =
          assignmentRun semantics policy
            (node :: rest) assignment := by
            simp only [assignmentRun]
            apply FinDist.bind_congr
            intro afterNode _
            exact (ih (before ++ after) hrestPerm hrestNodup
              hrestOrder hremainingOrder afterNode).symm

theorem topological_pairwise
    (topological :
      GameTheoryMath.DAG.TopologicalOrder diagram.parents) :
    topological.order.Pairwise
      (fun earlier later => later ∉ diagram.parents earlier) := by
  rw [List.pairwise_iff_getElem]
  intro firstIndex laterIndex hfirstBound hlaterBound hlt hedge
  obtain ⟨parentIndex, hparentLt, hparent⟩ :=
    topological.respects ⟨firstIndex, hfirstBound⟩
      topological.order[laterIndex] hedge
  have hindexEq :
      parentIndex = ⟨laterIndex, hlaterBound⟩ :=
    topological.nodup.get_inj_iff.mp hparent
  have hvalueEq : parentIndex.val = laterIndex := by
    simpa using congrArg Fin.val hindexEq
  have hreverse := hparentLt
  rw [hvalueEq] at hreverse
  exact (Nat.not_lt_of_ge (Nat.le_of_lt hlt)) hreverse

/-- Assignment evaluation is independent of the chosen valid topological
order. This is the direct theorem; no public swap-reachability certificate is
introduced. -/
theorem assignmentRun_topological_order_independent
    [DecidableEq Node]
    (semantics : TypedMAID.Semantics diagram)
    (policy : TypedMAID.Policy diagram)
    (first second :
      GameTheoryMath.DAG.TopologicalOrder diagram.parents)
    (assignment : TypedMAID.Assignment diagram) :
    assignmentRun semantics policy first.order assignment =
      assignmentRun semantics policy second.order assignment := by
  have hperm : first.order.Perm second.order :=
    (List.perm_ext_iff_of_nodup first.nodup second.nodup).mpr
      fun node => ⟨
        fun _ => second.complete node,
        fun _ => first.complete node⟩
  exact assignmentRun_eq_of_perm semantics policy
    first.order second.order hperm first.nodup
      (topological_pairwise first)
      (topological_pairwise second) assignment

theorem serialNodeLaw_eq_assignmentNodeLaw
    (topological :
      GameTheoryMath.DAG.TopologicalOrder diagram.parents)
    [DecidableEq Player] [DecidableEq Node]
    (semantics : TypedMAID.Semantics diagram)
    (policy : TypedMAID.Policy diagram)
    (state : Stage diagram topological)
    (hpending : state.path.length < topological.order.length) :
    serialNodeLaw topological semantics policy state hpending =
      assignmentNodeLaw semantics policy
        (state.assignment topological semantics)
        (state.pendingNode topological hpending) := by
  match hkind :
      diagram.kind (state.pendingNode topological hpending) with
  | .chance =>
      rw [serialNodeLaw_of_chance topological semantics policy
        state hpending hkind]
      unfold assignmentNodeLaw Stage.configOf
      split
      next => rfl
      next owner hdecision =>
        rw [hkind] at hdecision
        contradiction
  | .decision owner =>
      rw [serialNodeLaw_of_decision topological semantics policy
        state hpending hkind]
      unfold assignmentNodeLaw Stage.configOf
      split
      next hchance =>
        rw [hkind] at hchance
        contradiction
      next activeOwner hdecision =>
        have howner : activeOwner = owner :=
          TypedMAID.NodeKind.decision.inj
            (hdecision.symm.trans hkind)
        subst activeOwner
        rfl

theorem assignment_advance
    (topological :
      GameTheoryMath.DAG.TopologicalOrder diagram.parents)
    [DecidableEq Node]
    (semantics : TypedMAID.Semantics diagram)
    (state : Stage diagram topological)
    (hpending : state.path.length < topological.order.length)
    (value : diagram.Value (state.pendingNode topological hpending)) :
    (state.advance topological hpending value).assignment
        topological semantics =
      Stage.Assignment.setOne (state.assignment topological semantics)
        ⟨state.pendingNode topological hpending, value⟩ := by
  simp [Stage.assignment, Stage.advance_path, List.foldl_append]

theorem map_assignment_serialStep
    (topological :
      GameTheoryMath.DAG.TopologicalOrder diagram.parents)
    [DecidableEq Player] [DecidableEq Node]
    (semantics : TypedMAID.Semantics diagram)
    (policy : TypedMAID.Policy diagram)
    (state : Stage diagram topological)
    (hpending : state.path.length < topological.order.length) :
    FinDist.map (Stage.assignment topological semantics)
        (serialStep topological semantics policy state hpending) =
      assignmentStep semantics policy
        (state.assignment topological semantics)
        (state.pendingNode topological hpending) := by
  unfold serialStep assignmentStep
  rw [FinDist.map_comp,
    serialNodeLaw_eq_assignmentNodeLaw topological semantics policy
      state hpending]
  apply congrArg (fun f =>
    FinDist.map f
      (assignmentNodeLaw semantics policy
        (state.assignment topological semantics)
        (state.pendingNode topological hpending)))
  funext value
  exact assignment_advance topological semantics state hpending value

/-- A complete serialized stage run has exactly the assignment law obtained by
executing the remaining explicit node list. -/
theorem map_assignment_serialRun
    (topological :
      GameTheoryMath.DAG.TopologicalOrder diagram.parents)
    [DecidableEq Player] [DecidableEq Node]
    (semantics : TypedMAID.Semantics diagram)
    (policy : TypedMAID.Policy diagram) :
    ∀ (fuel : ℕ) (state : Stage diagram topological),
      (topological.order.drop state.path.length).length = fuel →
      FinDist.map (Stage.assignment topological semantics)
          (serialRun topological semantics policy fuel state) =
        assignmentRun semantics policy
          (topological.order.drop state.path.length)
          (state.assignment topological semantics) := by
  intro fuel
  induction fuel with
  | zero =>
      intro state hremaining
      have hempty :
          topological.order.drop state.path.length = [] :=
        List.length_eq_zero_iff.mp hremaining
      rw [serialRun, FinDist.map_pure, hempty, assignmentRun]
  | succ fuel ih =>
      intro state hremaining
      have hterminal :
          state.path.length ≠ topological.order.length := by
        intro heq
        rw [heq] at hremaining
        simp at hremaining
      have hpending :
          state.path.length < topological.order.length :=
        Nat.lt_of_le_of_ne state.length_le hterminal
      have hdrop :
          topological.order.drop state.path.length =
            state.pendingNode topological hpending ::
              topological.order.drop (state.path.length + 1) := by
        exact List.drop_eq_getElem_cons hpending
      have htail :
          (topological.order.drop
            (state.path.length + 1)).length = fuel := by
        simp only [List.length_drop] at hremaining ⊢
        omega
      rw [serialRun, dif_neg hterminal, FinDist.map_bind,
        hdrop, assignmentRun]
      unfold serialStep assignmentStep
      rw [FinDist.bind_map, FinDist.bind_map,
        serialNodeLaw_eq_assignmentNodeLaw topological semantics
          policy state hpending]
      apply FinDist.bind_congr
      intro value _
      rw [ih (state.advance topological hpending value)]
      · simp only [Stage.advance_length]
        rw [assignment_advance topological semantics state hpending value]
      · simpa only [Stage.advance_length, Nat.add_comm] using htail

/-- Complete serialized runs at any two topological orders have exactly the
same typed assignment law. -/
theorem serialRun_topological_order_independent
    [DecidableEq Player] [DecidableEq Node]
    (semantics : TypedMAID.Semantics diagram)
    (policy : TypedMAID.Policy diagram)
    (first second :
      GameTheoryMath.DAG.TopologicalOrder diagram.parents) :
    FinDist.map (Stage.assignment first semantics)
        (serialRun first semantics policy first.order.length
          (Stage.initial first)) =
      FinDist.map (Stage.assignment second semantics)
        (serialRun second semantics policy second.order.length
          (Stage.initial second)) := by
  rw [map_assignment_serialRun first semantics policy
      first.order.length (Stage.initial first) (by simp [Stage.initial]),
    map_assignment_serialRun second semantics policy
      second.order.length (Stage.initial second)
        (by simp [Stage.initial])]
  exact assignmentRun_topological_order_independent semantics policy
    first second semantics.defaultValue

/-- On the one-owner compiler path, the actual EFG behavioral assignment law
is independent of the supplied topological order. -/
theorem behavioralRun_topological_order_independent_unit
    {Vertex : Type uNode}
    {unitDiagram : TypedMAID.Structure Unit Vertex}
    [DecidableEq Vertex]
    (semantics : TypedMAID.Semantics unitDiagram)
    (policy : TypedMAID.Policy unitDiagram)
    (first second :
      GameTheoryMath.DAG.TopologicalOrder unitDiagram.parents) :
    FinDist.map
        (fun history =>
          Stage.assignment first semantics history.state)
        ((information first semantics).runBehavioral
          (behavioralProfile first semantics policy)
          first.order.length) =
      FinDist.map
        (fun history =>
          Stage.assignment second semantics history.state)
        ((information second semantics).runBehavioral
          (behavioralProfile second semantics policy)
          second.order.length) := by
  have hfirstState :=
    map_state_runBehavioralFrom_eq_serialRun_unit first semantics
      policy first.order.length (execution first semantics).initHistory
  have hfirstAssignment :=
    congrArg (FinDist.map (Stage.assignment first semantics))
      hfirstState
  rw [FinDist.map_comp] at hfirstAssignment
  have hsecondState :=
    map_state_runBehavioralFrom_eq_serialRun_unit second semantics
      policy second.order.length (execution second semantics).initHistory
  have hsecondAssignment :=
    congrArg (FinDist.map (Stage.assignment second semantics))
      hsecondState
  rw [FinDist.map_comp] at hsecondAssignment
  calc
    _ =
        FinDist.map (Stage.assignment first semantics)
          (serialRun first semantics policy first.order.length
            (Stage.initial first)) := by
      simpa [
        GameTheory.Protocol.InformationModel.runBehavioral,
        Function.comp_def] using hfirstAssignment
    _ =
        FinDist.map (Stage.assignment second semantics)
          (serialRun second semantics policy second.order.length
            (Stage.initial second)) :=
      serialRun_topological_order_independent semantics policy
        first second
    _ = _ := by
      simpa [
        GameTheory.Protocol.InformationModel.runBehavioral,
        Function.comp_def] using hsecondAssignment.symm

end GameTheory.Experimental.TypedMAID.Order
