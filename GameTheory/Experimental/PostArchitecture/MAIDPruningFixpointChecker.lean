/-
# EXP-109: executable MAID edge-addition fixpoint checker

The graph carrier is enumerated from a caller-supplied topological order.  The
checker uses that list for every directed and ancestral-moral reachability
query; no finite carrier is stored in the MAID data.
-/

import GameTheory.Experimental.PostArchitecture.FiniteDirectedReachability
import GameTheory.Experimental.PostArchitecture.MAIDGraphDeciders

namespace GameTheory.Experimental.PostArchitecture.MAIDPruningFixpointGraph

open GameTheory.Languages.MAID
open GameTheory.Languages.MAID.ObservationPruning
open MAIDRequisiteObservation
open FiniteDirectedReachability

universe uPlayer uNode

variable {Player : Type uPlayer} {Node : Type uNode}
variable {diagram : Structure Player Node}
variable {semantics : Semantics diagram}

namespace UtilityView

variable (view : MAIDRequisiteObservation.UtilityView semantics)
variable (owner : Player)

def graphNodeEnumeration [DecidableEq Node]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents) :
    Enumeration (view.GraphNode owner) where
  nodes := graphNodeList view owner topological
  nodup := graphNodeList_nodup view owner topological
  complete := graphNode_mem_graphNodeList view owner topological

def directedReachableUnder? [DecidableEq Node]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (decisionParents : DecisionParentMap Node)
    (source target : view.GraphNode owner) : Bool :=
  (graphNodeEnumeration view owner topological).reachable
    (fun parent child => directedEdgeUnder? view owner decisionParents parent child)
    source target

theorem directedReachableUnder?_eq_true_iff [DecidableEq Node]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (decisionParents : DecisionParentMap Node)
    (source target : view.GraphNode owner) :
    directedReachableUnder? view owner topological decisionParents source target = true ↔
      Relation.ReflTransGen
        (DirectedEdgeUnder view owner decisionParents) source target := by
  have h := Enumeration.reachable_eq_true_iff
      (graphNodeEnumeration view owner topological)
      (fun parent child =>
        directedEdgeUnder? view owner decisionParents parent child) source target
  constructor
  · intro reachable
    apply (h.mp reachable).lift id
    intro parent child hedge
    exact (directedEdgeUnder?_eq_true_iff view owner decisionParents parent child).mp hedge
  · intro reachable
    apply h.mpr
    apply reachable.lift id
    intro parent child hedge
    exact (directedEdgeUnder?_eq_true_iff view owner decisionParents parent child).mpr hedge

/-- Strict directed relevance from a decision node to one of the owner's
utility leaves.  The generic closure is reflexive, but these two constructors
are disjoint, so a successful query necessarily contains an edge. -/
def isRelevantUtilityTermUnder? [DecidableEq Node]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (decisionParents : DecisionParentMap Node)
    (site : DecisionSite diagram owner) (term : view.UtilitySite owner) : Bool :=
  directedReachableUnder? view owner topological decisionParents
    (.base site.1) (.utility term)

theorem isRelevantUtilityTermUnder?_eq_true_iff [DecidableEq Node]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (decisionParents : DecisionParentMap Node)
    (site : DecisionSite diagram owner) (term : view.UtilitySite owner) :
    isRelevantUtilityTermUnder? view owner topological decisionParents site term = true ↔
      IsRelevantUtilityTermUnder view decisionParents site term := by
  rw [isRelevantUtilityTermUnder?, directedReachableUnder?_eq_true_iff]
  unfold IsRelevantUtilityTermUnder
  constructor
  · intro path
    rw [Relation.reflTransGen_iff_eq_or_transGen] at path
    rcases path with equality | path
    · cases equality
    · exact path
  · intro path
    exact path.to_reflTransGen

def ancestralUnder? [DecidableEq Node]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (decisionParents : DecisionParentMap Node)
    (source target : view.GraphNode owner)
    (evidence : Finset (view.GraphNode owner))
    (node : view.GraphNode owner) : Bool :=
  (graphNodeEnumeration view owner topological).nodes.any fun root =>
    (decide (root = source ∨ root = target ∨ root ∈ evidence)) &&
      directedReachableUnder? view owner topological decisionParents node root

theorem ancestralUnder?_eq_true_iff [DecidableEq Node]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (decisionParents : DecisionParentMap Node)
    (source target : view.GraphNode owner)
    (evidence : Finset (view.GraphNode owner))
    (node : view.GraphNode owner) :
    ancestralUnder? view owner topological decisionParents source target evidence node =
        true ↔
      FiniteBNMoralSeparation.InAncestralClosure
        (graphParentsUnder view decisionParents) {source} {target} evidence node := by
  rw [ancestralUnder?, List.any_eq_true]
  constructor
  · rintro ⟨root, hroot, hrootQuery⟩
    rw [Bool.and_eq_true] at hrootQuery
    have hroot'' : root = source ∨ root = target ∨ root ∈ evidence :=
      decide_eq_true_eq.mp hrootQuery.1
    have hpath : Relation.ReflTransGen
        (DirectedEdgeUnder view owner decisionParents) node root :=
      (directedReachableUnder?_eq_true_iff view owner topological
        decisionParents node root).mp hrootQuery.2
    have hroot' : root ∈ insert source (insert target evidence) := by
      simpa [Finset.mem_insert] using hroot''
    exact ⟨root, by simpa [FiniteBNMoralSeparation.queryRoots] using hroot', hpath⟩
  · rintro ⟨root, hroot, hpath⟩
    have hreachable :
        directedReachableUnder? view owner topological decisionParents node root = true :=
      (directedReachableUnder?_eq_true_iff view owner topological
        decisionParents node root).mpr hpath
    have hroot' : root = source ∨ root = target ∨ root ∈ evidence := by
      simpa [FiniteBNMoralSeparation.queryRoots, Finset.mem_insert] using hroot
    refine ⟨root, graphNode_mem_graphNodeList view owner topological root, ?_⟩
    rw [Bool.and_eq_true]
    exact ⟨decide_eq_true_eq.mpr hroot', hreachable⟩

def ancestralMoralReachableUnder? [DecidableEq Node]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (decisionParents : DecisionParentMap Node)
    (source target : view.GraphNode owner)
    (evidence : Finset (view.GraphNode owner))
    (first second : view.GraphNode owner) : Bool :=
  (graphNodeEnumeration view owner topological).reachable
    (fun left right =>
      ancestralMoralAdjacentUnder? view owner topological decisionParents
        (fun node =>
          ancestralUnder? view owner topological decisionParents source target evidence node =
            true)
        evidence left right)
    first second

theorem ancestralMoralAdjacentUnder?_eq_true_iff' [DecidableEq Node]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (decisionParents : DecisionParentMap Node)
    (source target : view.GraphNode owner)
    (evidence : Finset (view.GraphNode owner))
    (first second : view.GraphNode owner) :
    ancestralMoralAdjacentUnder? view owner topological decisionParents
        (fun node =>
          ancestralUnder? view owner topological decisionParents source target evidence node =
            true)
        evidence first second = true ↔
      FiniteBNMoralSeparation.MoralAdjacent
        (graphParentsUnder view decisionParents) {source} {target} evidence first second := by
  rw [ancestralMoralAdjacentUnder?_eq_true_iff]
  unfold AncestralMoralAdjacentUnder
    FiniteBNMoralSeparation.MoralAdjacent
  constructor
  · rintro ⟨hne, hfirst, hsecond, hafirst, hasecond, hedge⟩
    refine ⟨hne, hfirst, hsecond, ?_, ?_, ?_⟩
    · exact (ancestralUnder?_eq_true_iff view owner topological decisionParents
        source target evidence first).mp hafirst
    · exact (ancestralUnder?_eq_true_iff view owner topological decisionParents
        source target evidence second).mp hasecond
    · rcases hedge with hedge | hedge |
        ⟨child, _, hchild, hfirstChild, hsecondChild⟩
      · exact Or.inl hedge
      · exact Or.inr (Or.inl hedge)
      · exact Or.inr (Or.inr ⟨child,
          (ancestralUnder?_eq_true_iff view owner topological decisionParents
            source target evidence child).mp hchild,
          hfirstChild, hsecondChild⟩)
  · rintro ⟨hne, hfirst, hsecond, hafirst, hasecond, hedge⟩
    refine ⟨hne, hfirst, hsecond, ?_, ?_, ?_⟩
    · exact (ancestralUnder?_eq_true_iff view owner topological decisionParents
        source target evidence first).mpr hafirst
    · exact (ancestralUnder?_eq_true_iff view owner topological decisionParents
        source target evidence second).mpr hasecond
    · rcases hedge with hedge | hedge |
        ⟨child, hchild, hfirstChild, hsecondChild⟩
      · exact Or.inl hedge
      · exact Or.inr (Or.inl hedge)
      · exact Or.inr (Or.inr ⟨child,
          graphNode_mem_graphNodeList view owner topological child,
          (ancestralUnder?_eq_true_iff view owner topological decisionParents
            source target evidence child).mpr hchild,
          hfirstChild, hsecondChild⟩)

theorem ancestralMoralReachableUnder?_eq_true_iff [DecidableEq Node]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (decisionParents : DecisionParentMap Node)
    (source target : view.GraphNode owner)
    (evidence : Finset (view.GraphNode owner))
    (first second : view.GraphNode owner) :
    ancestralMoralReachableUnder? view owner topological decisionParents
        source target evidence first second = true ↔
      Relation.ReflTransGen
        (FiniteBNMoralSeparation.MoralAdjacent
          (graphParentsUnder view decisionParents) {source} {target} evidence)
        first second := by
  unfold ancestralMoralReachableUnder?
  rw [Enumeration.reachable_eq_true_iff]
  constructor
  · intro path
    apply path.lift id
    intro left right adjacent
    exact (ancestralMoralAdjacentUnder?_eq_true_iff' view owner topological
      decisionParents source target evidence left right).mp adjacent
  · intro path
    apply path.lift id
    intro left right adjacent
    exact (ancestralMoralAdjacentUnder?_eq_true_iff' view owner topological
      decisionParents source target evidence left right).mpr adjacent

def dConnectedUnder? [DecidableEq Node]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (decisionParents : DecisionParentMap Node)
    (source target : view.GraphNode owner)
    (evidence : Finset (view.GraphNode owner)) : Bool :=
  (decide (source ∉ evidence ∧ target ∉ evidence)) &&
    ancestralMoralReachableUnder? view owner topological decisionParents
      source target evidence source target

theorem dConnectedUnder?_eq_true_iff [DecidableEq Node]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (decisionParents : DecisionParentMap Node)
    (source target : view.GraphNode owner)
    (evidence : Finset (view.GraphNode owner)) :
    dConnectedUnder? view owner topological decisionParents source target evidence = true ↔
      DConnectedUnder view decisionParents source target evidence := by
  unfold dConnectedUnder? DConnectedUnder
  rw [Bool.and_eq_true]
  constructor
  · rintro ⟨hopen, hpath⟩
    refine ⟨?_, ?_, ?_⟩
    · exact (decide_eq_true_eq.mp hopen).1
    · exact (decide_eq_true_eq.mp hopen).2
    · exact (ancestralMoralReachableUnder?_eq_true_iff view owner topological
        decisionParents source target evidence source target).mp hpath
  · rintro ⟨hsource, htarget, hpath⟩
    refine ⟨decide_eq_true_eq.mpr ⟨hsource, htarget⟩, ?_⟩
    exact (ancestralMoralReachableUnder?_eq_true_iff view owner topological
      decisionParents source target evidence source target).mpr hpath

def edgeAdditionStableAt? [DecidableEq Node]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (pruning : Pruning diagram)
    {owner : Player} (site : DecisionSite diagram owner) : Bool :=
  let decisionParents := Pruning.restoreAllAt pruning site
  let removed := Pruning.missingAt pruning site
  (decide (removed ⊆ decisionParents site.1)) &&
    (List.finRange (view.terms owner).length).all fun term =>
      !isRelevantUtilityTermUnder? view owner topological
          decisionParents site term ||
        (topological.order.filter fun observation =>
          decide (observation ∈ removed)).all fun observation =>
          !dConnectedUnder? view owner topological decisionParents
            (.base observation) (.utility term)
            (conditioningUnder view decisionParents site removed)

theorem edgeAdditionStableAt?_eq_true_iff [DecidableEq Node]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (pruning : Pruning diagram)
    {owner : Player} (site : DecisionSite diagram owner) :
    edgeAdditionStableAt? view topological pruning site = true ↔
      IsEdgeAdditionStableAt view pruning site := by
  unfold edgeAdditionStableAt? IsEdgeAdditionStableAt
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true]
  constructor
  · rintro ⟨hsubset, hterms⟩
    refine ⟨decide_eq_true_eq.mp hsubset, ?_⟩
    intro term hterm observation hobservation hdconnected
    have hcases := hterms term (List.mem_finRange term)
    have htermTrue :=
      (isRelevantUtilityTermUnder?_eq_true_iff view owner topological
        (Pruning.restoreAllAt pruning site) site term).mpr hterm
    rcases hcases with htermFalse | hobservations
    · simp [htermTrue] at htermFalse
    · have hobservationListed : observation ∈ topological.order.filter fun node =>
          decide (node ∈ Pruning.missingAt pruning site) := by
        rw [List.mem_filter]
        exact ⟨topological.complete observation, decide_eq_true_eq.mpr hobservation⟩
      have hobservationFalse := hobservations observation hobservationListed
      have hobservationTrue :=
        (dConnectedUnder?_eq_true_iff view owner topological
          (Pruning.restoreAllAt pruning site) (.base observation) (.utility term)
          (conditioningUnder view (Pruning.restoreAllAt pruning site) site
            (Pruning.missingAt pruning site))).mpr hdconnected
      simp [hobservationTrue] at hobservationFalse
  · rintro ⟨hsubset, hterms⟩
    refine ⟨decide_eq_true_eq.mpr hsubset, ?_⟩
    intro term _
    by_cases htermTrue :
        isRelevantUtilityTermUnder? view owner topological
          (Pruning.restoreAllAt pruning site) site term = true
    · right
      intro observation hobservation
      have hobservation' : observation ∈ Pruning.missingAt pruning site := by
        rw [List.mem_filter] at hobservation
        exact decide_eq_true_eq.mp hobservation.2
      have hconnectedFalse :
          dConnectedUnder? view owner topological
              (Pruning.restoreAllAt pruning site) (.base observation) (.utility term)
              (conditioningUnder view (Pruning.restoreAllAt pruning site) site
                (Pruning.missingAt pruning site)) = false := by
        apply Bool.eq_false_iff.mpr
        intro hconnected
        exact hterms term
          ((isRelevantUtilityTermUnder?_eq_true_iff view owner topological
            (Pruning.restoreAllAt pruning site) site term).mp htermTrue)
          observation hobservation'
          ((dConnectedUnder?_eq_true_iff view owner topological
            (Pruning.restoreAllAt pruning site) (.base observation) (.utility term)
            (conditioningUnder view (Pruning.restoreAllAt pruning site) site
              (Pruning.missingAt pruning site))).mp hconnected)
      simp [hconnectedFalse]
    · left
      have htermFalse := Bool.eq_false_iff.mpr htermTrue
      simp [htermFalse]

def edgeAdditionFixpoint? [DecidableEq Node] [DecidableEq Player]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (players : List Player) (pruning : Pruning diagram) : Bool :=
  players.all fun owner =>
    topological.order.all fun node =>
      if hkind : diagram.kind node = .decision owner then
        edgeAdditionStableAt? view topological pruning
          (⟨node, hkind⟩ : DecisionSite diagram owner)
      else
        true

theorem edgeAdditionFixpoint?_eq_true_iff [DecidableEq Node] [DecidableEq Player]
    (topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents)
    (players : List Player) (hplayers : ∀ owner, owner ∈ players)
    (pruning : Pruning diagram) :
    edgeAdditionFixpoint? view topological players pruning = true ↔
      IsEdgeAdditionFixpoint view pruning := by
  unfold edgeAdditionFixpoint? IsEdgeAdditionFixpoint
  simp only [List.all_eq_true]
  constructor
  · intro h owner site
    have howner := h owner (hplayers owner)
    have hsite := howner site.1 (topological.complete site.1)
    simp only [dif_pos site.2] at hsite
    exact (edgeAdditionStableAt?_eq_true_iff view topological pruning site).mp hsite
  · intro h owner _ node _
    if hkind : diagram.kind node = .decision owner then
      simp only [dif_pos hkind]
      exact (edgeAdditionStableAt?_eq_true_iff view topological pruning
        (⟨node, hkind⟩ : DecisionSite diagram owner)).mpr
        (h owner ⟨node, hkind⟩)
    else
      simp only [dif_neg hkind]

end UtilityView

/-! ## Executable control -/

namespace ExecutableCheckerControl

private inductive TestNode
  | site
  deriving DecidableEq

private def testParents (_ : TestNode) : Finset TestNode := ∅

private def testTopological : GameTheory.Math.DAG.TopologicalOrder testParents where
  order := [.site]
  nodup := by decide
  complete node := by cases node; simp
  respects := by simp [testParents]

private def testDiagram : Structure Unit TestNode where
  kind _ := .decision ()
  parents := testParents
  observedParents := testParents
  Value _ := Bool
  observed_sub _ := Finset.Subset.rfl
  observed_eq_of_chance node hchance := by
    cases node
    simp at hchance
  acyclic := GameTheory.Math.DAG.acyclic_of_topologicalOrder testTopological

private def testSemantics : Semantics testDiagram where
  defaultValue _ := false
  chanceLaw node hchance := by
    cases node
    simp [testDiagram] at hchance
  utility _ _ := 0

private def testView : UtilityView testSemantics where
  terms _ := []
  utility_eq_sum _ _ := by simp [testSemantics]

private def testPruning : Pruning testDiagram where
  kept _ := ∅
  kept_sub_observed _ := Finset.Subset.rfl

/-- The complete checker reduces to `true` on a one-decision executable MAID. -/
example : UtilityView.edgeAdditionFixpoint?
    testView testTopological [()] testPruning = true := by
  decide

end ExecutableCheckerControl

end GameTheory.Experimental.PostArchitecture.MAIDPruningFixpointGraph
