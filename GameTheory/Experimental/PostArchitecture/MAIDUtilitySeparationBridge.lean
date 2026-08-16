/-
# EXP-105: MAID utility-separation graph bridge

The MAID requisite-observation predicate and generic finite-BN separation use
the same owner-specific parent graph.  This module identifies their singleton
query presentations and supplies only the disjointness facts needed by a later
global-Markov application.  It makes no semantic or reduction claim.
-/

import GameTheory.Experimental.PostArchitecture.FiniteBNMoralSeparation
import GameTheory.Experimental.PostArchitecture.MAIDRequisiteObservation

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.MAIDUtilitySeparationBridge

open GameTheory.Languages.MAID
open GameTheory.Experimental.PostArchitecture.MAIDRequisiteObservation

universe uPlayer uNode

variable {Player : Type uPlayer} {Node : Type uNode}
variable {diagram : Structure Player Node} {semantics : Semantics diagram}

variable (view : UtilityView semantics)

/-- The canonical graph query corresponding to a set of removed base
observations. -/
def removedGraphNodes [DecidableEq Node] (owner : Player)
    (removed : Finset Node) : Finset (view.GraphNode owner) :=
  removed.image UtilityView.GraphNode.base

/-- The two directed-edge presentations are definitionally the same. -/
theorem directedEdge_iff [DecidableEq Node] {owner : Player}
    (parent child : view.GraphNode owner) :
    view.DirectedEdge parent child ↔
      FiniteBNMoralSeparation.DirectedEdge view.graphParents parent child :=
  Iff.rfl

/-- Directed ancestry is unchanged by moving to the generic graph API. -/
theorem ancestorOrSelf_iff [DecidableEq Node] {owner : Player}
    (ancestor descendant : view.GraphNode owner) :
    view.AncestorOrSelf ancestor descendant ↔
      FiniteBNMoralSeparation.AncestorOrSelf view.graphParents ancestor
        descendant :=
  Iff.rfl

/-- The MAID source/target root spelling equals the generic pair of singleton
query sets. -/
theorem inAncestralClosure_iff [DecidableEq Node] {owner : Player}
    (source target node : view.GraphNode owner)
    (evidence : Finset (view.GraphNode owner)) :
    view.InAncestralClosure source target evidence node ↔
      FiniteBNMoralSeparation.InAncestralClosure view.graphParents
        {source} {target} evidence node := by
  constructor
  · rintro ⟨root, hroot, path⟩
    exact ⟨root, by simpa [FiniteBNMoralSeparation.queryRoots] using hroot,
      path⟩
  · rintro ⟨root, hroot, path⟩
    exact ⟨root, by simpa [FiniteBNMoralSeparation.queryRoots] using hroot,
      path⟩

/-- Moral adjacency is identical after expressing the endpoints as singleton
query sets in the generic API. -/
theorem moralAdjacent_iff [DecidableEq Node] {owner : Player}
    (source target : view.GraphNode owner)
    (evidence : Finset (view.GraphNode owner))
    (left right : view.GraphNode owner) :
    view.MoralAdjacent source target evidence left right ↔
      FiniteBNMoralSeparation.MoralAdjacent view.graphParents
        {source} {target} evidence left right := by
  simp only [UtilityView.MoralAdjacent,
    FiniteBNMoralSeparation.MoralAdjacent, directedEdge_iff,
    inAncestralClosure_iff]

private theorem moralAdjacent_relation_eq [DecidableEq Node]
    {owner : Player} (source target : view.GraphNode owner)
    (evidence : Finset (view.GraphNode owner)) :
    view.MoralAdjacent source target evidence =
      FiniteBNMoralSeparation.MoralAdjacent view.graphParents
        {source} {target} evidence := by
  funext left right
  apply propext
  exact moralAdjacent_iff view source target evidence left right

/-- `DConnected` is the singleton-query specialization of generic ancestral-
moral connectivity, over the same `view.graphParents`. -/
theorem dConnected_iff_connected [DecidableEq Node] {owner : Player}
    (source target : view.GraphNode owner)
    (evidence : Finset (view.GraphNode owner)) :
    view.DConnected source target evidence ↔
      FiniteBNMoralSeparation.Connected view.graphParents
        {source} {target} evidence source target := by
  unfold UtilityView.DConnected FiniteBNMoralSeparation.Connected
  rw [moralAdjacent_relation_eq view source target evidence]

/-- Failure of MAID d-connection gives the singleton setwise separation
required by the generic finite-BN theorem. -/
theorem separates_singletons_of_not_dConnected [DecidableEq Node]
    {owner : Player} (source target : view.GraphNode owner)
    (evidence : Finset (view.GraphNode owner))
    (hnot : ¬ view.DConnected source target evidence) :
    FiniteBNMoralSeparation.Separates view.graphParents
      {source} {target} evidence := by
  intro left hleft right hright
  have hleftEq : left = source := by simpa using hleft
  have hrightEq : right = target := by simpa using hright
  subst left
  subst right
  intro connected
  exact hnot ((dConnected_iff_connected view source target evidence).2 connected)

private theorem removedBase_ancestor_decision [DecidableEq Node]
    {owner : Player} (site : DecisionSite diagram owner)
    (removed : Finset Node) (hsubset : removed ⊆ diagram.observedParents site.1)
    (observation : Node) (hremoved : observation ∈ removed) :
    FiniteBNMoralSeparation.AncestorOrSelf
      (view.graphParents (owner := owner))
      (.base observation : view.GraphNode owner)
      (.base site.1 : view.GraphNode owner) := by
  apply Relation.ReflTransGen.single
  simp [FiniteBNMoralSeparation.DirectedEdge, UtilityView.graphParents,
    effectiveParents, site.2, hsubset hremoved]

private theorem inAncestralClosure_removed_iff_singleton [DecidableEq Node]
    {owner : Player} (site : DecisionSite diagram owner)
    (removed : Finset Node) (hsubset : removed ⊆ diagram.observedParents site.1)
    (observation : Node) (hremoved : observation ∈ removed)
    (term : view.UtilitySite owner)
    (evidence : Finset (view.GraphNode owner))
    (hdecision : (.base site.1 : view.GraphNode owner) ∈ evidence)
    (node : view.GraphNode owner) :
    FiniteBNMoralSeparation.InAncestralClosure view.graphParents
        (removedGraphNodes view owner removed) {.utility term} evidence node ↔
      FiniteBNMoralSeparation.InAncestralClosure view.graphParents
        {.base observation} {.utility term} evidence node := by
  constructor
  · rintro ⟨root, hroot, path⟩
    have hcases : root = .utility term ∨
        root ∈ removedGraphNodes view owner removed ∨ root ∈ evidence := by
      simpa [FiniteBNMoralSeparation.queryRoots] using hroot
    rcases hcases with htarget | hremovedRoot | hevidence
    · exact ⟨root, by simp [FiniteBNMoralSeparation.queryRoots, htarget], path⟩
    · obtain ⟨other, hother, rfl⟩ := Finset.mem_image.mp hremovedRoot
      refine ⟨.base site.1, ?_, path.trans
        (removedBase_ancestor_decision view site removed hsubset other hother)⟩
      simp [FiniteBNMoralSeparation.queryRoots, hdecision]
    · exact ⟨root, by simp [FiniteBNMoralSeparation.queryRoots, hevidence], path⟩
  · rintro ⟨root, hroot, path⟩
    refine ⟨root, ?_, path⟩
    have hcases : root = .base observation ∨
        root = .utility term ∨ root ∈ evidence := by
      simpa [FiniteBNMoralSeparation.queryRoots] using hroot
    rcases hcases with hsource | htarget | hevidence
    · subst root
      simp [FiniteBNMoralSeparation.queryRoots, removedGraphNodes, hremoved]
    · simp [FiniteBNMoralSeparation.queryRoots, htarget]
    · simp [FiniteBNMoralSeparation.queryRoots, hevidence]

private theorem moralAdjacent_removed_relation_eq [DecidableEq Node]
    {owner : Player} (site : DecisionSite diagram owner)
    (removed : Finset Node) (hsubset : removed ⊆ diagram.observedParents site.1)
    (observation : Node) (hremoved : observation ∈ removed)
    (term : view.UtilitySite owner)
    (evidence : Finset (view.GraphNode owner))
    (hdecision : (.base site.1 : view.GraphNode owner) ∈ evidence) :
    FiniteBNMoralSeparation.MoralAdjacent view.graphParents
        (removedGraphNodes view owner removed) {.utility term} evidence =
      view.MoralAdjacent (.base observation) (.utility term) evidence := by
  calc
    FiniteBNMoralSeparation.MoralAdjacent view.graphParents
        (removedGraphNodes view owner removed) {.utility term} evidence =
        FiniteBNMoralSeparation.MoralAdjacent view.graphParents
          {.base observation} {.utility term} evidence := by
      funext left right
      apply propext
      simp only [FiniteBNMoralSeparation.MoralAdjacent,
        inAncestralClosure_removed_iff_singleton view site removed hsubset
          observation hremoved term evidence hdecision]
    _ = view.MoralAdjacent (.base observation) (.utility term) evidence :=
      (moralAdjacent_relation_eq view (.base observation) (.utility term)
        evidence).symm

/-- Set-valued graphical ignorability is exact generic setwise separation for
the whole removed base-coordinate query and one relevant utility leaf. -/
theorem separates_removedGraphNodes_of_areGraphicallyIgnorable
    [DecidableEq Node] {owner : Player}
    (site : DecisionSite diagram owner) (removed : Finset Node)
    (hignore : view.AreGraphicallyIgnorable site removed)
    (term : view.UtilitySite owner)
    (hrelevant : view.IsRelevantUtilityTerm site term) :
    FiniteBNMoralSeparation.Separates view.graphParents
      (removedGraphNodes view owner removed) {.utility term}
      (view.observationConditioningSet site removed) := by
  intro source hsource target htarget
  obtain ⟨observation, hremoved, rfl⟩ := Finset.mem_image.mp hsource
  have htargetEq : target = .utility term := by simpa using htarget
  subst target
  rintro ⟨hsourceOpen, htargetOpen, path⟩
  have hdecision :
      (.base site.1 : view.GraphNode owner) ∈
        view.observationConditioningSet site removed := by
    simp [UtilityView.observationConditioningSet]
  rw [moralAdjacent_removed_relation_eq view site removed hignore.1
    observation hremoved term _ hdecision] at path
  exact hignore.2 term hrelevant observation hremoved
    ⟨hsourceOpen, htargetOpen, path⟩

/-- A base query and a distinct-constructor utility query are disjoint. -/
theorem base_utility_singletons_disjoint [DecidableEq Node]
    {owner : Player} (observation : Node) (term : view.UtilitySite owner) :
    Disjoint
      ({.base observation} : Finset (view.GraphNode owner))
      ({.utility term} : Finset (view.GraphNode owner)) := by
  simp

/-- A utility singleton is disjoint from observation conditioning because the
latter contains only base graph nodes. -/
theorem utility_conditioning_disjoint [DecidableEq Node]
    {owner : Player} (site : DecisionSite diagram owner)
    (removed : Finset Node) (term : view.UtilitySite owner) :
    Disjoint
      ({.utility term} : Finset (view.GraphNode owner))
      (view.observationConditioningSet site removed) := by
  simp [UtilityView.observationConditioningSet]

/-- The whole removed base-node query is disjoint from a utility singleton. -/
theorem removedGraphNodes_utility_disjoint [DecidableEq Node]
    {owner : Player} (removed : Finset Node) (term : view.UtilitySite owner) :
    Disjoint (removedGraphNodes view owner removed)
      ({.utility term} : Finset (view.GraphNode owner)) := by
  simp [removedGraphNodes]

/-- A removed observation is absent from the conditioning set.  Membership in
the declared observations rules out equality with the decision by acyclicity.
-/
theorem base_conditioning_disjoint [DecidableEq Node]
    {owner : Player} (site : DecisionSite diagram owner)
    (removed : Finset Node) (observation : Node)
    (hremoved : observation ∈ removed)
    (hsubset : removed ⊆ diagram.observedParents site.1) :
    Disjoint
      ({.base observation} : Finset (view.GraphNode owner))
      (view.observationConditioningSet site removed) := by
  have hparent : observation ∈ diagram.parents site.1 :=
    diagram.observed_sub site.1 (hsubset hremoved)
  have hne : observation ≠ site.1 := by
    intro equality
    subst observation
    exact diagram.acyclic site.1 (Relation.TransGen.single hparent)
  simp [UtilityView.observationConditioningSet, hremoved, hne]

/-- Every removed base node is absent from the common conditioning set. -/
theorem removedGraphNodes_conditioning_disjoint [DecidableEq Node]
    {owner : Player} (site : DecisionSite diagram owner)
    (removed : Finset Node)
    (hsubset : removed ⊆ diagram.observedParents site.1) :
    Disjoint (removedGraphNodes view owner removed)
      (view.observationConditioningSet site removed) := by
  rw [Finset.disjoint_left]
  intro graphNode hgraphNode hconditioned
  obtain ⟨observation, hremoved, rfl⟩ := Finset.mem_image.mp hgraphNode
  have hsingle :=
    base_conditioning_disjoint view site removed observation hremoved hsubset
  exact Finset.disjoint_left.mp hsingle (by simp) hconditioned

/-- The exact set-valued utility query has all three disjointness premises
required by finite global Markov. -/
theorem removed_query_disjointness [DecidableEq Node]
    {owner : Player} (site : DecisionSite diagram owner)
    (removed : Finset Node) (term : view.UtilitySite owner)
    (hsubset : removed ⊆ diagram.observedParents site.1) :
    Disjoint (removedGraphNodes view owner removed)
        ({.utility term} : Finset (view.GraphNode owner)) ∧
      Disjoint (removedGraphNodes view owner removed)
        (view.observationConditioningSet site removed) ∧
      Disjoint ({.utility term} : Finset (view.GraphNode owner))
        (view.observationConditioningSet site removed) :=
  ⟨removedGraphNodes_utility_disjoint view removed term,
    removedGraphNodes_conditioning_disjoint view site removed hsubset,
    utility_conditioning_disjoint view site removed term⟩

/-- The exact singleton utility query used for one removed observation has
all three disjointness premises required by finite global Markov. -/
theorem singleton_query_disjointness [DecidableEq Node]
    {owner : Player} (site : DecisionSite diagram owner)
    (removed : Finset Node) (observation : Node)
    (term : view.UtilitySite owner)
    (hremoved : observation ∈ removed)
    (hsubset : removed ⊆ diagram.observedParents site.1) :
    Disjoint
        ({.base observation} : Finset (view.GraphNode owner))
        ({.utility term} : Finset (view.GraphNode owner)) ∧
      Disjoint
        ({.base observation} : Finset (view.GraphNode owner))
        (view.observationConditioningSet site removed) ∧
      Disjoint
        ({.utility term} : Finset (view.GraphNode owner))
        (view.observationConditioningSet site removed) :=
  ⟨base_utility_singletons_disjoint view observation term,
    base_conditioning_disjoint view site removed observation hremoved hsubset,
    utility_conditioning_disjoint view site removed term⟩

/-- Existing set-valued graphical ignorability supplies generic separation for
each relevant utility term and each removed observation. -/
theorem separates_of_areGraphicallyIgnorable [DecidableEq Node]
    {owner : Player} (site : DecisionSite diagram owner)
    (removed : Finset Node) (hignore : view.AreGraphicallyIgnorable site removed)
    (term : view.UtilitySite owner)
    (hrelevant : view.IsRelevantUtilityTerm site term)
    (observation : Node) (hremoved : observation ∈ removed) :
    FiniteBNMoralSeparation.Separates view.graphParents
      {.base observation} {.utility term}
      (view.observationConditioningSet site removed) :=
  separates_singletons_of_not_dConnected view _ _ _
    (hignore.2 term hrelevant observation hremoved)

end GameTheory.Experimental.PostArchitecture.MAIDUtilitySeparationBridge
