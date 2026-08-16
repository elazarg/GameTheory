/-
# EXP-104: finite ancestral-moral component partitions

This file turns ancestral-moral separation into explicit finite coordinate
regions and a disjoint partition of ancestral factor indices.  Components not
connected to the first query set are assigned deterministically to the right
region.  The result is purely graph-theoretic; no probabilistic independence
claim is made here.
-/

import GameTheory.Experimental.PostArchitecture.FiniteBNFactorScopes
import GameTheory.Experimental.PostArchitecture.FiniteBNMoralSeparation

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.FiniteBNMoralComponents

open GameTheory.Experimental.PostArchitecture.FiniteBNFactorScopes
open GameTheory.Experimental.PostArchitecture.FiniteBNMoralSeparation

universe uNode

variable {Node : Type uNode}

/-- The finite indices of factors in the ancestral query graph. -/
def ancestralFactors [Fintype Node] [DecidableEq Node]
    (parents : Node → Finset Node)
    (first second evidence : Finset Node) : Finset Node := by
  classical
  exact Finset.univ.filter
    (InAncestralClosure parents first second evidence)

/-- Ancestral coordinates remaining after the evidence vertices are deleted. -/
def openAncestralRegion [Fintype Node] [DecidableEq Node]
    (parents : Node → Finset Node)
    (first second evidence : Finset Node) : Finset Node :=
  ancestralFactors parents first second evidence \ evidence

/-- An open ancestral coordinate belongs to the left region exactly when its
moral component meets the first query set. -/
def leftRegion [Fintype Node] [DecidableEq Node]
    (parents : Node → Finset Node)
    (first second evidence : Finset Node) : Finset Node := by
  classical
  exact (openAncestralRegion parents first second evidence).filter fun node =>
    ∃ source ∈ first, Connected parents first second evidence source node

/-- Every remaining open ancestral component, including every neutral
component, is assigned to the right region. -/
def rightRegion [Fintype Node] [DecidableEq Node]
    (parents : Node → Finset Node)
    (first second evidence : Finset Node) : Finset Node :=
  openAncestralRegion parents first second evidence \
    leftRegion parents first second evidence

/-- An ancestral factor is assigned left when its scope meets the left open
region.  A scope with no open coordinates is therefore assigned right. -/
def leftFactors [Fintype Node] [DecidableEq Node]
    (parents : Node → Finset Node)
    (first second evidence : Finset Node) : Finset Node := by
  classical
  exact (ancestralFactors parents first second evidence).filter fun child =>
    ∃ coordinate ∈ factorScope parents child,
      coordinate ∈ leftRegion parents first second evidence

/-- The complementary ancestral factor indices. -/
def rightFactors [Fintype Node] [DecidableEq Node]
    (parents : Node → Finset Node)
    (first second evidence : Finset Node) : Finset Node :=
  ancestralFactors parents first second evidence \
    leftFactors parents first second evidence

theorem mem_ancestralFactors_iff [Fintype Node] [DecidableEq Node]
    (parents : Node → Finset Node) (first second evidence : Finset Node)
    (node : Node) :
    node ∈ ancestralFactors parents first second evidence ↔
      InAncestralClosure parents first second evidence node := by
  classical
  simp [ancestralFactors]

theorem mem_openAncestralRegion_iff [Fintype Node] [DecidableEq Node]
    (parents : Node → Finset Node) (first second evidence : Finset Node)
    (node : Node) :
    node ∈ openAncestralRegion parents first second evidence ↔
      InAncestralClosure parents first second evidence node ∧
        node ∉ evidence := by
  classical
  simp [openAncestralRegion, mem_ancestralFactors_iff]

theorem mem_leftRegion_iff [Fintype Node] [DecidableEq Node]
    (parents : Node → Finset Node) (first second evidence : Finset Node)
    (node : Node) :
    node ∈ leftRegion parents first second evidence ↔
      node ∈ openAncestralRegion parents first second evidence ∧
        ∃ source ∈ first,
          Connected parents first second evidence source node := by
  classical
  simp [leftRegion]

theorem regions_disjoint [Fintype Node] [DecidableEq Node]
    (parents : Node → Finset Node) (first second evidence : Finset Node) :
    Disjoint (leftRegion parents first second evidence)
      (rightRegion parents first second evidence) := by
  rw [Finset.disjoint_left]
  intro node hleft hright
  exact (Finset.mem_sdiff.mp hright).2 hleft

theorem regions_cover_openAncestral [Fintype Node] [DecidableEq Node]
    (parents : Node → Finset Node) (first second evidence : Finset Node) :
    leftRegion parents first second evidence ∪
        rightRegion parents first second evidence =
      openAncestralRegion parents first second evidence := by
  apply Finset.Subset.antisymm
  · intro node hnode
    rcases Finset.mem_union.mp hnode with hleft | hright
    · exact (mem_leftRegion_iff parents first second evidence node).mp hleft |>.1
    · exact (Finset.mem_sdiff.mp hright).1
  · intro node hnode
    by_cases hleft : node ∈ leftRegion parents first second evidence
    · exact Finset.mem_union_left _ hleft
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hnode, hleft⟩)

theorem factors_disjoint [Fintype Node] [DecidableEq Node]
    (parents : Node → Finset Node) (first second evidence : Finset Node) :
    Disjoint (leftFactors parents first second evidence)
      (rightFactors parents first second evidence) := by
  rw [Finset.disjoint_left]
  intro node hleft hright
  exact (Finset.mem_sdiff.mp hright).2 hleft

theorem factors_cover_ancestral [Fintype Node] [DecidableEq Node]
    (parents : Node → Finset Node) (first second evidence : Finset Node) :
    leftFactors parents first second evidence ∪
        rightFactors parents first second evidence =
      ancestralFactors parents first second evidence := by
  apply Finset.Subset.antisymm
  · intro node hnode
    rcases Finset.mem_union.mp hnode with hleft | hright
    · exact (Finset.mem_filter.mp hleft).1
    · exact (Finset.mem_sdiff.mp hright).1
  · intro node hnode
    by_cases hleft : node ∈ leftFactors parents first second evidence
    · exact Finset.mem_union_left _ hleft
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hnode, hleft⟩)

theorem first_mem_leftRegion [Fintype Node] [DecidableEq Node]
    (parents : Node → Finset Node) (first second evidence : Finset Node)
    {node : Node} (hnode : node ∈ first) (hopen : node ∉ evidence) :
    node ∈ leftRegion parents first second evidence := by
  rw [mem_leftRegion_iff]
  constructor
  · rw [mem_openAncestralRegion_iff]
    exact ⟨⟨node, by simp [queryRoots, hnode], Relation.ReflTransGen.refl⟩,
      hopen⟩
  · exact ⟨node, hnode,
      ⟨hopen, hopen, Relation.ReflTransGen.refl⟩⟩

theorem second_mem_rightRegion_of_separates
    [Fintype Node] [DecidableEq Node]
    (parents : Node → Finset Node) (first second evidence : Finset Node)
    (hseparates : Separates parents first second evidence)
    {node : Node} (hnode : node ∈ second) (hopen : node ∉ evidence) :
    node ∈ rightRegion parents first second evidence := by
  apply Finset.mem_sdiff.mpr
  constructor
  · rw [mem_openAncestralRegion_iff]
    exact ⟨⟨node, by simp [queryRoots, hnode], Relation.ReflTransGen.refl⟩,
      hopen⟩
  · intro hleft
    obtain ⟨_, source, hsource, hconnected⟩ :=
      (mem_leftRegion_iff parents first second evidence node).mp hleft
    exact hseparates source hsource node hnode hconnected

private theorem factorScope_mem_ancestral
    [DecidableEq Node]
    (parents : Node → Finset Node) (first second evidence : Finset Node)
    {child coordinate : Node}
    (hchild : InAncestralClosure parents first second evidence child)
    (hcoordinate : coordinate ∈ factorScope parents child) :
    InAncestralClosure parents first second evidence coordinate := by
  rcases Finset.mem_insert.mp hcoordinate with rfl | hparent
  · exact hchild
  · exact parent_mem_ancestralClosure hchild hparent

theorem leftFactor_scope_subset [Fintype Node] [DecidableEq Node]
    (parents : Node → Finset Node) (first second evidence : Finset Node)
    {child : Node}
    (hchild : child ∈ leftFactors parents first second evidence) :
    factorScope parents child ⊆
      leftRegion parents first second evidence ∪ evidence := by
  classical
  have hchildAncestral :
      InAncestralClosure parents first second evidence child :=
    (mem_ancestralFactors_iff parents first second evidence child).mp
      (Finset.mem_filter.mp hchild).1
  obtain ⟨anchor, hanchorScope, hanchorLeft⟩ :=
    (Finset.mem_filter.mp hchild).2
  have hanchorOpen : anchor ∉ evidence :=
    ((mem_openAncestralRegion_iff parents first second evidence anchor).mp
      ((mem_leftRegion_iff parents first second evidence anchor).mp
        hanchorLeft).1).2
  intro coordinate hcoordinate
  by_cases hcoordinateEvidence : coordinate ∈ evidence
  · exact Finset.mem_union_right _ hcoordinateEvidence
  · apply Finset.mem_union_left
    rw [mem_leftRegion_iff]
    constructor
    · rw [mem_openAncestralRegion_iff]
      exact ⟨factorScope_mem_ancestral parents first second evidence
        hchildAncestral hcoordinate, hcoordinateEvidence⟩
    · obtain ⟨_, source, hsource, hsourceAnchor⟩ :=
        (mem_leftRegion_iff parents first second evidence anchor).mp hanchorLeft
      refine ⟨source, hsource, ?_⟩
      rcases hsourceAnchor with ⟨hsourceOpen, _, hpath⟩
      by_cases heq : anchor = coordinate
      · subst coordinate
        exact ⟨hsourceOpen, hanchorOpen, hpath⟩
      · have hedge := factorScope_pairwise_moralAdjacent hchildAncestral
          hanchorScope hcoordinate heq hanchorOpen hcoordinateEvidence
        exact ⟨hsourceOpen, hcoordinateEvidence,
          hpath.trans (Relation.ReflTransGen.single hedge)⟩

theorem rightFactor_scope_subset [Fintype Node] [DecidableEq Node]
    (parents : Node → Finset Node) (first second evidence : Finset Node)
    {child : Node}
    (hchild : child ∈ rightFactors parents first second evidence) :
    factorScope parents child ⊆
      rightRegion parents first second evidence ∪ evidence := by
  classical
  have hchildAncestral :
      InAncestralClosure parents first second evidence child :=
    (mem_ancestralFactors_iff parents first second evidence child).mp
      (Finset.mem_sdiff.mp hchild).1
  have hchildNotLeft :
      child ∉ leftFactors parents first second evidence :=
    (Finset.mem_sdiff.mp hchild).2
  intro coordinate hcoordinate
  by_cases hcoordinateEvidence : coordinate ∈ evidence
  · exact Finset.mem_union_right _ hcoordinateEvidence
  · apply Finset.mem_union_left
    apply Finset.mem_sdiff.mpr
    constructor
    · rw [mem_openAncestralRegion_iff]
      exact ⟨factorScope_mem_ancestral parents first second evidence
        hchildAncestral hcoordinate, hcoordinateEvidence⟩
    · intro hcoordinateLeft
      apply hchildNotLeft
      apply Finset.mem_filter.mpr
      exact ⟨(Finset.mem_sdiff.mp hchild).1,
        ⟨coordinate, hcoordinate, hcoordinateLeft⟩⟩

/-- The graph-side partition certificate produced by ancestral-moral
separation.  Neutral open components are included on the right. -/
theorem exists_moral_factor_partition_of_separates
    [Fintype Node] [DecidableEq Node]
    (parents : Node → Finset Node) (first second evidence : Finset Node)
    (hseparates : Separates parents first second evidence) :
    Disjoint (leftRegion parents first second evidence)
        (rightRegion parents first second evidence) ∧
      leftRegion parents first second evidence ∪
          rightRegion parents first second evidence =
        openAncestralRegion parents first second evidence ∧
      Disjoint (leftFactors parents first second evidence)
        (rightFactors parents first second evidence) ∧
      leftFactors parents first second evidence ∪
          rightFactors parents first second evidence =
        ancestralFactors parents first second evidence ∧
      (∀ child ∈ leftFactors parents first second evidence,
        factorScope parents child ⊆
          leftRegion parents first second evidence ∪ evidence) ∧
      (∀ child ∈ rightFactors parents first second evidence,
        factorScope parents child ⊆
          rightRegion parents first second evidence ∪ evidence) ∧
      (∀ node ∈ first, node ∉ evidence →
        node ∈ leftRegion parents first second evidence) ∧
      ∀ node ∈ second, node ∉ evidence →
        node ∈ rightRegion parents first second evidence := by
  exact ⟨regions_disjoint parents first second evidence,
    regions_cover_openAncestral parents first second evidence,
    factors_disjoint parents first second evidence,
    factors_cover_ancestral parents first second evidence,
    fun _ hchild => leftFactor_scope_subset parents first second evidence hchild,
    fun _ hchild => rightFactor_scope_subset parents first second evidence hchild,
    fun _ hnode => first_mem_leftRegion parents first second evidence hnode,
    fun _ hnode => second_mem_rightRegion_of_separates
      parents first second evidence hseparates hnode⟩

end GameTheory.Experimental.PostArchitecture.FiniteBNMoralComponents
