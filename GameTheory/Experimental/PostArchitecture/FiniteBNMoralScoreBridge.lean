/-
# EXP-104: ancestral-moral score certificates

This module connects the finite ancestral-moral component partition to the
score interface used by latent finite summation.  It makes no probability or
conditional-independence claim.
-/

import GameTheory.Experimental.PostArchitecture.FiniteBNMoralComponents
import GameTheory.Experimental.PostArchitecture.FiniteBNScoreAssembly

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.FiniteBNMoralScoreBridge

open GameTheory.Experimental.PostArchitecture.FiniteBNFactorScopes
open GameTheory.Experimental.PostArchitecture.FiniteBNGlobalMarkov
open GameTheory.Experimental.PostArchitecture.FiniteBNMoralComponents
open GameTheory.Experimental.PostArchitecture.FiniteBNMoralSeparation
open GameTheory.Experimental.PostArchitecture.FiniteBNScoreAssembly

universe uNode uValue

variable {Node : Type uNode} (Value : Node → Type uValue)

/-- Open left-region coordinates not fixed by the query. -/
def latentLeft [Fintype Node] [DecidableEq Node]
    (parents : Node → Finset Node)
    (first second evidence : Finset Node) : Finset Node :=
  leftRegion parents first second evidence \
    fixedCoordinates first second evidence

/-- Open right-region coordinates not fixed by the query. -/
def latentRight [Fintype Node] [DecidableEq Node]
    (parents : Node → Finset Node)
    (first second evidence : Finset Node) : Finset Node :=
  rightRegion parents first second evidence \
    fixedCoordinates first second evidence

private theorem latent_cover
    [Fintype Node] [DecidableEq Node]
    (parents : Node → Finset Node)
    (first second evidence : Finset Node) :
    ancestralFactors parents first second evidence \
        fixedCoordinates first second evidence =
      latentLeft parents first second evidence ∪
        latentRight parents first second evidence := by
  have hregions := regions_cover_openAncestral parents first second evidence
  ext node
  constructor
  · intro hnode
    have hancestral := (Finset.mem_sdiff.mp hnode).1
    have hnotFixed := (Finset.mem_sdiff.mp hnode).2
    have hnotEvidence : node ∉ evidence := by
      intro hevidence
      apply hnotFixed
      simp [fixedCoordinates, hevidence]
    have hopen :
        node ∈ openAncestralRegion parents first second evidence := by
      exact Finset.mem_sdiff.mpr ⟨hancestral, hnotEvidence⟩
    have hregion :
        node ∈ leftRegion parents first second evidence ∪
          rightRegion parents first second evidence := by
      rw [hregions]
      exact hopen
    rcases Finset.mem_union.mp hregion with hleft | hright
    · exact Finset.mem_union_left _
        (Finset.mem_sdiff.mpr ⟨hleft, hnotFixed⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_sdiff.mpr ⟨hright, hnotFixed⟩)
  · intro hnode
    rcases Finset.mem_union.mp hnode with hleft | hright
    · have hleft' := Finset.mem_sdiff.mp hleft
      have hopen :
          node ∈ openAncestralRegion parents first second evidence := by
        rw [← hregions]
        exact Finset.mem_union_left _ hleft'.1
      exact Finset.mem_sdiff.mpr
        ⟨(Finset.mem_sdiff.mp hopen).1, hleft'.2⟩
    · have hright' := Finset.mem_sdiff.mp hright
      have hopen :
          node ∈ openAncestralRegion parents first second evidence := by
        rw [← hregions]
        exact Finset.mem_union_right _ hright'.1
      exact Finset.mem_sdiff.mpr
        ⟨(Finset.mem_sdiff.mp hopen).1, hright'.2⟩

/-- Pairwise-disjoint query blocks give the five-way coordinate partition
required by score assembly. -/
theorem scorePartition
    [Fintype Node] [DecidableEq Node]
    (parents : Node → Finset Node)
    (first second evidence : Finset Node)
    (hfirstSecond : Disjoint first second)
    (hfirstEvidence : Disjoint first evidence)
    (hsecondEvidence : Disjoint second evidence) :
    ScorePartition first second evidence
      (ancestralFactors parents first second evidence)
      (latentLeft parents first second evidence)
      (latentRight parents first second evidence) where
  first_second := hfirstSecond
  first_evidence := hfirstEvidence
  second_evidence := hsecondEvidence
  fixed_subset := by
    intro node hnode
    apply queryRoots_subset_ancestralFactors parents first second evidence
    simpa [fixedCoordinates, queryRoots] using hnode
  latent :=
    { left_right :=
        (regions_disjoint parents first second evidence).mono
          Finset.sdiff_subset Finset.sdiff_subset
      latent_cover := latent_cover parents first second evidence }

private theorem leftRegion_subset_coordinates
    [Fintype Node] [DecidableEq Node]
    (parents : Node → Finset Node)
    (first second evidence : Finset Node)
    (hseparates : Separates parents first second evidence) :
    leftRegion parents first second evidence ⊆
      leftCoordinates first evidence
        (latentLeft parents first second evidence) := by
  intro node hleft
  by_cases hfirst : node ∈ first
  · simp [leftCoordinates, hfirst]
  have hopen :=
    (mem_leftRegion_iff parents first second evidence node).mp hleft |>.1
  have hnotEvidence : node ∉ evidence := (Finset.mem_sdiff.mp hopen).2
  have hnotSecond : node ∉ second := by
    intro hsecond
    have hright := second_mem_rightRegion_of_separates
      parents first second evidence hseparates hsecond hnotEvidence
    exact (Finset.disjoint_left.mp
      (regions_disjoint parents first second evidence)) hleft hright
  have hnotFixed : node ∉ fixedCoordinates first second evidence := by
    simp [fixedCoordinates, hfirst, hnotSecond, hnotEvidence]
  have hlatent : node ∈ latentLeft parents first second evidence :=
    Finset.mem_sdiff.mpr ⟨hleft, hnotFixed⟩
  simp [leftCoordinates, hlatent]

private theorem rightRegion_subset_coordinates
    [Fintype Node] [DecidableEq Node]
    (parents : Node → Finset Node)
    (first second evidence : Finset Node) :
    rightRegion parents first second evidence ⊆
      rightCoordinates second evidence
        (latentRight parents first second evidence) := by
  intro node hright
  by_cases hsecond : node ∈ second
  · simp [rightCoordinates, hsecond]
  have hopen := (Finset.mem_sdiff.mp hright).1
  have hnotEvidence : node ∉ evidence := (Finset.mem_sdiff.mp hopen).2
  have hnotFirst : node ∉ first := by
    intro hfirst
    have hleft := first_mem_leftRegion
      parents first second evidence hfirst hnotEvidence
    exact (Finset.disjoint_left.mp
      (regions_disjoint parents first second evidence)) hleft hright
  have hnotFixed : node ∉ fixedCoordinates first second evidence := by
    simp [fixedCoordinates, hnotFirst, hsecond, hnotEvidence]
  have hlatent : node ∈ latentRight parents first second evidence :=
    Finset.mem_sdiff.mpr ⟨hright, hnotFixed⟩
  simp [rightCoordinates, hlatent]

/-- Ancestral-moral separation produces a rank-one-ready split of the
ancestral factor score with exact left and right dependency coordinates. -/
theorem exists_moral_scores_of_separates
    [Fintype Node] [DecidableEq Node]
    (parents : Node → Finset Node)
    (kernels : LocalKernels Value parents)
    (first second evidence : Finset Node)
    (hseparates : Separates parents first second evidence) :
    ∃ leftScore rightScore : Assignment Value → ℝ,
      (∀ assignment,
        factorProduct Value parents kernels
            (ancestralFactors parents first second evidence) assignment =
          leftScore assignment * rightScore assignment) ∧
      DependsOnlyOn Value
          (leftCoordinates first evidence
            (latentLeft parents first second evidence)) leftScore ∧
        DependsOnlyOn Value
          (rightCoordinates second evidence
            (latentRight parents first second evidence)) rightScore := by
  obtain ⟨_, _, hfactorsDisjoint, hfactorsCover,
      hleftScopes, hrightScopes, _, _⟩ :=
    exists_moral_factor_partition_of_separates
      parents first second evidence hseparates
  have hleftScopes' : ∀ child ∈ leftFactors parents first second evidence,
      factorScope parents child ⊆
        leftCoordinates first evidence
          (latentLeft parents first second evidence) := by
    intro child hchild
    apply (hleftScopes child hchild).trans
    intro node hnode
    rcases Finset.mem_union.mp hnode with hregion | hevidence
    · exact leftRegion_subset_coordinates
        parents first second evidence hseparates hregion
    · simp [leftCoordinates, hevidence]
  have hrightScopes' : ∀ child ∈ rightFactors parents first second evidence,
      factorScope parents child ⊆
        rightCoordinates second evidence
          (latentRight parents first second evidence) := by
    intro child hchild
    apply (hrightScopes child hchild).trans
    intro node hnode
    rcases Finset.mem_union.mp hnode with hregion | hevidence
    · exact rightRegion_subset_coordinates
        parents first second evidence hregion
    · simp [rightCoordinates, hevidence]
  obtain ⟨leftScore, rightScore, hsplit, hleft, hright⟩ :=
    exists_partition_scores Value parents kernels
      (leftFactors parents first second evidence)
      (rightFactors parents first second evidence)
      (leftCoordinates first evidence
        (latentLeft parents first second evidence))
      (rightCoordinates second evidence
        (latentRight parents first second evidence))
      hfactorsDisjoint hleftScopes' hrightScopes'
  refine ⟨leftScore, rightScore, ?_, hleft, hright⟩
  intro assignment
  rw [← hfactorsCover]
  exact hsplit assignment

end GameTheory.Experimental.PostArchitecture.FiniteBNMoralScoreBridge
