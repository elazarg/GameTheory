/-
# EXP-104: retained-cylinder decomposition

This module partitions a cylinder fixed on a smaller coordinate set into the
disjoint exact cylinders obtained by assigning the remaining coordinates of a
larger retained set.  It is the probability seam between parent-closed
marginalization and latent component sums.  No graph, factorization,
normalization, or positivity premise is used.
-/

import GameTheory.Experimental.PostArchitecture.FiniteBNLatentSum
import GameTheory.Experimental.PostArchitecture.FiniteBNMarginalization

noncomputable section

open scoped BigOperators

namespace GameTheory.Experimental.PostArchitecture.FiniteBNRetainedSum

open GameTheory.Math.Probability
open GameTheory.Experimental.PostArchitecture.DependentAssignmentEnumeration
open GameTheory.Experimental.PostArchitecture.FiniteBNGlobalMarkov
open GameTheory.Experimental.PostArchitecture.FiniteBNLatentSum
open GameTheory.Experimental.PostArchitecture.FiniteBNMarginalization

universe uNode uValue

variable {Node : Type uNode} (Value : Node → Type uValue)

/-- Extend a witness on the fixed coordinates with freely chosen values on
the coordinates newly fixed by the retained cylinder. -/
def fillRetained [DecidableEq Node]
    (fixed retained : Finset Node) (witness : Assignment Value)
    (configuration : Configuration Value (retained \ fixed)) :
    Assignment Value :=
  fun node => if hnode : node ∈ retained \ fixed
    then configuration ⟨node, hnode⟩ else witness node

@[simp]
theorem fillRetained_of_mem [DecidableEq Node]
    (fixed retained : Finset Node) (witness : Assignment Value)
    (configuration : Configuration Value (retained \ fixed))
    {node : Node} (hnode : node ∈ retained \ fixed) :
    fillRetained Value fixed retained witness configuration node =
      configuration ⟨node, hnode⟩ := by
  simp [fillRetained, hnode]

@[simp]
theorem fillRetained_of_notMem [DecidableEq Node]
    (fixed retained : Finset Node) (witness : Assignment Value)
    (configuration : Configuration Value (retained \ fixed))
    {node : Node} (hnode : node ∉ retained \ fixed) :
    fillRetained Value fixed retained witness configuration node =
      witness node := by
  simp [fillRetained, hnode]

/-- The configuration read from an assignment on the newly retained
coordinates. -/
def retainedConfiguration [DecidableEq Node] (fixed retained : Finset Node)
    (assignment : Assignment Value) : Configuration Value (retained \ fixed) :=
  fun node => assignment node.1

theorem agreeOn_retained_fillRetained
    [DecidableEq Node]
    (fixed retained : Finset Node)
    (witness assignment : Assignment Value)
    (hfixed : AgreeOn Value fixed assignment witness) :
    AgreeOn Value retained assignment
      (fillRetained Value fixed retained witness
        (retainedConfiguration Value fixed retained assignment)) := by
  intro node hnode
  by_cases hfixedNode : node ∈ fixed
  · rw [fillRetained_of_notMem]
    · exact hfixed node hfixedNode
    · simp [hfixedNode]
  · rw [fillRetained_of_mem]
    · rfl
    · exact Finset.mem_sdiff.mpr ⟨hnode, hfixedNode⟩

theorem agreeOn_fixed_of_agreeOn_retained_fillRetained
    [DecidableEq Node]
    (fixed retained : Finset Node) (hsubset : fixed ⊆ retained)
    (witness assignment : Assignment Value)
    (configuration : Configuration Value (retained \ fixed))
    (hagrees : AgreeOn Value retained assignment
      (fillRetained Value fixed retained witness configuration)) :
    AgreeOn Value fixed assignment witness := by
  intro node hnode
  rw [hagrees node (hsubset hnode), fillRetained_of_notMem]
  simp [hnode]

theorem retainedConfiguration_eq_of_agreeOn
    [DecidableEq Node]
    (fixed retained : Finset Node) (witness assignment : Assignment Value)
    {configuration : Configuration Value (retained \ fixed)}
    (hagrees : AgreeOn Value retained assignment
      (fillRetained Value fixed retained witness configuration)) :
    retainedConfiguration Value fixed retained assignment = configuration := by
  funext node
  exact (hagrees node.1 (Finset.mem_sdiff.mp node.2).1).trans
    (fillRetained_of_mem Value fixed retained witness configuration node.2)

/-- A smaller cylinder is the disjoint sum of all exact cylinders on a larger
retained set.  Finiteness is required only to enumerate the new coordinates. -/
theorem cylinderMass_eq_sum_retained
    [Fintype Node] [DecidableEq Node]
    [∀ node, Fintype (Value node)] [∀ node, DecidableEq (Value node)]
    (law : FinDist (Assignment Value))
    (fixed retained : Finset Node) (hsubset : fixed ⊆ retained)
    (witness : Assignment Value) :
    cylinderMass Value law fixed witness =
      ∑ configuration : Configuration Value (retained \ fixed),
        cylinderMass Value law retained
          (fillRetained Value fixed retained witness configuration) := by
  rw [cylinderMass_eq_sum Value law fixed witness]
  simp_rw [cylinderMass_eq_sum Value law retained]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro assignment _
  by_cases hfixed : AgreeOn Value fixed assignment witness
  · simp only [hfixed, if_true]
    let matching := retainedConfiguration Value fixed retained assignment
    rw [Finset.sum_eq_single matching]
    · rw [if_pos]
      exact agreeOn_retained_fillRetained Value fixed retained
        witness assignment hfixed
    · intro configuration _ hne
      have hnotAgree : ¬ AgreeOn Value retained assignment
          (fillRetained Value fixed retained witness configuration) := by
        intro hagrees
        exact hne (retainedConfiguration_eq_of_agreeOn Value fixed retained
          witness assignment hagrees).symm
      simp [hnotAgree]
    · simp
  · simp only [hfixed, if_false]
    symm
    apply Finset.sum_eq_zero
    intro configuration _
    have hnotAgree : ¬ AgreeOn Value retained assignment
        (fillRetained Value fixed retained witness configuration) := by
      intro hagrees
      exact hfixed (agreeOn_fixed_of_agreeOn_retained_fillRetained Value
        fixed retained hsubset witness assignment configuration hagrees)
    simp [hnotAgree]

/-- Reindex the retained-cylinder partition by two explicit latent blocks. -/
theorem cylinderMass_eq_sum_latents
    [Fintype Node] [DecidableEq Node]
    [∀ node, Fintype (Value node)] [∀ node, DecidableEq (Value node)]
    (law : FinDist (Assignment Value))
    (fixed retained latentLeft latentRight : Finset Node)
    (hsubset : fixed ⊆ retained)
    (partition : LatentPartition fixed retained latentLeft latentRight)
    (witness : Assignment Value) :
    cylinderMass Value law fixed witness =
      ∑ leftConfiguration : Configuration Value latentLeft,
        ∑ rightConfiguration : Configuration Value latentRight,
          cylinderMass Value law retained
            (fillRetained Value fixed retained witness
              ((retainedDifferenceEquivLatents Value fixed retained
                latentLeft latentRight partition).symm
                  (leftConfiguration, rightConfiguration))) := by
  rw [cylinderMass_eq_sum_retained Value law fixed retained hsubset witness]
  exact sum_configuration_eq_sum_latents Value fixed retained latentLeft
    latentRight partition fun configuration =>
      cylinderMass Value law retained
        (fillRetained Value fixed retained witness configuration)

/-- When the larger retained set is parent-closed, every exact retained
cylinder in the partition is its retained local-factor product. -/
theorem cylinderMass_eq_sum_factorProduct_of_parentClosed
    [Fintype Node] [DecidableEq Node]
    [∀ node, Fintype (Value node)] [∀ node, DecidableEq (Value node)]
    (law : FinDist (Assignment Value))
    (parents : Node → Finset Node)
    (topological : GameTheory.Math.DAG.TopologicalOrder parents)
    (kernels : LocalKernels Value parents)
    (hfactor : Factorizes Value law parents kernels)
    (fixed retained : Finset Node) (hsubset : fixed ⊆ retained)
    (hclosed : ParentClosed parents retained)
    (witness : Assignment Value) :
    cylinderMass Value law fixed witness =
      ∑ configuration : Configuration Value (retained \ fixed),
        factorProduct Value parents kernels retained
          (fillRetained Value fixed retained witness configuration) := by
  rw [cylinderMass_eq_sum_retained Value law fixed retained hsubset witness]
  apply Finset.sum_congr rfl
  intro configuration _
  exact cylinderMass_eq_factorProduct_of_parentClosed Value law parents
    topological kernels hfactor retained
      (fillRetained Value fixed retained witness configuration) hclosed

/-- Parent-closed marginalization followed by the latent split gives the exact
factor score consumed by rank-one assembly. -/
theorem cylinderMass_eq_sum_latentFactorProducts_of_parentClosed
    [Fintype Node] [DecidableEq Node]
    [∀ node, Fintype (Value node)] [∀ node, DecidableEq (Value node)]
    (law : FinDist (Assignment Value))
    (parents : Node → Finset Node)
    (topological : GameTheory.Math.DAG.TopologicalOrder parents)
    (kernels : LocalKernels Value parents)
    (hfactor : Factorizes Value law parents kernels)
    (fixed retained latentLeft latentRight : Finset Node)
    (hsubset : fixed ⊆ retained)
    (hclosed : ParentClosed parents retained)
    (partition : LatentPartition fixed retained latentLeft latentRight)
    (witness : Assignment Value) :
    cylinderMass Value law fixed witness =
      ∑ leftConfiguration : Configuration Value latentLeft,
        ∑ rightConfiguration : Configuration Value latentRight,
          factorProduct Value parents kernels retained
            (fillRetained Value fixed retained witness
              ((retainedDifferenceEquivLatents Value fixed retained
                latentLeft latentRight partition).symm
                  (leftConfiguration, rightConfiguration))) := by
  rw [cylinderMass_eq_sum_factorProduct_of_parentClosed Value law parents
    topological kernels hfactor fixed retained hsubset hclosed witness]
  exact sum_configuration_eq_sum_latents Value fixed retained latentLeft
    latentRight partition fun configuration =>
      factorProduct Value parents kernels retained
        (fillRetained Value fixed retained witness configuration)

/-! ## Two-coordinate control -/

namespace BoolControl

abbrev BoolValue (_ : Bool) := Bool

def witness : Assignment BoolValue := fun _ => false

def law : FinDist (Assignment BoolValue) := FinDist.pure witness

def fixed : Finset Bool := {false}

def retained : Finset Bool := Finset.univ

theorem fixed_subset_retained : fixed ⊆ retained := by
  intro node _
  simp [retained]

/-- Splitting the point-law cylinder over the second Boolean coordinate keeps
exactly one unit-mass retained cylinder. -/
theorem split_point_cylinder :
    cylinderMass BoolValue law fixed witness =
      ∑ configuration : Configuration BoolValue (retained \ fixed),
        cylinderMass BoolValue law retained
          (fillRetained BoolValue fixed retained witness configuration) :=
  cylinderMass_eq_sum_retained BoolValue law fixed retained
    fixed_subset_retained witness

end BoolControl

end GameTheory.Experimental.PostArchitecture.FiniteBNRetainedSum
