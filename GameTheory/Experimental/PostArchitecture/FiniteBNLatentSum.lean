/-
# EXP-104: dependent latent-coordinate sums

This module splits the coordinates newly fixed by a retained cylinder into two
disjoint latent blocks.  It is the cast-free Fubini seam between parent-closed
marginalization, factor-scope separation, and rank-one table algebra.

The carrier is an explicit retained set in the original node type.  This
matches the cylinder decomposition directly and avoids transporting factors,
scores, and configurations through an ancestral-node subtype.
-/

import GameTheory.Experimental.PostArchitecture.FiniteBNGlobalMarkov

noncomputable section

open scoped BigOperators

namespace GameTheory.Experimental.PostArchitecture.FiniteBNLatentSum

universe uNode uValue uResult

variable {Node : Type uNode} (Value : Node → Type uValue)

/-- A dependent assignment on exactly the selected coordinates. -/
abbrev Configuration (nodes : Finset Node) :=
  (node : {node // node ∈ nodes}) → Value node.1

/-- A retained carrier consists of fixed coordinates and two disjoint latent
blocks.  The equality prevents either latent block from containing coordinates
outside the retained carrier. -/
structure LatentPartition [DecidableEq Node]
    (fixed retained latentLeft latentRight : Finset Node) : Prop where
  left_right : Disjoint latentLeft latentRight
  latent_cover : retained \ fixed = latentLeft ∪ latentRight

/-- Split the newly retained dependent configuration into its two latent
blocks.  Membership branching retains the original node index, so no equality
transport is exposed. -/
def retainedDifferenceEquivLatents [DecidableEq Node]
    (fixed retained latentLeft latentRight : Finset Node)
    (partition : LatentPartition fixed retained latentLeft latentRight) :
    Configuration Value (retained \ fixed) ≃
      Configuration Value latentLeft × Configuration Value latentRight where
  toFun configuration :=
    (fun node => configuration ⟨node.1, by
      rw [partition.latent_cover]
      exact Finset.mem_union_left latentRight node.2⟩,
    fun node => configuration ⟨node.1, by
      rw [partition.latent_cover]
      exact Finset.mem_union_right latentLeft node.2⟩)
  invFun configurations node :=
    if hleft : node.1 ∈ latentLeft then configurations.1 ⟨node.1, hleft⟩
    else configurations.2 ⟨node.1, by
      have hunion : node.1 ∈ latentLeft ∪ latentRight := by
        rw [← partition.latent_cover]
        exact node.2
      rcases Finset.mem_union.mp hunion with hleft' | hright
      · exact False.elim (hleft hleft')
      · exact hright⟩
  left_inv configuration := by
    funext node
    by_cases hleft : node.1 ∈ latentLeft
    · simp [hleft]
    · simp [hleft]
  right_inv configurations := by
    apply Prod.ext
    · funext node
      simp [node.2]
    · funext node
      have hnotLeft : node.1 ∉ latentLeft := by
        intro hleft
        exact (Finset.disjoint_left.mp partition.left_right) hleft node.2
      simp [hnotLeft]

/-- Reindex a sum over the newly retained coordinates as nested sums over the
two latent blocks.  No node enumeration, positivity, normalization, or
inhabitedness premise is involved. -/
theorem sum_configuration_eq_sum_latents
    [DecidableEq Node]
    [∀ node, Fintype (Value node)]
    {Result : Type uResult} [AddCommMonoid Result]
    (fixed retained latentLeft latentRight : Finset Node)
    (partition : LatentPartition fixed retained latentLeft latentRight)
    (score : Configuration Value (retained \ fixed) → Result) :
    (∑ configuration : Configuration Value (retained \ fixed),
        score configuration) =
      ∑ leftConfiguration : Configuration Value latentLeft,
        ∑ rightConfiguration : Configuration Value latentRight,
          score ((retainedDifferenceEquivLatents Value fixed retained
            latentLeft latentRight partition).symm
              (leftConfiguration, rightConfiguration)) := by
  let equivalence := retainedDifferenceEquivLatents Value fixed retained
    latentLeft latentRight partition
  calc
    (∑ configuration : Configuration Value (retained \ fixed),
        score configuration) =
        ∑ configurations :
            Configuration Value latentLeft × Configuration Value latentRight,
          score (equivalence.symm configurations) := by
      apply Fintype.sum_equiv equivalence
      intro configuration
      exact congrArg score (equivalence.symm_apply_apply configuration).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]

/-! ## Empty and overlapping-block controls -/

namespace Controls

inductive ControlNode where
  | only
  deriving DecidableEq

abbrev UnitValue (_ : ControlNode) := Unit

def fixed : Finset ControlNode := {.only}

def retained : Finset ControlNode := {.only}

theorem emptyPartition : LatentPartition fixed retained ∅ ∅ where
  left_right := by simp
  latent_cover := by simp [fixed, retained]

/-- Empty latent blocks still have one dependent configuration each, so the
nested-sum reindexing remains valid for a singleton value domain. -/
theorem empty_latent_sum (score : Configuration UnitValue (retained \ fixed) → ℕ) :
    (∑ configuration, score configuration) =
      ∑ leftConfiguration : Configuration UnitValue ∅,
        ∑ rightConfiguration : Configuration UnitValue ∅,
          score ((retainedDifferenceEquivLatents UnitValue fixed retained
            ∅ ∅ emptyPartition).symm
              (leftConfiguration, rightConfiguration)) :=
  sum_configuration_eq_sum_latents UnitValue fixed retained ∅ ∅
    emptyPartition score

/-- One coordinate cannot be supplied independently by both latent blocks. -/
theorem overlapping_latents_rejected :
    ¬ LatentPartition ∅ retained retained retained := by
  intro partition
  have hmember : ControlNode.only ∈ retained := by
    simp [retained]
  exact (Finset.disjoint_left.mp partition.left_right)
    hmember hmember

end Controls

end GameTheory.Experimental.PostArchitecture.FiniteBNLatentSum
