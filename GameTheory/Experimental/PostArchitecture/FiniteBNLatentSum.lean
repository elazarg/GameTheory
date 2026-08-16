/-
# EXP-104: dependent latent-coordinate sums

This module reindexes a cylinder sum by two disjoint latent coordinate blocks.
It is the cast-free Fubini seam between factor-scope separation and the
rank-one table algebra.  The construction uses the existing dependent
assignment enumeration and does not define another joint evaluator.

The coordinate type here is the explicit carrier being marginalized.  For a
Bayesian-network ancestor reduction, instantiate it with the subtype of nodes
in the ancestral set; `LatentPartition.cover` then ranges only over that
carrier and says nothing about nonancestors already integrated out.
-/

import GameTheory.Experimental.PostArchitecture.DependentAssignmentEnumeration

noncomputable section

open scoped BigOperators

namespace GameTheory.Experimental.PostArchitecture.FiniteBNLatentSum

open GameTheory.Experimental.PostArchitecture.DependentAssignmentEnumeration
open GameTheory.Experimental.PostArchitecture.FiniteBNGlobalMarkov

universe uNode uValue uResult

variable {Node : Type uNode} (Value : Node → Type uValue)

/-- A dependent assignment on exactly the selected coordinates. -/
abbrev Configuration (nodes : Finset Node) :=
  (node : {node // node ∈ nodes}) → Value node.1

/-- The three blocks in a complement enumeration: fixed coordinates and two
latent sides. -/
structure LatentPartition [DecidableEq Node]
    (fixed latentLeft latentRight : Finset Node) : Prop where
  fixed_left : Disjoint fixed latentLeft
  fixed_right : Disjoint fixed latentRight
  left_right : Disjoint latentLeft latentRight
  cover : ∀ node, node ∈ (fixed ∪ latentLeft) ∪ latentRight

/-- Split a complementary dependent configuration into its two latent blocks.
Membership branching retains the original node index, so no equality
transport is exposed. -/
def complementEquivLatents [DecidableEq Node]
    (fixed latentLeft latentRight : Finset Node)
    (partition : LatentPartition fixed latentLeft latentRight) :
    ComplementConfiguration Value fixed ≃
      Configuration Value latentLeft × Configuration Value latentRight where
  toFun configuration :=
    (fun node => configuration ⟨node.1, fun hfixed =>
      (Finset.disjoint_left.mp partition.fixed_left) hfixed node.2⟩,
    fun node => configuration ⟨node.1, fun hfixed =>
      (Finset.disjoint_left.mp partition.fixed_right) hfixed node.2⟩)
  invFun configurations node :=
    if hleft : node.1 ∈ latentLeft then configurations.1 ⟨node.1, hleft⟩
    else configurations.2 ⟨node.1, by
      have hall : node.1 ∈ (fixed ∪ latentLeft) ∪ latentRight := by
        exact partition.cover node.1
      rcases Finset.mem_union.mp hall with hfixedOrLeft | hright
      · rcases Finset.mem_union.mp hfixedOrLeft with hfixed | hleft'
        · exact False.elim (node.2 hfixed)
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

/-- Reindex a cylinder sum as nested sums over the two latent coordinate
blocks.  No positivity, normalization, or inhabitedness premise is involved. -/
theorem sum_ite_agrees_eq_sum_latents
    [Fintype Node] [DecidableEq Node]
    [∀ node, Fintype (Value node)] [∀ node, DecidableEq (Value node)]
    {Result : Type uResult} [AddCommMonoid Result]
    (fixed latentLeft latentRight : Finset Node)
    (partition : LatentPartition fixed latentLeft latentRight)
    (witness : Assignment Value) (score : Assignment Value → Result) :
    (∑ assignment : Assignment Value,
        if AgreeOn Value fixed assignment witness then score assignment else 0) =
      ∑ leftConfiguration : Configuration Value latentLeft,
        ∑ rightConfiguration : Configuration Value latentRight,
          score (fillComplement Value fixed witness
            ((complementEquivLatents Value fixed latentLeft latentRight
              partition).symm (leftConfiguration, rightConfiguration))) := by
  rw [sum_ite_agrees_eq_sum_complement Value fixed witness score]
  let equivalence := complementEquivLatents Value fixed latentLeft latentRight partition
  calc
    (∑ configuration : ComplementConfiguration Value fixed,
        score (fillComplement Value fixed witness configuration)) =
        ∑ configurations :
            Configuration Value latentLeft × Configuration Value latentRight,
          score (fillComplement Value fixed witness
            (equivalence.symm configurations)) := by
      apply Fintype.sum_equiv equivalence
      intro configuration
      have hinverse := equivalence.symm_apply_apply configuration
      exact congrArg (fun completed =>
        score (fillComplement Value fixed witness completed)) hinverse.symm
    _ = _ := by
      rw [Fintype.sum_prod_type]

end GameTheory.Experimental.PostArchitecture.FiniteBNLatentSum
