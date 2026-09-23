/-
# Simultaneous optimal local lotteries

Continuous action scores on a finite product of probability simplices admit
a point where every coordinate lottery maximizes its own expected score.
The scores may depend on every coordinate, including the coordinate being
optimized. During each local comparison the scores themselves are held fixed.

Kakutani applies to the product of the local argmax correspondences: finite
expectation is linear in the alternative lottery, so every argmax set is
nonempty and convex, and continuity of the scores gives a closed graph.
-/

import GameTheory.Math.Probability.Simplex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import FixedPointTheorems.kakutani

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability

/-- Continuous action scores admit simultaneous optimal coordinate lotteries.
The action scores in each comparison are evaluated at the same profile `x`;
they may depend on `x`'s own coordinate as well as its other coordinates. -/
theorem exists_localChoice_fixedPoint
    {ι : Type*} [Fintype ι] {A : ι → Type*}
    [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
    (score : (Set.pi Set.univ fun i => simplexWeights (A i)) → ∀ i, A i → ℝ)
    (continuous_score : ∀ i a, Continuous fun x => score x i a) :
    ∃ x : (Set.pi Set.univ fun i => simplexWeights (A i)),
      ∀ i (alternative : FinDist (A i)),
        alternative.expect (score x i) ≤
          (FinDist.ofSimplex (x.property i (Set.mem_univ i))).expect (score x i) := by
  classical
  let domain : Set (∀ i, A i → ℝ) :=
    Set.pi Set.univ fun i => simplexWeights (A i)
  let replies (x : domain) : Set (∀ i, A i → ℝ) :=
    Set.pi Set.univ fun i =>
      {v | v ∈ simplexWeights (A i) ∧
        ∀ w ∈ simplexWeights (A i),
          (∑ a, w a * score x i a) ≤ ∑ a, v a * score x i a}
  have replies_subset (x : domain) : replies x ⊆ domain := by
    intro y hy i hi
    exact (hy i hi).1
  have replies_convex (x : domain) : Convex ℝ (replies x) := by
    apply convex_pi
    intro i _
    rintro v ⟨hv, hvmax⟩ w ⟨hw, hwmax⟩ a b ha hb hab
    refine ⟨convex_simplexWeights _ hv hw ha hb hab, fun u hu => ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_assoc,
      Finset.sum_add_distrib, ← Finset.mul_sum]
    calc
      (∑ c, u c * score x i c) =
          a * (∑ c, u c * score x i c) + b * (∑ c, u c * score x i c) := by
        rw [← add_mul, hab, one_mul]
      _ ≤ a * (∑ c, v c * score x i c) + b * (∑ c, w c * score x i c) :=
        add_le_add (mul_le_mul_of_nonneg_left (hvmax u hu) ha)
          (mul_le_mul_of_nonneg_left (hwmax u hu) hb)
  have replies_nonempty (x : domain) : (replies x).Nonempty := by
    have coordinate_nonempty (i : ι) : ∃ v ∈ simplexWeights (A i),
        ∀ w ∈ simplexWeights (A i),
          (∑ a, w a * score x i a) ≤ ∑ a, v a * score x i a := by
      have score_sum_continuous :
          Continuous (fun v : A i → ℝ => ∑ a, v a * score x i a) := by
        apply continuous_finsetSum
        intro a _
        exact (continuous_apply a).mul continuous_const
      obtain ⟨v, hv, hmax⟩ := (isCompact_simplexWeights (A i)).exists_isMaxOn
        (f := fun v => ∑ a, v a * score x i a)
        FinDist.simplexWeights_nonempty score_sum_continuous.continuousOn
      exact ⟨v, hv, fun w hw => hmax hw⟩
    choose v hv hmax using coordinate_nonempty
    exact ⟨v, fun i _ => ⟨hv i, hmax i⟩⟩
  have replies_closedGraph : closedGraph replies := by
    show IsClosed _
    have hset : {z : domain × (∀ i, A i → ℝ) | z.2 ∈ replies z.1} =
        (⋂ i : ι, {z : domain × (∀ i, A i → ℝ) |
          z.2 i ∈ simplexWeights (A i)}) ∩
        ⋂ i : ι, ⋂ w ∈ simplexWeights (A i),
          {z : domain × (∀ i, A i → ℝ) |
            (∑ a, w a * score z.1 i a) ≤ ∑ a, z.2 i a * score z.1 i a} := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, replies,
        Set.mem_pi, Set.mem_univ, forall_const]
      exact forall_and
    rw [hset]
    refine IsClosed.inter (isClosed_iInter fun i => ?_)
      (isClosed_iInter fun i => isClosed_iInter fun w => isClosed_iInter fun _ => ?_)
    · exact (isClosed_simplexWeights _).preimage ((continuous_apply i).comp continuous_snd)
    · apply isClosed_le
      · exact continuous_finsetSum Finset.univ fun a _ =>
          ((continuous_score i a).comp continuous_fst).const_mul (w a)
      · apply continuous_finsetSum
        intro a _
        have coordinate_continuous : Continuous
            (fun z : domain × (∀ i, A i → ℝ) => z.2 i a) :=
          (continuous_apply a).comp ((continuous_apply i).comp continuous_snd)
        exact coordinate_continuous.mul ((continuous_score i a).comp continuous_fst)
  have domain_nonempty : domain.Nonempty :=
    ⟨fun i => (FinDist.pure (Classical.arbitrary (A i))).prob,
      fun i _ => FinDist.prob_mem_simplexWeights _⟩
  obtain ⟨x, hx⟩ := kakutani_fixed_point domain
    (convex_pi fun i _ => convex_simplexWeights (A i))
    (isCompact_univ_pi fun i => isCompact_simplexWeights (A i)) domain_nonempty
    replies replies_closedGraph
    (fun x => ⟨replies_subset x, replies_convex x, replies_nonempty x⟩)
  refine ⟨x, fun i alternative => ?_⟩
  simpa only [FinDist.expect_eq_sum, FinDist.prob_ofSimplex] using
    (hx i (Set.mem_univ i)).2 alternative.prob alternative.prob_mem_simplexWeights

end GameTheory
