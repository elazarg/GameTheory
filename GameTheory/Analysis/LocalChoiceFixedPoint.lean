module

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

public import GameTheory.Math.Probability.Simplex
public import GameTheory.Analysis.FeasibleChoiceFixedPoint

@[expose] public section

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
      ∀ i (alternative : PMF (A i)),
        expect alternative (score x i) ≤
          expect (PMF.ofSimplex (x.property i (Set.mem_univ i))) (score x i) := by
  classical
  let domain : Set (∀ i, A i → ℝ) :=
    Set.pi Set.univ fun i => simplexWeights (A i)
  have continuous_objective (i : ι) : Continuous
      (fun p : domain × (A i → ℝ) => ∑ a, p.2 a * score p.1 i a) := by
    apply continuous_finsetSum
    intro a _
    exact ((continuous_apply a).comp continuous_snd).mul
      ((continuous_score i a).comp continuous_fst)
  have quasiconcave_objective (i : ι) (x : domain) :
      QuasiconcaveOn ℝ (simplexWeights (A i))
        (fun weights => ∑ a, weights a * score x i a) := by
    apply ConcaveOn.quasiconcaveOn
    refine ⟨convex_simplexWeights _, ?_⟩
    intro v _ w _ a b _ _ _
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_assoc,
      Finset.sum_add_distrib, ← Finset.mul_sum, le_refl]
  obtain ⟨x, optimal⟩ := exists_feasibleChoice_fixedPoint
    (fun i => simplexWeights (A i)) (fun i => convex_simplexWeights (A i))
    (fun i => isCompact_simplexWeights (A i)) (fun i => PMF.simplexWeights_nonempty)
    (fun i _ => simplexWeights (A i)) (fun _ _ => Set.Subset.refl _)
    (fun i => (isClosed_simplexWeights (A i)).preimage continuous_snd)
    (fun _ => LowerHemicontinuous.const) (fun _ _ => PMF.simplexWeights_nonempty)
    (fun i p => ∑ a, p.2 a * score p.1 i a)
    continuous_objective quasiconcave_objective
  refine ⟨x, fun i alternative => ?_⟩
  have hoptimal := (optimal i).2 (PMF.toReal_mem_simplexWeights alternative)
  rw [expect_eq_sum, expect_eq_sum]
  calc
    (∑ action, (alternative action).toReal * score x i action) ≤
        ∑ action, ((x : ∀ j, A j → ℝ) i action) * score x i action := hoptimal
    _ = ∑ action,
        ((PMF.ofSimplex (x.property i (Set.mem_univ i)) action).toReal) *
          score x i action := by
      apply Finset.sum_congr rfl
      intro action _
      congr 1
      exact (congrFun
        (PMF.ofSimplex_toReal (x.property i (Set.mem_univ i))) action).symm

end GameTheory
