module

/-
# Positive lotteries respecting a finite score ranking

Assigning a geometric weight to the number of strictly better alternatives
produces a positive lottery. Strict score improvements increase probability
by at least the reciprocal of the geometric ratio, while every coordinate
retains a uniform positive lower bound depending only on the finite carrier.
-/

public import GameTheory.Math.Probability.Simplex
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Data.Finset.Card

@[expose] public section

noncomputable section

namespace GameTheory.Math.Probability

open scoped BigOperators

private def scoreRank {A : Type*} [Fintype A] (score : A → ℝ) (action : A) : ℕ :=
  (Finset.univ.filter fun other => score action < score other).card

private theorem scoreRank_strict {A : Type*} [Fintype A]
    (score : A → ℝ) {worse better : A} (improvement : score worse < score better) :
    scoreRank score better < scoreRank score worse := by
  classical
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro other member
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at member ⊢
    exact improvement.trans member
  · intro equal
    have member : better ∈ Finset.univ.filter fun other => score worse < score other := by
      simp [improvement]
    rw [← equal] at member
    simp at member

private theorem scoreRank_le_card {A : Type*} [Fintype A]
    (score : A → ℝ) (action : A) : scoreRank score action ≤ Fintype.card A := by
  classical
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_univ)

/-- Any finite score ranking admits a positive lottery with geometric relative
error bounds. Its common coordinate floor depends only on the carrier and the
ratio, independently of the scores and their ties. -/
theorem exists_simplexWeights_geometric_ranking {A : Type*} [Fintype A] [Nonempty A]
    (score : A → ℝ) (epsilon : ℝ) (positive : 0 < epsilon) (small : epsilon ≤ 1) :
    ∃ w : A → ℝ, w ∈ simplexWeights A ∧
      (∀ action, epsilon ^ Fintype.card A / (Fintype.card A : ℝ) ≤ w action) ∧
      ∀ worse better, score worse < score better → w worse ≤ epsilon * w better := by
  classical
  let total : ℝ := ∑ action : A, epsilon ^ scoreRank score action
  have total_positive : 0 < total := by
    let action : A := Classical.choice ‹Nonempty A›
    have lower : epsilon ^ scoreRank score action ≤ total :=
      Finset.single_le_sum (fun other _ => pow_nonneg positive.le _) (Finset.mem_univ action)
    exact lt_of_lt_of_le (pow_pos positive _) lower
  have total_le_card : total ≤ (Fintype.card A : ℝ) := by
    calc
      total ≤ ∑ _action : A, (1 : ℝ) :=
        Finset.sum_le_sum fun _ _ => pow_le_one₀ positive.le small
      _ = (Fintype.card A : ℝ) := by simp
  have card_positive : 0 < (Fintype.card A : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  let weights : A → ℝ := fun action => epsilon ^ scoreRank score action / total
  refine ⟨weights, mem_simplexWeights.mpr ⟨?_, ?_⟩, ?_, ?_⟩
  · intro action
    exact div_nonneg (pow_nonneg positive.le _) total_positive.le
  · dsimp only [weights]
    rw [← Finset.sum_div]
    exact div_self total_positive.ne'
  · intro action
    apply (le_div_iff₀ total_positive).mpr
    calc
      (epsilon ^ Fintype.card A / (Fintype.card A : ℝ)) * total ≤
          (epsilon ^ Fintype.card A / (Fintype.card A : ℝ)) * (Fintype.card A : ℝ) :=
        mul_le_mul_of_nonneg_left total_le_card
          (div_nonneg (pow_nonneg positive.le _) card_positive.le)
      _ = epsilon ^ Fintype.card A := div_mul_cancel₀ _ card_positive.ne'
      _ ≤ epsilon ^ scoreRank score action :=
        pow_le_pow_of_le_one positive.le small (scoreRank_le_card score action)
  · intro worse better improvement
    have bound := pow_le_pow_of_le_one positive.le small
      (Nat.succ_le_of_lt (scoreRank_strict score improvement))
    rw [pow_succ'] at bound
    exact (div_le_div_of_nonneg_right bound total_positive.le).trans_eq
      (mul_div_assoc epsilon (epsilon ^ scoreRank score better) total)

end GameTheory.Math.Probability
