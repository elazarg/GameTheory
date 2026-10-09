import GameTheory.Finite.BimatrixCertificate
import GameTheory.Math.MatchingMass
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
/-! Paired-action matching games with bounded integer payoff perturbations.
Dominant matching payoffs force positive, nearly uniform block masses in every
valid exact Nash certificate, while allowing either action within a block to have zero weight. -/
namespace GameTheory.Finite.BimatrixBlockGame
open BimatrixCertificate
open scoped BigOperators

/-- The paired action block of an action index. -/
def pairedBlock {k : ℕ} (i : Fin (k * 2)) : Fin k := (finProdFinEquiv.symm i).1

/-- A matching block payoff plus a cellwise integer perturbation. -/
def matchingBlockPayoff {k : ℕ} (H : ℤ) (E : Fin (k * 2) → Fin (k * 2) → ℤ)
    (i j : Fin (k * 2)) : ℤ := (if pairedBlock i = pairedBlock j then H else 0) + E i j

/-- The normalized probability mass of both actions in one block. -/
def blockMass {k : ℕ} (w : Fin (k * 2) → ℕ) (den : ℕ) (i : Fin k) : ℚ :=
  ∑ b : Fin 2, (w (finProdFinEquiv (i, b)) : ℚ) / den

/-- An action score splits into matching-block weight and perturbation score. -/
theorem matching_score {k : ℕ} (H : ℤ) (E : Fin (k * 2) → Fin (k * 2) → ℤ)
    (w : Fin (k * 2) → ℕ) (i : Fin k) (a : Fin 2) :
    (∑ j, matchingBlockPayoff H E (finProdFinEquiv (i, a)) j * (w j : ℤ)) =
      H * (∑ b : Fin 2, (w (finProdFinEquiv (i, b)) : ℤ)) +
        ∑ j, E (finProdFinEquiv (i, a)) j * (w j : ℤ) := by
  simp only [matchingBlockPayoff, add_mul, Finset.sum_add_distrib]
  congr 1
  rw [← Equiv.sum_comp finProdFinEquiv]
  rw [Fintype.sum_prod_type]
  simp [pairedBlock, ← Finset.mul_sum]

private theorem perturbation_bounds {k : ℕ} (E : Fin (k * 2) → ℤ)
    (w : Fin (k * 2) → ℕ) (den : ℕ) (D : ℤ)
    (hw : (∑ j, w j) = den) (hE : ∀ j, 0 ≤ E j ∧ E j ≤ D) :
    0 ≤ (∑ j, E j * (w j : ℤ)) ∧ (∑ j, E j * (w j : ℤ)) ≤ D * den := by
  constructor
  · exact Finset.sum_nonneg fun j _ => mul_nonneg (hE j).1 (Nat.cast_nonneg _)
  · calc
      _ ≤ ∑ j, D * (w j : ℤ) := Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_right (hE j).2 (Nat.cast_nonneg _)
      _ = D * den := by rw [← Finset.mul_sum, ← Nat.cast_sum, hw]

/-- Normalized scores split into matching-block probability and perturbation payoff. -/
theorem matching_score_div {k : ℕ} (H : ℤ) (E : Fin (k * 2) → Fin (k * 2) → ℤ)
    (w : Fin (k * 2) → ℕ) (den : ℕ) (i : Fin k) (a : Fin 2) :
    ((∑ j, matchingBlockPayoff H E (finProdFinEquiv (i, a)) j * (w j : ℤ) : ℤ) : ℚ) / den =
      (H : ℚ) * blockMass w den i +
        ((∑ j, E (finProdFinEquiv (i, a)) j * (w j : ℤ) : ℤ) : ℚ) / den := by
  rw [matching_score]
  simp only [Int.cast_add, Int.cast_mul, Int.cast_sum, Int.cast_natCast,
    add_div, blockMass, ← Finset.sum_div]
  ring
private theorem matching_block_gap_bound {k : ℕ} (H D : ℤ)
    (E : Fin (k * 2) → Fin (k * 2) → ℤ) (w : Fin (k * 2) → ℕ) (den : ℕ)
    (hw : (∑ j, w j) = den) (hden : 0 < den)
    (hE : ∀ i j, 0 ≤ E i j ∧ E i j ≤ D) (i j : Fin k) (a b : Fin 2)
    (hscore : (∑ l, matchingBlockPayoff H E (finProdFinEquiv (j, b)) l * (w l : ℤ)) ≤
      ∑ l, matchingBlockPayoff H E (finProdFinEquiv (i, a)) l * (w l : ℤ)) :
    (H : ℚ) * (blockMass w den j - blockMass w den i) ≤ D := by
  have hd : (0 : ℚ) < den := by exact_mod_cast hden
  have hs : ((∑ l, matchingBlockPayoff H E (finProdFinEquiv (j, b)) l * (w l : ℤ) : ℤ) : ℚ) / den ≤
      ((∑ l, matchingBlockPayoff H E (finProdFinEquiv (i, a)) l * (w l : ℤ) : ℤ) : ℚ) / den :=
    div_le_div_of_nonneg_right (by exact_mod_cast hscore) hd.le
  rw [matching_score_div, matching_score_div] at hs
  have hi := perturbation_bounds (E (finProdFinEquiv (i, a))) w den D hw
    (hE (finProdFinEquiv (i, a)))
  have hj := perturbation_bounds (E (finProdFinEquiv (j, b))) w den D hw
    (hE (finProdFinEquiv (j, b)))
  have hei : ((∑ l, E (finProdFinEquiv (i, a)) l * (w l : ℤ) : ℤ) : ℚ) / den ≤ D := by
    apply (div_le_iff₀ hd).mpr
    exact_mod_cast hi.2
  have hej : (0 : ℚ) ≤ ((∑ l, E (finProdFinEquiv (j, b)) l * (w l : ℤ) : ℤ) : ℚ) / den :=
    div_nonneg (by exact_mod_cast hj.1) hd.le
  nlinarith

private theorem positive_block_has_weight {k : ℕ} (w : Fin (k * 2) → ℕ)
    (den : ℕ) (i : Fin k) (hi : 0 < blockMass w den i) :
    ∃ b : Fin 2, 0 < w (finProdFinEquiv (i, b)) := by
  by_contra h
  push Not at h
  have hz : ∀ b : Fin 2, w (finProdFinEquiv (i, b)) = 0 := fun b => Nat.eq_zero_of_le_zero (h b)
  simp [blockMass, hz] at hi
/-- A supported row block nearly maximizes opponent block mass. -/
theorem row_block_comparison {k : ℕ} (H D : ℤ)
    (L R : Fin (k * 2) → Fin (k * 2) → ℤ) (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (matchingBlockPayoff H L) (matchingBlockPayoff (-H) R))
    (hH : 0 < H) (hL : ∀ i j, 0 ≤ L i j ∧ L i j ≤ D)
    (i : Fin k) (hi : 0 < blockMass c.rowWeights c.rowDenominator i) (j : Fin k) :
    blockMass c.colWeights c.colDenominator j ≤
      blockMass c.colWeights c.colDenominator i + (D : ℚ) / H := by
  obtain ⟨a, ha⟩ := positive_block_has_weight _ _ _ hi
  have hs : rowScore (matchingBlockPayoff H L) c (finProdFinEquiv (j, 0)) ≤
      rowScore (matchingBlockPayoff H L) c (finProdFinEquiv (i, a)) := by
    rw [(hc.2.2.2.2.1 _).2 ha]
    exact (hc.2.2.2.2.1 _).1
  have hgap := matching_block_gap_bound H D L c.colWeights c.colDenominator
    hc.2.2.2.1 hc.2.1 hL i j a 0 hs
  have hHq : (0 : ℚ) < H := by exact_mod_cast hH
  have hdiff : blockMass c.colWeights c.colDenominator j -
      blockMass c.colWeights c.colDenominator i ≤ (D : ℚ) / H := by
    apply (le_div_iff₀ hHq).mpr
    nlinarith
  linarith

/-- A supported column block nearly minimizes opponent block mass. -/
theorem col_block_comparison {k : ℕ} (H D : ℤ)
    (L R : Fin (k * 2) → Fin (k * 2) → ℤ) (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (matchingBlockPayoff H L) (matchingBlockPayoff (-H) R))
    (hH : 0 < H) (hR : ∀ i j, 0 ≤ R i j ∧ R i j ≤ D)
    (i : Fin k) (hi : 0 < blockMass c.colWeights c.colDenominator i) (j : Fin k) :
    blockMass c.rowWeights c.rowDenominator i ≤
      blockMass c.rowWeights c.rowDenominator j + (D : ℚ) / H := by
  obtain ⟨a, ha⟩ := positive_block_has_weight _ _ _ hi
  have hs : colScore (matchingBlockPayoff (-H) R) c (finProdFinEquiv (j, 0)) ≤
      colScore (matchingBlockPayoff (-H) R) c (finProdFinEquiv (i, a)) := by
    rw [(hc.2.2.2.2.2 _).2 ha]
    exact (hc.2.2.2.2.2 _).1
  have hswap (u : Fin k) (b : Fin 2) :
      colScore (matchingBlockPayoff (-H) R) c (finProdFinEquiv (u, b)) =
      ∑ l, matchingBlockPayoff (-H) (fun x y => R y x) (finProdFinEquiv (u, b)) l *
        (c.rowWeights l : ℤ) := by
    unfold colScore
    apply Finset.sum_congr rfl
    intro l _
    simp only [matchingBlockPayoff, eq_comm]
  rw [hswap, hswap] at hs
  have hgap := matching_block_gap_bound (-H) D (fun x y => R y x)
    c.rowWeights c.rowDenominator hc.2.2.1 hc.1 (fun x y => hR y x) i j a 0 hs
  have hHq : (0 : ℚ) < H := by exact_mod_cast hH
  have hdiff : blockMass c.rowWeights c.rowDenominator i -
      blockMass c.rowWeights c.rowDenominator j ≤ (D : ℚ) / H := by
    apply (le_div_iff₀ hHq).mpr
    push_cast at hgap
    nlinarith
  linarith

/-- Grouping normalized action weights into pairs preserves total probability. -/
theorem sum_blockMass {k : ℕ} (w : Fin (k * 2) → ℕ) (den : ℕ) (hden : 0 < den)
    (hw : (∑ i, w i) = den) : (∑ i, blockMass w den i) = 1 := by
  unfold blockMass
  rw [← Fintype.sum_prod_type']
  change (∑ x : Fin k × Fin 2, (w (finProdFinEquiv x) : ℚ) / den) = 1
  rw [Equiv.sum_comp finProdFinEquiv (fun i => (w i : ℚ) / den)]
  rw [← Finset.sum_div, ← Nat.cast_sum, hw]
  exact div_self (by exact_mod_cast hden.ne')

/-- A matching payoff exceeding the total perturbation scale forces every block
into support and bounds its distance from uniform probability. -/
theorem blockMass_uniform {k : ℕ} (H D : ℤ)
    (L R : Fin (k * 2) → Fin (k * 2) → ℤ) (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (matchingBlockPayoff H L) (matchingBlockPayoff (-H) R))
    (hL : ∀ i j, 0 ≤ L i j ∧ L i j ≤ D) (hR : ∀ i j, 0 ≤ R i j ∧ R i j ≤ D)
    (hscale : (k : ℤ) * D < H) :
    (∀ i, 0 < blockMass c.rowWeights c.rowDenominator i ∧
      0 < blockMass c.colWeights c.colDenominator i) ∧
    ∀ i, |blockMass c.rowWeights c.rowDenominator i - 1 / (k : ℚ)| ≤ (D : ℚ) / H ∧
      |blockMass c.colWeights c.colDenominator i - 1 / (k : ℚ)| ≤ (D : ℚ) / H := by
  have hk : 0 < k := by
    by_contra hk
    have hk : k = 0 := Nat.eq_zero_of_not_pos hk
    have hsum := hc.2.2.1
    simp [hk] at hsum
    have hden := hc.1
    omega
  let a : Fin (k * 2) := finProdFinEquiv (⟨0, hk⟩, 0)
  have hD : 0 ≤ D := (hL a a).1.trans (hL a a).2
  have hH : 0 < H := (mul_nonneg (Nat.cast_nonneg k) hD).trans_lt hscale
  have hkq : (0 : ℚ) < k := by exact_mod_cast hk
  have hHq : (0 : ℚ) < H := by exact_mod_cast hH
  have hsmall : (D : ℚ) / H < 1 / (k : ℚ) := by
    apply (div_lt_div_iff₀ hHq hkq).mpr
    have hs : (D : ℚ) * k < H := by exact_mod_cast (by simpa only [mul_comm] using hscale)
    simpa only [one_mul] using hs
  exact GameTheory.Math.matchingMass_uniform hk
    (blockMass c.rowWeights c.rowDenominator) (blockMass c.colWeights c.colDenominator)
    (sum_blockMass _ _ hc.1 hc.2.2.1) (sum_blockMass _ _ hc.2.1 hc.2.2.2.1) _ hsmall
    (row_block_comparison H D L R c hc hH hL) (col_block_comparison H D L R c hc hH hR)
end GameTheory.Finite.BimatrixBlockGame
