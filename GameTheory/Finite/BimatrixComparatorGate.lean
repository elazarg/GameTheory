import GameTheory.Finite.BimatrixAffineGate
import Mathlib.Algebra.BigOperators.Fin

/-! Paired-action comparison games select the lower or upper output endpoint
according to the sign of a weighted integer signal. Zero signals leave the pair unconstrained. -/
namespace GameTheory.Finite.BimatrixComparatorGate
open BimatrixCertificate BimatrixBlockGame
open scoped BigOperators
variable {k : ℕ}

/-- Each auxiliary action receives one side of the comparison signal. -/
def columnPerturbation (P N : Fin k → Fin (k * 2) → ℤ) (r s : Fin (k * 2)) : ℤ :=
  if (finProdFinEquiv.symm s).2 = 0 then P (pairedBlock s) r else N (pairedBlock s) r

/-- Opposite matching blocks with a comparison signal independent of the output. -/
def columnPayoff (H : ℤ) (P N : Fin k → Fin (k * 2) → ℤ) :
    Fin (k * 2) → Fin (k * 2) → ℤ :=
  matchingBlockPayoff (-H) (columnPerturbation P N)

/-- The signal evaluated against the actual normalized row weights. -/
def signal (c : BimatrixCertificate (k * 2) (k * 2))
    (P N : Fin k → Fin (k * 2) → ℤ) (i : Fin k) : ℚ :=
  ((∑ r, (P i r - N i r) * (c.rowWeights r : ℤ) : ℤ) : ℚ) / c.rowDenominator

/-- The matching baseline cancels between the two auxiliary column actions. -/
theorem column_gain (H : ℤ) (P N : Fin k → Fin (k * 2) → ℤ)
    (c : BimatrixCertificate (k * 2) (k * 2)) (i : Fin k) :
    colScore (columnPayoff H P N) c (finProdFinEquiv (i, 0)) -
      colScore (columnPayoff H P N) c (finProdFinEquiv (i, 1)) =
        ∑ r, (P i r - N i r) * (c.rowWeights r : ℤ) := by
  simp [columnPayoff, colScore, matchingBlockPayoff, columnPerturbation, pairedBlock,
    add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, ite_mul]

/-- Every accepted certificate selects the row and auxiliary endpoints according
 to the comparison signal, before normalizing the weights. -/
theorem comparator_weights (H C : ℤ) (P N : Fin k → Fin (k * 2) → ℤ)
    (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (BimatrixAffineGate.rowPayoff H C) (columnPayoff H P N)) (hC : 0 < C)
    (i : Fin k)
    (hY : 0 < c.colWeights (finProdFinEquiv (i, 0)) +
      c.colWeights (finProdFinEquiv (i, 1))) :
    (0 < (∑ r, (P i r - N i r) * (c.rowWeights r : ℤ)) →
      c.colWeights (finProdFinEquiv (i, 0)) =
        c.colWeights (finProdFinEquiv (i, 0)) + c.colWeights (finProdFinEquiv (i, 1)) ∧
      c.rowWeights (finProdFinEquiv (i, 1)) =
        c.rowWeights (finProdFinEquiv (i, 0)) + c.rowWeights (finProdFinEquiv (i, 1))) ∧
    ((∑ r, (P i r - N i r) * (c.rowWeights r : ℤ)) < 0 →
      c.colWeights (finProdFinEquiv (i, 0)) = 0 ∧
        c.rowWeights (finProdFinEquiv (i, 1)) = 0) := by
  have hr := BimatrixAffineGate.row_support H C _ c hc hC i
  have hg := column_gain H P N c i
  have h := GameTheory.Math.pairSupport_comparator
    ((c.rowWeights (finProdFinEquiv (i, 0)) : ℚ) + c.rowWeights (finProdFinEquiv (i, 1)))
    ((c.colWeights (finProdFinEquiv (i, 0)) : ℚ) + c.colWeights (finProdFinEquiv (i, 1)))
    (c.rowWeights (finProdFinEquiv (i, 1)) : ℚ)
    (c.colWeights (finProdFinEquiv (i, 0)) : ℚ)
    ((∑ r, (P i r - N i r) * (c.rowWeights r : ℤ) : ℤ) : ℚ)
    (by exact_mod_cast hY) (Nat.cast_nonneg _) (le_add_of_nonneg_left (Nat.cast_nonneg _))
    (Nat.cast_nonneg _) (le_add_of_nonneg_right (Nat.cast_nonneg _))
    (fun hx => by
      have hi : 0 < c.rowWeights (finProdFinEquiv (i, 1)) := by exact_mod_cast hx
      have hh : (c.colWeights (finProdFinEquiv (i, 1)) : ℚ) ≤
        c.colWeights (finProdFinEquiv (i, 0)) := by exact_mod_cast hr.1 hi
      linarith)
    (fun hx => by
      have hi : 0 < c.rowWeights (finProdFinEquiv (i, 0)) := by
        have hh : (0 : ℚ) < c.rowWeights (finProdFinEquiv (i, 0)) := by linarith
        exact_mod_cast hh
      have hh : (c.colWeights (finProdFinEquiv (i, 0)) : ℚ) ≤
        c.colWeights (finProdFinEquiv (i, 1)) := by exact_mod_cast hr.2 hi
      linarith)
    (fun hy => by
      have hi : 0 < c.colWeights (finProdFinEquiv (i, 0)) := by exact_mod_cast hy
      have hs := colScore_le_of_pos hc hi (finProdFinEquiv (i, 1))
      have hh : 0 ≤ ∑ r, (P i r - N i r) * (c.rowWeights r : ℤ) := by linarith
      exact_mod_cast hh)
    (fun hy => by
      have hi : 0 < c.colWeights (finProdFinEquiv (i, 1)) := by
        have hh : (0 : ℚ) < c.colWeights (finProdFinEquiv (i, 1)) := by linarith
        exact_mod_cast hh
      have hs := colScore_le_of_pos hc hi (finProdFinEquiv (i, 0))
      have hh : (∑ r, (P i r - N i r) * (c.rowWeights r : ℤ)) ≤ 0 := by linarith
      exact_mod_cast hh)
  constructor
  · intro ht
    have htq : (0 : ℚ) < (∑ r, (P i r - N i r) * (c.rowWeights r : ℤ) : ℤ) := by
      exact_mod_cast ht
    exact_mod_cast h.1 htq
  · intro ht
    have htq : ((∑ r, (P i r - N i r) * (c.rowWeights r : ℤ) : ℤ) : ℚ) < 0 := by
      exact_mod_cast ht
    exact_mod_cast h.2 htq
/-- A nonzero comparison signal forces the normalized output to the corresponding
 endpoint of its row block. Only the auxiliary block needs positive mass. -/
theorem comparator (H C : ℤ) (P N : Fin k → Fin (k * 2) → ℤ)
    (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (BimatrixAffineGate.rowPayoff H C) (columnPayoff H P N)) (hC : 0 < C)
    (i : Fin k) (hY : 0 < blockMass c.colWeights c.colDenominator i) :
    (0 < signal c P N i →
      BimatrixAffineGate.auxiliaryValue c i = blockMass c.colWeights c.colDenominator i ∧
      BimatrixAffineGate.value c i = blockMass c.rowWeights c.rowDenominator i) ∧
    (signal c P N i < 0 →
      BimatrixAffineGate.auxiliaryValue c i = 0 ∧ BimatrixAffineGate.value c i = 0) := by
  have hd : (0 : ℚ) < c.colDenominator := by exact_mod_cast hc.2.1
  have hdr : (0 : ℚ) < c.rowDenominator := by exact_mod_cast hc.1
  have hYnat : 0 < c.colWeights (finProdFinEquiv (i, 0)) +
      c.colWeights (finProdFinEquiv (i, 1)) := by
    rw [blockMass, Fin.sum_univ_two, ← add_div] at hY
    have hp := (div_pos_iff_of_pos_right hd).mp hY
    exact_mod_cast hp
  have h := comparator_weights H C P N c hc hC i hYnat
  constructor
  · intro ht
    have hs : 0 < ∑ r, (P i r - N i r) * (c.rowWeights r : ℤ) := by
      have hp := (div_pos_iff_of_pos_right hdr).mp ht
      exact_mod_cast hp
    have hw := h.1 hs
    have hzcol : c.colWeights (finProdFinEquiv (i, 1)) = 0 := by omega
    have hzrow : c.rowWeights (finProdFinEquiv (i, 0)) = 0 := by omega
    simp [BimatrixAffineGate.auxiliaryValue, BimatrixAffineGate.value,
      blockMass, Fin.sum_univ_two, hzcol, hzrow]
  · intro ht
    have hs : (∑ r, (P i r - N i r) * (c.rowWeights r : ℤ)) < 0 := by
      have hp := (div_lt_iff₀ hdr).mp ht
      simp only [zero_mul] at hp
      exact_mod_cast hp
    have hw := h.2 hs
    simp [BimatrixAffineGate.auxiliaryValue, BimatrixAffineGate.value, hw.1, hw.2]
end GameTheory.Finite.BimatrixComparatorGate
