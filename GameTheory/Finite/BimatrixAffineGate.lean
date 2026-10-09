import GameTheory.Finite.BimatrixBlockGame
import GameTheory.Math.PairSupportGate
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Tactic.FieldSimp

/-! Integer paired-action games implement saturated affine equations.
Each row pair responds to its own auxiliary column pair. The column payoff
difference compares an affine signal with the output row probability. -/

namespace GameTheory.Finite.BimatrixAffineGate

open BimatrixCertificate BimatrixBlockGame
open scoped BigOperators

variable {k : ℕ}

/-- The row action is rewarded for the opposite action in its auxiliary column pair. -/
def rowPerturbation (C : ℤ) (r s : Fin (k * 2)) : ℤ :=
  if (finProdFinEquiv.symm r).2 = 0 then
    if s = finProdFinEquiv (pairedBlock r, 1) then C else 0
  else if s = finProdFinEquiv (pairedBlock r, 0) then C else 0

/-- The auxiliary pair compares the positive signal with the negative signal and output. -/
def columnPerturbation (C : ℤ) (P N : Fin k → Fin (k * 2) → ℤ)
    (r s : Fin (k * 2)) : ℤ :=
  if (finProdFinEquiv.symm s).2 = 0 then P (pairedBlock s) r
  else N (pairedBlock s) r + if r = finProdFinEquiv (pairedBlock s, 1) then C else 0

/-- Matching blocks with a within-pair response signal. -/
def rowPayoff (H C : ℤ) : Fin (k * 2) → Fin (k * 2) → ℤ :=
  matchingBlockPayoff H (rowPerturbation C)

/-- Opposite matching blocks with an affine comparison signal. -/
def columnPayoff (H C : ℤ) (P N : Fin k → Fin (k * 2) → ℤ) :
    Fin (k * 2) → Fin (k * 2) → ℤ :=
  matchingBlockPayoff (-H) (columnPerturbation C P N)

/-- The output coordinate is the probability of the second row action. -/
def value (c : BimatrixCertificate (k * 2) (k * 2)) (i : Fin k) : ℚ :=
  (c.rowWeights (finProdFinEquiv (i, 1)) : ℚ) / c.rowDenominator

/-- The control coordinate is the probability of the first auxiliary column action. -/
def auxiliaryValue (c : BimatrixCertificate (k * 2) (k * 2)) (i : Fin k) : ℚ :=
  (c.colWeights (finProdFinEquiv (i, 0)) : ℚ) / c.colDenominator

/-- The signed affine target is expressed against the actual normalized row weights. -/
def target (c : BimatrixCertificate (k * 2) (k * 2)) (C : ℤ)
    (P N : Fin k → Fin (k * 2) → ℤ) (i : Fin k) : ℚ :=
  ((∑ r, (P i r - N i r) * (c.rowWeights r : ℤ) : ℤ) : ℚ) /
    ((C : ℚ) * c.rowDenominator)

/-- The matching baseline cancels when comparing the two row actions. -/
theorem row_gain (H C : ℤ) (c : BimatrixCertificate (k * 2) (k * 2)) (i : Fin k) :
    rowScore (rowPayoff H C) c (finProdFinEquiv (i, 1)) -
      rowScore (rowPayoff H C) c (finProdFinEquiv (i, 0)) =
        C * ((c.colWeights (finProdFinEquiv (i, 0)) : ℤ) -
          (c.colWeights (finProdFinEquiv (i, 1)) : ℤ)) := by
  simp only [rowPayoff, rowScore]
  rw [matching_score, matching_score]
  simp [rowPerturbation, pairedBlock, ite_mul]
  ring

/-- The auxiliary column difference is the affine signal minus the output. -/
theorem column_gain (H C : ℤ) (P N : Fin k → Fin (k * 2) → ℤ)
    (c : BimatrixCertificate (k * 2) (k * 2)) (i : Fin k) :
    colScore (columnPayoff H C P N) c (finProdFinEquiv (i, 0)) -
      colScore (columnPayoff H C P N) c (finProdFinEquiv (i, 1)) =
        (∑ r, (P i r - N i r) * (c.rowWeights r : ℤ)) -
          C * (c.rowWeights (finProdFinEquiv (i, 1)) : ℤ) := by
  simp [columnPayoff, colScore, matchingBlockPayoff, columnPerturbation, pairedBlock,
    add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, ite_mul]
  ring

/-- Supported row actions impose the opposing auxiliary weight comparisons. -/
theorem row_support (H C : ℤ) (B : Fin (k * 2) → Fin (k * 2) → ℤ)
    (c : BimatrixCertificate (k * 2) (k * 2)) (hc : c.Valid (rowPayoff H C) B)
    (hC : 0 < C) (i : Fin k) :
    (0 < c.rowWeights (finProdFinEquiv (i, 1)) →
      c.colWeights (finProdFinEquiv (i, 1)) ≤ c.colWeights (finProdFinEquiv (i, 0))) ∧
    (0 < c.rowWeights (finProdFinEquiv (i, 0)) →
      c.colWeights (finProdFinEquiv (i, 0)) ≤ c.colWeights (finProdFinEquiv (i, 1))) := by
  have hg := row_gain H C c i
  constructor
  · intro hi
    have hs := rowScore_le_of_pos hc hi (finProdFinEquiv (i, 0))
    have hw : (c.colWeights (finProdFinEquiv (i, 1)) : ℤ) ≤
        c.colWeights (finProdFinEquiv (i, 0)) := by nlinarith
    exact_mod_cast hw
  · intro hi
    have hs := rowScore_le_of_pos hc hi (finProdFinEquiv (i, 1))
    have hw : (c.colWeights (finProdFinEquiv (i, 0)) : ℤ) ≤
        c.colWeights (finProdFinEquiv (i, 1)) := by nlinarith
    exact_mod_cast hw

/-- Every accepted certificate implements the affine gate before normalization. -/
theorem clamp_weights (H C : ℤ) (P N : Fin k → Fin (k * 2) → ℤ)
    (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (rowPayoff H C) (columnPayoff H C P N)) (hC : 0 < C)
    (i : Fin k)
    (hX : 0 < c.rowWeights (finProdFinEquiv (i, 0)) +
      c.rowWeights (finProdFinEquiv (i, 1)))
    (hY : 0 < c.colWeights (finProdFinEquiv (i, 0)) +
      c.colWeights (finProdFinEquiv (i, 1))) :
    (c.rowWeights (finProdFinEquiv (i, 1)) : ℚ) =
      max 0 (min ((c.rowWeights (finProdFinEquiv (i, 0)) : ℚ) +
        c.rowWeights (finProdFinEquiv (i, 1)))
        (((∑ r, (P i r - N i r) * (c.rowWeights r : ℤ) : ℤ) : ℚ) / C)) := by
  have hr := row_support H C _ c hc hC i
  have hg := column_gain H C P N c i
  have hCq : (0 : ℚ) < C := by exact_mod_cast hC
  apply GameTheory.Math.pairSupport_clamp
    (((c.rowWeights (finProdFinEquiv (i, 0)) : ℚ) +
      c.rowWeights (finProdFinEquiv (i, 1))))
    (((c.colWeights (finProdFinEquiv (i, 0)) : ℚ) +
      c.colWeights (finProdFinEquiv (i, 1))))
    (c.rowWeights (finProdFinEquiv (i, 1)) : ℚ)
    (c.colWeights (finProdFinEquiv (i, 0)) : ℚ)
    (((∑ r, (P i r - N i r) * (c.rowWeights r : ℤ) : ℤ) : ℚ) / C)
  · exact_mod_cast hX
  · exact_mod_cast hY
  · exact Nat.cast_nonneg _
  · exact le_add_of_nonneg_left (Nat.cast_nonneg _)
  · intro hx
    have hi : 0 < c.rowWeights (finProdFinEquiv (i, 1)) := by exact_mod_cast hx
    have hh : (c.colWeights (finProdFinEquiv (i, 1)) : ℚ) ≤
        c.colWeights (finProdFinEquiv (i, 0)) := by exact_mod_cast hr.1 hi
    linarith
  · intro hx
    have hi : 0 < c.rowWeights (finProdFinEquiv (i, 0)) := by
      have hh : (0 : ℚ) < c.rowWeights (finProdFinEquiv (i, 0)) := by linarith
      exact_mod_cast hh
    have hh : (c.colWeights (finProdFinEquiv (i, 0)) : ℚ) ≤
        c.colWeights (finProdFinEquiv (i, 1)) := by exact_mod_cast hr.2 hi
    linarith
  · intro hy
    have hi : 0 < c.colWeights (finProdFinEquiv (i, 0)) := by exact_mod_cast hy
    have hs := colScore_le_of_pos hc hi (finProdFinEquiv (i, 1))
    apply (le_div_iff₀ hCq).mpr
    have hh : C * (c.rowWeights (finProdFinEquiv (i, 1)) : ℤ) ≤
        ∑ r, (P i r - N i r) * (c.rowWeights r : ℤ) := by linarith
    exact_mod_cast (by simpa only [mul_comm] using hh)
  · intro hy
    have hi : 0 < c.colWeights (finProdFinEquiv (i, 1)) := by
      have hh : (0 : ℚ) < c.colWeights (finProdFinEquiv (i, 1)) := by linarith
      exact_mod_cast hh
    have hs := colScore_le_of_pos hc hi (finProdFinEquiv (i, 0))
    apply (div_le_iff₀ hCq).mpr
    have hh : (∑ r, (P i r - N i r) * (c.rowWeights r : ℤ)) ≤
        C * (c.rowWeights (finProdFinEquiv (i, 1)) : ℤ) := by linarith
    exact_mod_cast (by simpa only [mul_comm] using hh)

/-- Pair mass is the sum of its two normalized weights. -/
theorem blockMass_pair (w : Fin (k * 2) → ℕ) (den : ℕ) (i : Fin k) :
    blockMass w den i = ((w (finProdFinEquiv (i, 0)) : ℚ) +
      w (finProdFinEquiv (i, 1))) / den := by
  simp [blockMass, Fin.sum_univ_succ, add_div]

/-- Every accepted certificate with positive block masses satisfies the saturated gate. -/
theorem value_eq_clamp (H C : ℤ) (P N : Fin k → Fin (k * 2) → ℤ)
    (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (rowPayoff H C) (columnPayoff H C P N)) (hC : 0 < C)
    (i : Fin k) (hX : 0 < blockMass c.rowWeights c.rowDenominator i)
    (hY : 0 < blockMass c.colWeights c.colDenominator i) :
    value c i = max 0 (min (blockMass c.rowWeights c.rowDenominator i)
      (target c C P N i)) := by
  have hd : (0 : ℚ) < c.rowDenominator := by exact_mod_cast hc.1
  have he : (0 : ℚ) < c.colDenominator := by exact_mod_cast hc.2.1
  rw [blockMass_pair] at hX hY
  have hx : 0 < c.rowWeights (finProdFinEquiv (i, 0)) +
      c.rowWeights (finProdFinEquiv (i, 1)) := by
    have hh := (div_pos_iff_of_pos_right hd).mp hX
    exact_mod_cast hh
  have hy : 0 < c.colWeights (finProdFinEquiv (i, 0)) +
      c.colWeights (finProdFinEquiv (i, 1)) := by
    have hh := (div_pos_iff_of_pos_right he).mp hY
    exact_mod_cast hh
  unfold value
  rw [clamp_weights H C P N c hc hC i hx hy]
  rw [← max_div_div_right hd.le, ← min_div_div_right hd.le]
  simp only [zero_div, div_div, blockMass_pair, target]

/-- A common coefficient cap bounds every row perturbation. -/
theorem rowPerturbation_bounds (C D : ℤ) (hC : 0 ≤ C) (hCD : C ≤ D)
    (r s : Fin (k * 2)) : 0 ≤ rowPerturbation C r s ∧ rowPerturbation C r s ≤ D := by
  unfold rowPerturbation
  split_ifs <;> exact ⟨by omega, by omega⟩

/-- The output coefficient is included in the negative-signal cap. -/
theorem columnPerturbation_bounds (C D : ℤ) (P N : Fin k → Fin (k * 2) → ℤ)
    (hC : 0 ≤ C) (hP : ∀ i r, 0 ≤ P i r ∧ P i r ≤ D)
    (hN : ∀ i r, 0 ≤ N i r ∧ N i r + C ≤ D)
    (r s : Fin (k * 2)) :
    0 ≤ columnPerturbation C P N r s ∧ columnPerturbation C P N r s ≤ D := by
  unfold columnPerturbation
  split_ifs
  · exact hP _ _
  · exact ⟨add_nonneg (hN _ _).1 hC, (hN _ _).2⟩
  · simpa only [add_zero] using
      And.intro (hN (pairedBlock s) r).1 (by linarith [(hN (pairedBlock s) r).2])

/-- Dominant matching payoffs make all affine gate equations hold in every equilibrium. -/
theorem all_values_eq_clamp (H C D : ℤ) (P N : Fin k → Fin (k * 2) → ℤ)
    (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (rowPayoff H C) (columnPayoff H C P N))
    (hC : 0 < C) (hCD : C ≤ D)
    (hP : ∀ i r, 0 ≤ P i r ∧ P i r ≤ D)
    (hN : ∀ i r, 0 ≤ N i r ∧ N i r + C ≤ D)
    (hscale : (k : ℤ) * D < H) :
    ∀ i, value c i = max 0 (min (blockMass c.rowWeights c.rowDenominator i)
      (target c C P N i)) := by
  have hm := blockMass_uniform H D (rowPerturbation C) (columnPerturbation C P N) c hc
    (rowPerturbation_bounds C D hC.le hCD)
    (columnPerturbation_bounds C D P N hC.le hP hN) hscale
  exact fun i => value_eq_clamp H C P N c hc hC i (hm.1 i).1 (hm.1 i).2

/-- Rescaling the block capacity to one introduces only the matching-mass error. -/
theorem normalized_value_error (H C D : ℤ) (P N : Fin k → Fin (k * 2) → ℤ)
    (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (rowPayoff H C) (columnPayoff H C P N))
    (hC : 0 < C) (hCD : C ≤ D)
    (hP : ∀ i r, 0 ≤ P i r ∧ P i r ≤ D)
    (hN : ∀ i r, 0 ≤ N i r ∧ N i r + C ≤ D)
    (hscale : (k : ℤ) * D < H) (i : Fin k) :
    |(k : ℚ) * value c i - max 0 (min 1 ((k : ℚ) * target c C P N i))| ≤
      (k : ℚ) * ((D : ℚ) / H) := by
  have hm := blockMass_uniform H D (rowPerturbation C) (columnPerturbation C P N) c hc
    (rowPerturbation_bounds C D hC.le hCD)
    (columnPerturbation_bounds C D P N hC.le hP hN) hscale
  have hk : (k : ℚ) ≠ 0 := by
    intro hz
    have hh := hm.1 i
    have hkn : k = 0 := by exact_mod_cast hz
    have hi := i.isLt
    omega
  rw [all_values_eq_clamp H C D P N c hc hC hCD hP hN hscale i,
    mul_max_of_nonneg _ _ (Nat.cast_nonneg k), mul_zero,
    mul_min_of_nonneg _ _ (Nat.cast_nonneg k)]
  have hmin := abs_min_sub_min_le_max
    ((k : ℚ) * blockMass c.rowWeights c.rowDenominator i)
    ((k : ℚ) * target c C P N i) 1 ((k : ℚ) * target c C P N i)
  simp only [sub_self, abs_zero] at hmin
  rw [max_eq_left (abs_nonneg _)] at hmin
  have hmax := abs_max_sub_max_le_max (0 : ℚ)
    (min ((k : ℚ) * blockMass c.rowWeights c.rowDenominator i)
      ((k : ℚ) * target c C P N i)) 0 (min 1 ((k : ℚ) * target c C P N i))
  simp only [sub_self, abs_zero] at hmax
  conv at hmax =>
    rhs
    rw [max_eq_right (abs_nonneg _)]
  have hmass : |(k : ℚ) * blockMass c.rowWeights c.rowDenominator i - 1| ≤
      (k : ℚ) * ((D : ℚ) / H) := by
    have he : (k : ℚ) * blockMass c.rowWeights c.rowDenominator i - 1 =
        (k : ℚ) * (blockMass c.rowWeights c.rowDenominator i - 1 / (k : ℚ)) := by
      field_simp
    rw [he, abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
    exact mul_le_mul_of_nonneg_left (hm.2 i).1 (Nat.cast_nonneg k)
  exact hmax.trans (hmin.trans hmass)

end GameTheory.Finite.BimatrixAffineGate
