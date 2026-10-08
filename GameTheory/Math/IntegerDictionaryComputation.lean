import GameTheory.Math.IntegerCramerComputation
import GameTheory.Math.PerturbedDictionary
import GameTheory.Math.IntegerRatioSelection

/-! # Materialized integer symbolic dictionaries

Signed Cramer numerators store constant and perturbation coefficients over one
positive determinant denominator. This also represents entering directions,
including negative coordinates, without rational arithmetic during computation.
-/

namespace GameTheory.Math.IntegerDictionaryComputation

variable {n : ℕ}

private def rawCoefficients (M : Matrix (Fin n) (Fin n) ℤ) (q : Fin n → ℤ)
    (i : Fin n) : Fin (n + 1) → ℤ :=
  Fin.cons (IntegerCramerComputation.signedNumerator M q i)
    (fun j => IntegerCramerComputation.signedNumerator M (Pi.single j 1) i)

/-- Materialize all constant and perturbation numerators in a row-major array. -/
def coefficients (M : Matrix (Fin n) (Fin n) ℤ) (q : Fin n → ℤ) :
    Matrix (Fin n) (Fin (n + 1)) ℤ :=
  Matrix.ofArray (Array.ofFn fun p : Fin (n * (n + 1)) =>
    rawCoefficients M q p.divNat p.modNat) Array.size_ofFn

theorem coefficients_eq (M : Matrix (Fin n) (Fin n) ℤ) (q : Fin n → ℤ) :
    coefficients M q = fun i => Fin.cons (IntegerCramerComputation.signedNumerator M q i)
      (fun j => IntegerCramerComputation.signedNumerator M (Pi.single j 1) i) :=
  Matrix.ofArray_ofFn (rawCoefficients M q)

/-- Materialize the signed entering-direction numerators. -/
def direction (M : Matrix (Fin n) (Fin n) ℤ) (c : Fin n → ℤ) : Fin n → ℤ :=
  let values := Array.ofFn (IntegerCramerComputation.signedNumerator M c)
  fun i => values[i]'(by simpa only [values, Array.size_ofFn] using i.isLt)

theorem direction_eq (M : Matrix (Fin n) (Fin n) ℤ) (c : Fin n → ℤ) (i : Fin n) :
    direction M c i = IntegerCramerComputation.signedNumerator M c i := by
  simp only [direction, Fin.getElem_fin, Array.getElem_ofFn]

/-- Division by one positive scale recovers the canonical symbolic dictionary. -/
theorem coefficients_decode (M : Matrix (Fin n) (Fin n) ℤ) (q : Fin n → ℤ)
    (hdet : M.det ≠ 0) (i : Fin n) (k : Fin (n + 1)) :
    (coefficients M q i k : ℚ) / (IntegerCramerComputation.denominator M : ℚ) =
      PerturbedDictionary.dictionaryCoefficients (M.map (fun z : ℤ => (z : ℚ)))
        (fun j => (q j : ℚ)) i k := by
  rw [coefficients_eq]
  refine Fin.cases ?_ (fun j => ?_) k
  · exact IntegerCramerComputation.signed_decode M q hdet i
  · simp only [Fin.cons_succ, PerturbedDictionary.coefficient_succ]
    have he := IntegerCramerComputation.signed_decode M (Pi.single j 1) hdet i
    have hb : (fun k => ((Pi.single j (1 : ℤ) : Fin n → ℤ) k : ℚ)) =
        (Pi.single j (1 : ℚ) : Fin n → ℚ) := by
      funext k
      simp only [Pi.single_apply]
      split <;> rfl
    rw [hb, Matrix.mulVec_single_one] at he
    exact he

theorem direction_decode (M : Matrix (Fin n) (Fin n) ℤ) (c : Fin n → ℤ)
    (hdet : M.det ≠ 0) (i : Fin n) :
    (direction M c i : ℚ) / (IntegerCramerComputation.denominator M : ℚ) =
      (M.map (fun z : ℤ => (z : ℚ)))⁻¹.mulVec (fun j => (c j : ℚ)) i := by
  rw [direction_eq]
  exact IntegerCramerComputation.signed_decode M c hdet i

/-- Compute the symbolic minimum ratio using only stored integer cross-products. -/
def select (M : Matrix (Fin n) (Fin n) ℤ) (q c : Fin n → ℤ) : Option (Fin n) :=
  IntegerRatioSelection.select (coefficients M q) (direction M c)

theorem select_none (M : Matrix (Fin n) (Fin n) ℤ) (q c : Fin n → ℤ)
    (hdet : M.det ≠ 0) : select M q c = none ↔
      ∀ i, (M.map (fun z : ℤ => (z : ℚ)))⁻¹.mulVec (fun j => (c j : ℚ)) i ≤ 0 := by
  have hd : (0 : ℚ) < (IntegerCramerComputation.denominator M : ℚ) := by
    rw [IntegerCramerComputation.denominator_eq]
    exact_mod_cast IntegerCramerEncoding.denominator_pos M hdet
  rw [select, IntegerRatioSelection.select_none (coefficients M q) (direction M c)]
  constructor
  · intro hh i
    rw [← direction_decode M c hdet i]
    exact div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hh i) hd.le
  · intro hh i
    have he := hh i
    rw [← direction_decode M c hdet i] at he
    have hz : (direction M c i : ℚ) ≤ 0 := by
      simpa only [zero_mul] using (div_le_iff₀ hd).mp he
    exact_mod_cast hz

/-- The stored symbolic numerator fields have the canonical determinant width. -/
theorem coefficients_bound (M : Matrix (Fin n) (Fin n) ℤ) (q : Fin n → ℤ) (h : ℕ)
    (hM : ∀ i j, (M i j).natAbs ≤ 2 ^ h) (hq : ∀ i, (q i).natAbs ≤ 2 ^ h)
    (hdet : M.det ≠ 0) (i : Fin n) (k : Fin (n + 1)) :
    (coefficients M q i k).natAbs < 2 ^ IntegerBasisBounds.width n h := by
  rw [coefficients_eq]
  refine Fin.cases ?_ (fun j => ?_) k
  · exact IntegerCramerComputation.signedNumerator_bound M q h hM hq hdet i
  · simp only [Fin.cons_succ]
    apply IntegerCramerComputation.signedNumerator_bound M (Pi.single j 1) h hM _ hdet i
    intro a
    simp only [Pi.single_apply]
    split
    · exact Nat.one_le_pow h 2 (by decide)
    · exact Nat.zero_le _

theorem direction_bound (M : Matrix (Fin n) (Fin n) ℤ) (c : Fin n → ℤ) (h : ℕ)
    (hM : ∀ i j, (M i j).natAbs ≤ 2 ^ h) (hc : ∀ i, (c i).natAbs ≤ 2 ^ h)
    (hdet : M.det ≠ 0) (i : Fin n) :
    (direction M c i).natAbs < 2 ^ IntegerBasisBounds.width n h := by
  rw [direction_eq]
  exact IntegerCramerComputation.signedNumerator_bound M c h hM hc hdet i

/-- Cross-products used by the comparison retain polynomial binary width. -/
theorem crossProduct_bound (M : Matrix (Fin n) (Fin n) ℤ) (q c : Fin n → ℤ) (h : ℕ)
    (hM : ∀ i j, (M i j).natAbs ≤ 2 ^ h) (hq : ∀ i, (q i).natAbs ≤ 2 ^ h)
    (hc : ∀ i, (c i).natAbs ≤ 2 ^ h) (hdet : M.det ≠ 0)
    (i j : Fin n) (k : Fin (n + 1)) :
    (coefficients M q i k * direction M c j).natAbs <
      2 ^ (2 * IntegerBasisBounds.width n h) := by
  have ha := coefficients_bound M q h hM hq hdet i k
  have hb := direction_bound M c h hM hc hdet j
  rw [Int.natAbs_mul]
  calc
    _ ≤ 2 ^ IntegerBasisBounds.width n h * (direction M c j).natAbs :=
      Nat.mul_le_mul_right _ ha.le
    _ < 2 ^ IntegerBasisBounds.width n h * 2 ^ IntegerBasisBounds.width n h :=
      Nat.mul_lt_mul_of_pos_left hb (by positivity)
    _ = 2 ^ (2 * IntegerBasisBounds.width n h) := by rw [← pow_add, two_mul]

/-- The computed row is a leaving row of the canonical rational dictionary. -/
theorem select_some_spec (M : Matrix (Fin n) (Fin n) ℤ) (q c : Fin n → ℤ)
    (hdet : M.det ≠ 0) (l : Fin n) (hsel : select M q c = some l) :
    IsLeavingRow (PerturbedDictionary.dictionaryCoefficients
      (M.map (fun z : ℤ => (z : ℚ))) (fun j => (q j : ℚ)))
      ((M.map (fun z : ℤ => (z : ℚ)))⁻¹.mulVec (fun j => (c j : ℚ))) l := by
  have hd : (0 : ℚ) < (IntegerCramerComputation.denominator M : ℚ) := by
    rw [IntegerCramerComputation.denominator_eq]
    exact_mod_cast IntegerCramerEncoding.denominator_pos M hdet
  have hh := IntegerRatioSelection.select_some_spec (coefficients M q) (direction M c) l hsel
  refine ⟨?_, ?_⟩
  · rw [← direction_decode M c hdet l]
    exact div_pos hh.1 hd
  · intro i hi
    rw [← direction_decode M c hdet i] at hi
    have hp : (0 : ℚ) < (direction M c i : ℚ) := (div_pos_iff_of_pos_right hd).mp hi
    have he := hh.2 i hp
    have hc (j : Fin n) (k : Fin (n + 1)) :
        PerturbedDictionary.dictionaryCoefficients (M.map (fun z : ℤ => (z : ℚ)))
          (fun j => (q j : ℚ)) j k /
          (M.map (fun z : ℤ => (z : ℚ)))⁻¹.mulVec (fun j => (c j : ℚ)) j =
        (coefficients M q j k : ℚ) / (direction M c j : ℚ) := by
      rw [← coefficients_decode M q hdet j k, ← direction_decode M c hdet j]
      exact div_div_div_cancel_right₀ hd.ne' _ _
    simpa only [hc] using he

end GameTheory.Math.IntegerDictionaryComputation
