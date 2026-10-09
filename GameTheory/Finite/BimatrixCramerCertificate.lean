import GameTheory.Finite.BimatrixBasisBounds
import GameTheory.Finite.BimatrixComplementaryCertificateBounds
import GameTheory.Math.IntegerCramerComputation

/-! Compact certificates for the equilibrium at a complementary basis.
One absolute basis determinant clears all coordinates, avoiding a product of
reduced denominators. The sign-adjusted Cramer weights preserve the supplied
endpoint and fit the existing binary certificate width after payoff unshifting.
-/
namespace GameTheory.Finite
open GameTheory.Math GameTheory.Math.CanonicalDictionary

namespace BimatrixBasis
variable {m n : ℕ} {A B : Fin m → Fin n → ℤ}

/-- Extend the natural Cramer coordinates by zero outside the basis. -/
def cramerWeight (basis : BimatrixBasis A B) (v : BimatrixVariable m n) : ℕ :=
  if hv : v ∈ basis.basic then
    IntegerCramerComputation.numerator basis.integerMatrix (fun _ => 1)
      ((basis.basic.orderIsoOfFin basis.cardinality).symm ⟨v, hv⟩)
  else 0

private theorem integerSolution_nonneg (basis : BimatrixBasis A B) (i : Fin (m + n)) :
    0 ≤ (basis.integerMatrix.map (fun z : ℤ => (z : ℚ)))⁻¹.mulVec
      (fun _ => (1 : ℚ)) i := by
  simpa only [basis.integerMatrix_map, PerturbedDictionary.coefficient_zero] using
    FiniteLexicographic.constant_nonneg (basis.feasible.2 i).le

/-- Dividing every ambient weight by the same determinant recovers the exact basis point. -/
theorem cramerWeight_decode (basis : BimatrixBasis A B) (v : BimatrixVariable m n) :
    (basis.cramerWeight v : ℚ) / IntegerCramerEncoding.denominator basis.integerMatrix =
      basis.coordinates v := by
  by_cases hv : v ∈ basis.basic
  · simp only [cramerWeight, coordinates, BasisCoordinates.inverseCoordinates,
      BasisCoordinates.lift, dite_eq_left hv, IntegerCramerComputation.numerator_eq]
    have hh := IntegerCramerEncoding.decode basis.integerMatrix (fun _ => 1)
      basis.integerMatrix_det_ne_zero basis.integerSolution_nonneg
      ((basis.basic.orderIsoOfFin basis.cardinality).symm ⟨v, hv⟩)
    simpa only [basis.integerMatrix_map, Int.cast_one] using hh
  · simp only [cramerWeight, dite_eq_right hv, Nat.cast_zero, zero_div]
    exact (basis.coordinates_outside v hv).symm

theorem cramerWeight_lt (basis : BimatrixBasis A B) (h : ℕ)
    (hA : ∀ i j, (A i j).natAbs ≤ 2 ^ h) (hB : ∀ i j, (B i j).natAbs ≤ 2 ^ h)
    (v : BimatrixVariable m n) :
    basis.cramerWeight v < 2 ^ IntegerBasisBounds.width (m + n) h := by
  unfold cramerWeight
  split
  · rw [IntegerCramerComputation.numerator_eq]
    exact IntegerCramerEncoding.numerator_lt basis.integerMatrix (fun _ => 1) h
      (basis.integerMatrix_bound h hA hB) (fun _ => Nat.one_le_pow h 2 (by decide))
      _
  · positivity

/-- Normalize Cramer payoff weights and undo independent payoff shifts. -/
def cramerCertificate (basis : BimatrixBasis A B) (a b : ℤ) : BimatrixCertificate m n :=
  (complementaryNashCertificate
    (fun i => basis.cramerWeight (toLex (finSumFinEquiv (.inl i), true)))
    (fun j => basis.cramerWeight (toLex (finSumFinEquiv (.inr j), true)))
    (IntegerCramerComputation.denominator basis.integerMatrix)
    (IntegerCramerComputation.denominator basis.integerMatrix)).shiftPayoffs (-a) (-b)

/-- The common-denominator payoff point is the original endpoint, coordinate by coordinate. -/
theorem cramerPoint_eq (basis : BimatrixBasis A B) :
    bimatrixComplementaryPoint
      (fun i => basis.cramerWeight (toLex (finSumFinEquiv (.inl i), true)))
      (fun j => basis.cramerWeight (toLex (finSumFinEquiv (.inr j), true)))
      (IntegerCramerEncoding.denominator basis.integerMatrix)
      (IntegerCramerEncoding.denominator basis.integerMatrix) = basis.payoffPoint := by
  funext k
  cases k with
  | inl i => exact basis.cramerWeight_decode _
  | inr j => exact basis.cramerWeight_decode _

theorem cramerCertificate_fitsWidth (basis : BimatrixBasis A B) (a b : ℤ) (h s : ℕ)
    (hA : ∀ i j, (A i j).natAbs ≤ 2 ^ h) (hB : ∀ i j, (B i j).natAbs ≤ 2 ^ h)
    (ha : a.natAbs ≤ 2 ^ s) (hb : b.natAbs ≤ 2 ^ s) :
    (basis.cramerCertificate a b).FitsWidth
      (IntegerBasisBounds.width (m + n) h + (m + n) + s + 2) := by
  unfold cramerCertificate
  rw [IntegerCramerComputation.denominator_eq]
  exact complementaryNashCertificate_fitsWidth _ _ _ a b _ s
    (fun _ => (basis.cramerWeight_lt h hA hB _).le)
    (fun _ => (basis.cramerWeight_lt h hA hB _).le)
    (IntegerCramerEncoding.denominator_lt basis.integerMatrix h
      (basis.integerMatrix_bound h hA hB)).le ha hb

end BimatrixBasis

/-- A complementary non-source basis of a shifted game certifies the original signed game. -/
theorem cramerCertificate_valid {m n : ℕ} (A B : Fin m → Fin n → ℤ) (a b : ℤ)
    (basis : BimatrixBasis (fun i j => A i j + a) (fun i j => B i j + b))
    (hc : ComplementaryLabels.IsComplementary basis.nonbasic)
    (hs : basis ≠ bimatrixSourceBasis (fun i j => A i j + a) (fun i j => B i j + b)) :
    (basis.cramerCertificate a b).Valid A B := by
  unfold BimatrixBasis.cramerCertificate
  rw [IntegerCramerComputation.denominator_eq]
  obtain ⟨hne, hsol⟩ := basis.nonzero_payoffPoint_isSolution hc hs
  have hd := IntegerCramerEncoding.denominator_pos basis.integerMatrix
    basis.integerMatrix_det_ne_zero
  apply unshiftedComplementaryCertificate_valid A B a b _ _ _ _ hd hd
  · rwa [basis.cramerPoint_eq]
  · rwa [basis.cramerPoint_eq]

private theorem cramerWidth_le (m n h : ℕ) :
    IntegerBasisBounds.width (m + n) (h + 2) + (m + n) + (h + 2) + 2 ≤
      GameTheory.bimatrixCertificateWidth m n h := by
  unfold IntegerBasisBounds.width GameTheory.bimatrixCertificateWidth
  nlinarith

/-- The certificate of every non-source complementary shifted basis fits the
existing serialized field bound, without selecting a different equilibrium. -/
theorem shiftedCramerCertificate_valid_fitsWidth {m n : ℕ}
    (A B : Fin m → Fin n → ℤ) (h : ℕ)
    (hA : ∀ i j, (A i j).natAbs ≤ 2 ^ h) (hB : ∀ i j, (B i j).natAbs ≤ 2 ^ h)
    (basis : BimatrixBasis (fun i j => A i j + ((2 : ℤ) ^ h + 1))
      (fun i j => B i j + ((2 : ℤ) ^ h + 1)))
    (hc : ComplementaryLabels.IsComplementary basis.nonbasic)
    (hs : basis ≠ bimatrixSourceBasis (fun i j => A i j + ((2 : ℤ) ^ h + 1))
      (fun i j => B i j + ((2 : ℤ) ^ h + 1))) :
    (basis.cramerCertificate ((2 : ℤ) ^ h + 1) ((2 : ℤ) ^ h + 1)).Valid A B ∧
    (basis.cramerCertificate ((2 : ℤ) ^ h + 1) ((2 : ℤ) ^ h + 1)).FitsWidth
      (GameTheory.bimatrixCertificateWidth m n h) := by
  refine ⟨cramerCertificate_valid A B _ _ basis hc hs, ?_⟩
  have hshift : ((2 : ℤ) ^ h + 1).natAbs ≤ 2 ^ (h + 2) := by
    simpa only [zero_add] using (payoff_add_pow_bound 0 h (by simp)).le
  obtain ⟨hdp, hdq, hr, hc, hu, hv⟩ := basis.cramerCertificate_fitsWidth _ _ (h + 2) (h + 2)
    (fun i j => (payoff_add_pow_bound (A i j) h (hA i j)).le)
    (fun i j => (payoff_add_pow_bound (B i j) h (hB i j)).le) hshift hshift
  have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (cramerWidth_le m n h)
  exact ⟨hdp.trans_le hp, hdq.trans_le hp, fun i => (hr i).trans_le hp,
    fun j => (hc j).trans_le hp, hu.trans_le hp, hv.trans_le hp⟩

end GameTheory.Finite
