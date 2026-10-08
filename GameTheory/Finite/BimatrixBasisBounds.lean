import GameTheory.Finite.BimatrixBasisSolution
import GameTheory.Math.IntegerBasisBounds
import GameTheory.Finite.BimatrixEndpointBounds

/-! Polynomial binary bounds on every certified bimatrix basis.
Integer column encodings coincide with the canonical rational columns. Cramer
bounds control constant and symbolic coordinates and all entering directions,
independently of path length or payoff positivity.
-/
namespace GameTheory.Finite
open GameTheory.Math GameTheory.Math.CanonicalDictionary
variable {m n : ℕ}

/-- Integer encoding of the canonical rational columns, using their exact numerators. -/
def bimatrixIntegerColumns (A B : Fin m → Fin n → ℤ) :
    Matrix (Fin (m + n)) (BimatrixVariable m n) ℤ :=
  fun i v => (bimatrixBasisColumns A B i v).num

theorem bimatrixIntegerColumns_cast (A B : Fin m → Fin n → ℤ)
    (i : Fin (m + n)) (v : BimatrixVariable m n) :
    (bimatrixIntegerColumns A B i v : ℚ) = bimatrixBasisColumns A B i v := by
  unfold bimatrixIntegerColumns bimatrixBasisColumns
  split
  · cases hr : finSumFinEquiv.symm i <;> cases hc : finSumFinEquiv.symm (ofLex v).1 <;>
      simp [bimatrixEnteringColumn, bimatrixComplementaryMatrix, hr]
  · simp only [Pi.single_apply]
    split <;> norm_num

theorem bimatrixIntegerColumns_bound (A B : Fin m → Fin n → ℤ) (h : ℕ)
    (hA : ∀ i j, (A i j).natAbs ≤ 2 ^ h) (hB : ∀ i j, (B i j).natAbs ≤ 2 ^ h)
    (i : Fin (m + n)) (v : BimatrixVariable m n) :
    (bimatrixIntegerColumns A B i v).natAbs ≤ 2 ^ h := by
  unfold bimatrixIntegerColumns bimatrixBasisColumns
  split
  · cases hr : finSumFinEquiv.symm i <;> cases hc : finSumFinEquiv.symm (ofLex v).1 <;>
      simp only [bimatrixEnteringColumn, bimatrixComplementaryMatrix, hr,
        neg_neg, neg_zero, Rat.num_intCast, Rat.num_zero, Int.natAbs_zero]
    · exact Nat.zero_le _
    · exact hA _ _
    · exact hB _ _
    · exact Nat.zero_le _
  · simp only [Pi.single_apply]
    split
    · simpa using Nat.one_le_pow h 2 (by decide)
    · simp

namespace BimatrixBasis
variable {A B : Fin m → Fin n → ℤ}

/-- Integer encoding of the canonically sorted selected columns. -/
def integerMatrix (basis : BimatrixBasis A B) : Matrix (Fin (m + n)) (Fin (m + n)) ℤ :=
  basisMatrix (bimatrixIntegerColumns A B) basis.basic basis.cardinality

theorem integerMatrix_map (basis : BimatrixBasis A B) :
    basis.integerMatrix.map (fun z : ℤ => (z : ℚ)) =
      basisMatrix (bimatrixBasisColumns A B) basis.basic basis.cardinality := by
  ext i j
  exact bimatrixIntegerColumns_cast A B i _

theorem integerMatrix_det_ne_zero (basis : BimatrixBasis A B) :
    basis.integerMatrix.det ≠ 0 := by
  intro hz
  apply basis.feasible.1
  rw [← basis.integerMatrix_map, ← Int.cast_det, hz, Int.cast_zero]

theorem integerMatrix_bound (basis : BimatrixBasis A B) (h : ℕ)
    (hA : ∀ i j, (A i j).natAbs ≤ 2 ^ h) (hB : ∀ i j, (B i j).natAbs ≤ 2 ^ h)
    (i j : Fin (m + n)) : (basis.integerMatrix i j).natAbs ≤ 2 ^ h :=
  bimatrixIntegerColumns_bound A B h hA hB i _

/-- Every constant or symbolic perturbation coefficient has polynomial binary width. -/
theorem dictionaryCoefficients_bounds (basis : BimatrixBasis A B) (h : ℕ)
    (hA : ∀ i j, (A i j).natAbs ≤ 2 ^ h) (hB : ∀ i j, (B i j).natAbs ≤ 2 ^ h)
    (i : Fin (m + n)) (k : Fin (m + n + 1)) :
    (PerturbedDictionary.dictionaryCoefficients
      (basisMatrix (bimatrixBasisColumns A B) basis.basic basis.cardinality)
      (fun _ => 1) i k).num.natAbs < 2 ^ IntegerBasisBounds.width (m + n) h ∧
    (PerturbedDictionary.dictionaryCoefficients
      (basisMatrix (bimatrixBasisColumns A B) basis.basic basis.cardinality)
      (fun _ => 1) i k).den < 2 ^ IntegerBasisBounds.width (m + n) h := by
  refine Fin.cases ?_ (fun j => ?_) k
  · have hh := IntegerBasisBounds.inv_mulVec_bounds basis.integerMatrix (fun _ => 1) h
      (basis.integerMatrix_bound h hA hB)
      (fun _ => Nat.one_le_pow h 2 (by decide)) basis.integerMatrix_det_ne_zero i
    simpa only [basis.integerMatrix_map, Int.cast_one,
      PerturbedDictionary.coefficient_zero] using hh
  · have hh := IntegerBasisBounds.inv_entry_bounds basis.integerMatrix h
      (basis.integerMatrix_bound h hA hB) basis.integerMatrix_det_ne_zero i j
    simpa only [basis.integerMatrix_map, PerturbedDictionary.coefficient_succ] using hh

/-- Every entering-column direction has the same polynomial binary width. -/
theorem direction_bounds (basis : BimatrixBasis A B) (h : ℕ)
    (hA : ∀ i j, (A i j).natAbs ≤ 2 ^ h) (hB : ∀ i j, (B i j).natAbs ≤ 2 ^ h)
    (v : BimatrixVariable m n) (i : Fin (m + n)) :
    ((basisMatrix (bimatrixBasisColumns A B) basis.basic basis.cardinality)⁻¹.mulVec
      (fun j => bimatrixBasisColumns A B j v) i).num.natAbs <
        2 ^ IntegerBasisBounds.width (m + n) h ∧
    ((basisMatrix (bimatrixBasisColumns A B) basis.basic basis.cardinality)⁻¹.mulVec
      (fun j => bimatrixBasisColumns A B j v) i).den <
        2 ^ IntegerBasisBounds.width (m + n) h := by
  have hh := IntegerBasisBounds.inv_mulVec_bounds basis.integerMatrix
    (fun j => bimatrixIntegerColumns A B j v) h (basis.integerMatrix_bound h hA hB)
    (fun j => bimatrixIntegerColumns_bound A B h hA hB j v)
    basis.integerMatrix_det_ne_zero i
  simpa only [basis.integerMatrix_map, bimatrixIntegerColumns_cast] using hh

/-- Ambient basis coordinates have uniformly bounded reduced rational fields. -/
theorem coordinates_bounds (basis : BimatrixBasis A B) (h : ℕ)
    (hA : ∀ i j, (A i j).natAbs ≤ 2 ^ h) (hB : ∀ i j, (B i j).natAbs ≤ 2 ^ h)
    (v : BimatrixVariable m n) :
    (basis.coordinates v).num.natAbs < 2 ^ IntegerBasisBounds.width (m + n) h ∧
      (basis.coordinates v).den < 2 ^ IntegerBasisBounds.width (m + n) h := by
  by_cases hv : v ∈ basis.basic
  · let j := (basis.basic.orderIsoOfFin basis.cardinality).symm ⟨v, hv⟩
    have he : basis.basic.orderEmbOfFin basis.cardinality j = v :=
      congrArg Subtype.val ((basis.basic.orderIsoOfFin basis.cardinality).apply_symm_apply ⟨v, hv⟩)
    rw [← he]
    simpa only [coordinates, BasisCoordinates.inverseCoordinates_on_enumeration,
      PerturbedDictionary.coefficient_zero] using basis.dictionaryCoefficients_bounds h hA hB j 0
  · rw [basis.coordinates_outside v hv]
    have hp : 1 < 2 ^ IntegerBasisBounds.width (m + n) h := by
      simpa only [pow_zero] using Nat.pow_lt_pow_right (by decide : 1 < 2)
        (show 0 < IntegerBasisBounds.width (m + n) h by unfold IntegerBasisBounds.width; omega)
    simpa only [Rat.num_zero, Rat.den_zero, Int.natAbs_zero] using
      And.intro (Nat.zero_lt_of_lt hp) hp

/-- Every path endpoint's payoff coordinates share the basis coordinate bound. -/
theorem payoffPoint_bounds (basis : BimatrixBasis A B) (h : ℕ)
    (hA : ∀ i j, (A i j).natAbs ≤ 2 ^ h) (hB : ∀ i j, (B i j).natAbs ≤ 2 ^ h)
    (i : Fin m ⊕ Fin n) :
    (basis.payoffPoint i).num.natAbs < 2 ^ IntegerBasisBounds.width (m + n) h ∧
      (basis.payoffPoint i).den < 2 ^ IntegerBasisBounds.width (m + n) h :=
  basis.coordinates_bounds h hA hB _

/-- Clearing the same endpoint's coordinates preserves polynomial field width. -/
theorem endpointCertificate_fitsWidth (basis : BimatrixBasis A B) (a b : ℤ) (h s : ℕ)
    (hA : ∀ i j, (A i j).natAbs ≤ 2 ^ h) (hB : ∀ i j, (B i j).natAbs ≤ 2 ^ h)
    (ha : a.natAbs ≤ 2 ^ s) (hb : b.natAbs ≤ 2 ^ s) :
    (bimatrixEndpointCertificate basis.payoffPoint a b).FitsWidth
      (bimatrixEndpointWidth m n (IntegerBasisBounds.width (m + n) h) s) :=
  bimatrixEndpointCertificate_fitsWidth basis.payoffPoint a b _ s
    (fun i => (basis.payoffPoint_bounds h hA hB i).1.le)
    (fun i => (basis.payoffPoint_bounds h hA hB i).2.le) ha hb

end BimatrixBasis
end GameTheory.Finite
