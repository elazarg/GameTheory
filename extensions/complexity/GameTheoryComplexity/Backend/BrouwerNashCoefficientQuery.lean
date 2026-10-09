import GameTheoryComplexity.Backend.BinarySignedIndicator
import GameTheoryComplexity.Backend.BrouwerNashProgram

/-! Coefficient equations connecting unary scalar queries with the canonical gate factories. -/
namespace GameTheory.Complexity.Backend.BrouwerNashCoefficientQuery
open _root_.Complexity _root_.Complexity.Cobham
open GameTheory.Finite

/-- Both input contributions are retained when the two references coincide. -/
theorem affine₂_coefficients {k : ℕ} (a z : Fin k) (ca cz : ℤ)
    (r : Fin (k * 2)) :
    (BrouwerNashProgram.affine₂ a z ca cz 0).coefficients r =
      (if r = finProdFinEquiv (a, 1) then ca else 0) +
      (if r = finProdFinEquiv (z, 1) then cz else 0) := by
  rcases finProdFinEquiv.surjective r with ⟨⟨j, bit⟩, rfl⟩
  by_cases hb : bit = 0
  · subst bit
    simp [BrouwerNashProgram.affine₂, GameTheory.Finite.BimatrixArithmeticGate.gate,
      GameTheory.Finite.BimatrixArithmeticGate.coefficients]
  · have hb : bit = 1 := by
      apply Fin.ext
      have hlt := bit.isLt
      have hne : bit.val ≠ 0 := fun h => hb (Fin.ext h)
      omega
    subst bit
    simp [BrouwerNashProgram.affine₂, GameTheory.Finite.BimatrixArithmeticGate.gate,
      GameTheory.Finite.BimatrixArithmeticGate.coefficients]
/-- A ruler equality guard preserves the selected signed value exactly. -/
theorem select_value (out ruler word : List Bool) :
    binarySignedValue (caseBit₀ (lenEqFlag out ruler) word []) =
      if out.length = ruler.length then binarySignedValue word else 0 := by
  rcases lenEqFlag_flag out ruler with h | h
  · rw [h]
    simp only [(lenEqFlag_eq_true_iff _ _).mp h, ite_true, caseBit₀]
    rfl
  · have he : out.length ≠ ruler.length := by
      intro he
      have ht := (lenEqFlag_eq_true_iff out ruler).mpr he
      rw [h] at ht
      contradiction
    rw [h]
    simp only [he, ite_false, caseBit₀]
    rfl

/-- Two signed indicator queries implement an affine gate without imposing distinct references. -/
theorem affine₂_indicator_value {k : ℕ} (row input₀ input₁ scalar₀ scalar₁ : List Bool)
    (r : Fin (k * 2)) (a z : Fin k) (hr : row.length = r.val)
    (ha : input₀.length = a.val) (hz : input₁.length = z.val) :
    binarySignedValue (binarySignedIndicator ![row, input₀, scalar₀]) +
      binarySignedValue (binarySignedIndicator ![row, input₁, scalar₁]) =
      (BrouwerNashProgram.affine₂ a z (binarySignedValue scalar₀)
        (binarySignedValue scalar₁) 0).coefficients r := by
  rw [binarySignedIndicator_index _ _ _ r a hr ha,
    binarySignedIndicator_index _ _ _ r z hr hz, affine₂_coefficients]

/-- Paired-action equality is exactly the unary quotient and odd-parity test. -/
theorem pairedAction_iff {k : ℕ} (r : Fin (k * 2)) (a : Fin k) :
    (r.val / 2 = a.val ∧ r.val % 2 = 1) ↔ r = finProdFinEquiv (a, 1) := by
  rw [Fin.ext_iff]
  change (r.val / 2 = a.val ∧ r.val % 2 = 1) ↔ r.val = 1 + 2 * a.val
  omega

/-- A single affine input selects precisely its positive paired action. -/
theorem affine₁_coefficients {k : ℕ} (a : Fin k) (ca : ℤ) (r : Fin (k * 2)) :
    (BimatrixArithmeticGate.gate (fun j => if j = a then ca else 0) 0).coefficients r =
      if r = finProdFinEquiv (a, 1) then ca else 0 := by
  have hgate : BimatrixArithmeticGate.gate (fun j => if j = a then ca else 0) 0 =
      BrouwerNashProgram.affine₂ a a ca 0 0 := by
    unfold BrouwerNashProgram.affine₂
    congr 1
    funext j
    simp
  rw [hgate, affine₂_coefficients]
  simp

end GameTheory.Complexity.Backend.BrouwerNashCoefficientQuery