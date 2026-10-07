import GameTheoryComplexity.Backend.NashCertificateFormat

/-! Encoding bounded numerator certificates as fixed-width little-endian fields,
with an exact length and a round trip through the verifier's shared parser. -/

namespace GameTheory.Complexity.Backend

open GameTheory.Finite

/-- Certificate numbers in denominator, utility, row-weight, column-weight order. -/
def nashCertificateNumbers {q : ℕ} (c : NumeratorCertificate q) : List ℕ :=
  [c.rowDenominator, c.colDenominator, c.rowUtilityNumerator, c.colUtilityNumerator] ++
    List.ofFn c.rowWeights ++ List.ofFn c.colWeights

/-- Concatenate fixed-width little-endian certificate fields in parser order. -/
def encodeNashCertificate {q : ℕ} (W : ℕ) (c : NumeratorCertificate q) : List Bool :=
  (nashCertificateNumbers c).flatMap (Nat.toBitsLE W)

private theorem length_flatMap_fixed {α β : Type*} (xs : List α) (f : α → List β)
    (w : ℕ) (hf : ∀ a ∈ xs, (f a).length = w) :
    (xs.flatMap f).length = xs.length * w := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha := hf a (by simp)
    have ht : ∀ b ∈ xs, (f b).length = w := fun b hb => hf b (by simp [hb])
    simp only [List.flatMap_cons, List.length_append, List.length_cons, ha, ih ht]
    simp [Nat.add_mul, Nat.add_comm]

private theorem block_flatMap_fixed {α β : Type*} (xs : List α) (f : α → List β)
    (w : ℕ) (hf : ∀ a ∈ xs, (f a).length = w) (k : ℕ) (hk : k < xs.length) :
    ((xs.flatMap f).drop (k * w)).take w = f xs[k] := by
  induction xs generalizing k with
  | nil => simp at hk
  | cons a xs ih =>
    have ha := hf a (by simp)
    have ht : ∀ b ∈ xs, (f b).length = w := fun b hb => hf b (by simp [hb])
    cases k with
    | zero =>
      simp only [Nat.zero_mul, List.drop_zero, List.flatMap_cons, List.getElem_cons_zero]
      rw [← ha, List.take_append_length]
    | succ k =>
      have hk' : k < xs.length := by simpa using hk
      simp only [List.flatMap_cons, Nat.succ_mul, List.getElem_cons_succ]
      rw [Nat.add_comm, ← ha, List.drop_length_add_append]
      simpa only [ha] using ih ht k hk'

theorem nashCertificateNumbers_length {q : ℕ} (c : NumeratorCertificate q) :
    (nashCertificateNumbers c).length = 2 * q + 4 := by
  simp [nashCertificateNumbers]
  omega

/-- Each certificate uses exactly two weight vectors and four scalar fields. -/
theorem encodeNashCertificate_length {q : ℕ} (W : ℕ) (c : NumeratorCertificate q) :
    (encodeNashCertificate W c).length = (2 * q + 4) * W := by
  rw [encodeNashCertificate, length_flatMap_fixed _ _ W
    (fun _ _ => Nat.length_toBitsLE _ _), nashCertificateNumbers_length]

theorem nashCertificateField_encode {q : ℕ} (W : ℕ) (c : NumeratorCertificate q)
    (k : ℕ) (hk : k < (nashCertificateNumbers c).length) :
    nashCertificateField W k (encodeNashCertificate W c) =
      Nat.toBitsLE W (nashCertificateNumbers c)[k] := by
  exact block_flatMap_fixed (nashCertificateNumbers c) (Nat.toBitsLE W) W
    (fun _ _ => Nat.length_toBitsLE _ _) k hk

private theorem scalar_numbers {q : ℕ} (c : NumeratorCertificate q) :
    (nashCertificateNumbers c)[0]'(by rw [nashCertificateNumbers_length]; omega) =
      c.rowDenominator ∧
    (nashCertificateNumbers c)[1]'(by rw [nashCertificateNumbers_length]; omega) =
      c.colDenominator ∧
    (nashCertificateNumbers c)[2]'(by rw [nashCertificateNumbers_length]; omega) =
      c.rowUtilityNumerator ∧
    (nashCertificateNumbers c)[3]'(by rw [nashCertificateNumbers_length]; omega) =
      c.colUtilityNumerator := by
  simp [nashCertificateNumbers]

private theorem row_number {q : ℕ} (c : NumeratorCertificate q) (i : Fin q) :
    (nashCertificateNumbers c)[4 + i.val]'(by rw [nashCertificateNumbers_length]; omega) =
      c.rowWeights i := by
  simp only [show 4 + i.val = i.val + 1 + 1 + 1 + 1 by omega]
  simp only [nashCertificateNumbers, List.cons_append, List.nil_append,
    List.getElem_cons_succ]
  rw [List.getElem_append_left (by simp)]
  simp

private theorem col_number {q : ℕ} (c : NumeratorCertificate q) (i : Fin q) :
    (nashCertificateNumbers c)[4 + q + i.val]'(by rw [nashCertificateNumbers_length]; omega) =
      c.colWeights i := by
  simp only [show 4 + q + i.val = (q + i.val) + 1 + 1 + 1 + 1 by omega]
  simp only [nashCertificateNumbers, List.cons_append, List.nil_append,
    List.getElem_cons_succ]
  rw [List.getElem_append_right (by simp)]
  simp

/-- Every bounded certificate round-trips through the exact parser used by the
machine verifier, including its fixed-width zero padding. -/
theorem decodeNashCertificate_encode {q : ℕ} (W : ℕ) (c : NumeratorCertificate q)
    (hdp : c.rowDenominator < 2 ^ W) (hdq : c.colDenominator < 2 ^ W)
    (hU : c.rowUtilityNumerator < 2 ^ W) (hV : c.colUtilityNumerator < 2 ^ W)
    (ha : ∀ i, c.rowWeights i < 2 ^ W) (hb : ∀ i, c.colWeights i < 2 ^ W) :
    decodeNashCertificate q W (encodeNashCertificate W c) = c := by
  have hk (k : ℕ) (h : k < 2 * q + 4) : k < (nashCertificateNumbers c).length := by
    rwa [nashCertificateNumbers_length]
  have hs := scalar_numbers c
  have hrow (i : Fin q) : Nat.fromBitsLE
      (nashCertificateField W (4 + i) (encodeNashCertificate W c)) = c.rowWeights i := by
    rw [nashCertificateField_encode W c _ (hk _ (by omega)), row_number]
    exact Nat.fromBitsLE_toBitsLE (ha i)
  have hcol (i : Fin q) : Nat.fromBitsLE
      (nashCertificateField W (4 + q + i) (encodeNashCertificate W c)) = c.colWeights i := by
    rw [nashCertificateField_encode W c _ (hk _ (by omega)), col_number]
    exact Nat.fromBitsLE_toBitsLE (hb i)
  cases c
  simp only [decodeNashCertificate, nashCertificateField_encode W _ _ (hk 0 (by omega)),
    nashCertificateField_encode W _ _ (hk 1 (by omega)),
    nashCertificateField_encode W _ _ (hk 2 (by omega)),
    nashCertificateField_encode W _ _ (hk 3 (by omega)), hs.1, hs.2.1, hs.2.2.1, hs.2.2.2,
    Nat.fromBitsLE_toBitsLE hdp, Nat.fromBitsLE_toBitsLE hdq,
    Nat.fromBitsLE_toBitsLE hU, Nat.fromBitsLE_toBitsLE hV, hrow, hcol]

end GameTheory.Complexity.Backend
