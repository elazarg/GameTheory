import GameTheoryComplexity.Backend.GeneralBimatrixCodec

/-! Binary mixed-strategy certificates with unsigned probabilities and signed utilities. -/
namespace GameTheory.Complexity.Backend

/-- Polynomial field width in serialized instance length. -/
def generalCertificateWidth (L : ℕ) : ℕ := (2 * L + 2) * (8 * L + 6) + 1

/-- Decode scalar and vector fields without assuming validity. -/
def decodeGeneralCertificate (m n W : ℕ) (word : List Bool) :
    GameTheory.Finite.BimatrixCertificate m n where
  rowDenominator := generalNatField W 0 word
  colDenominator := generalNatField W 1 word
  rowUtilityNumerator := (generalNatField W 2 word : ℤ) - (generalNatField W 3 word : ℤ)
  colUtilityNumerator := (generalNatField W 4 word : ℤ) - (generalNatField W 5 word : ℤ)
  rowWeights i := generalNatField W (6 + i.val) word
  colWeights j := generalNatField W (6 + m + j.val) word

/-- Canonical values use disjoint positive and negative utility magnitudes. -/
def generalCertificateField {m n : ℕ} (c : GameTheory.Finite.BimatrixCertificate m n)
    (index : ℕ) : ℕ :=
  if index = 0 then c.rowDenominator else
  if index = 1 then c.colDenominator else
  if index = 2 then c.rowUtilityNumerator.toNat else
  if index = 3 then (-c.rowUtilityNumerator).toNat else
  if index = 4 then c.colUtilityNumerator.toNat else
  if index = 5 then (-c.colUtilityNumerator).toNat else
  if hi : index - 6 < m then c.rowWeights ⟨index - 6, hi⟩ else
  if hj : index - (6 + m) < n then c.colWeights ⟨index - (6 + m), hj⟩ else 0

/-- Serialize six scalar fields and the two mixed-strategy vectors. -/
def encodeGeneralCertificate {m n : ℕ} (W : ℕ)
    (c : GameTheory.Finite.BimatrixCertificate m n) : List Bool :=
  encodeGeneralFields W (6 + m + n) (generalCertificateField c)

@[simp] theorem encodeGeneralCertificate_length {m n : ℕ} (W : ℕ)
    (c : GameTheory.Finite.BimatrixCertificate m n) :
    (encodeGeneralCertificate W c).length = (6 + m + n) * W := by
  simp [encodeGeneralCertificate]

/-- Every canonical scalar or probability field inherits the certificate bound. -/
theorem generalCertificateField_lt {m n W : ℕ}
    (c : GameTheory.Finite.BimatrixCertificate m n) (hc : c.FitsWidth W) (index : ℕ) :
    generalCertificateField c index < 2 ^ W := by
  obtain ⟨hp, hq, hr, hs, hu, hv⟩ := hc
  unfold generalCertificateField
  split
  · exact hp
  split
  · exact hq
  split
  · omega
  split
  · omega
  split
  · omega
  split
  · omega
  split
  · exact hr _
  split
  · exact hs _
  · exact Nat.two_pow_pos W

/-- Every binary field is exactly the canonical value's width-bit encoding. -/
theorem generalCertificate_binaryField {m n : ℕ} (W : ℕ)
    (c : GameTheory.Finite.BimatrixCertificate m n) (index : ℕ) (hi : index < 6 + m + n) :
    generalBinaryField W index (encodeGeneralCertificate W c) =
      Nat.toBitsLE W (generalCertificateField c index) :=
  generalBinaryField_encode W (6 + m + n) _ index hi

/-- Decode the canonical serialization of any certificate fitting the field width. -/
theorem decodeGeneralCertificate_encode {m n W : ℕ}
    (c : GameTheory.Finite.BimatrixCertificate m n) (hc : c.FitsWidth W) :
    decodeGeneralCertificate m n W (encodeGeneralCertificate W c) = c := by
  have hf (index : ℕ) (hi : index < 6 + m + n) :
      generalNatField W index (encodeGeneralCertificate W c) = generalCertificateField c index :=
    generalNatField_encode W _ _ index hi (generalCertificateField_lt c hc index)
  have hrow (i : Fin m) : generalCertificateField c (6 + i.val) = c.rowWeights i := by
    simp only [generalCertificateField]
    split <;> try omega
    split <;> try omega
    split <;> try omega
    split <;> try omega
    split <;> try omega
    split <;> try omega
    split
    · congr 1; apply Fin.ext; simp
    · omega
  have hcol (j : Fin n) : generalCertificateField c (6 + m + j.val) = c.colWeights j := by
    simp only [generalCertificateField]
    split <;> try omega
    split <;> try omega
    split <;> try omega
    split <;> try omega
    split <;> try omega
    split <;> try omega
    split
    · omega
    split
    · congr 1; apply Fin.ext; simp
    · omega
  cases c
  unfold decodeGeneralCertificate
  congr 1
  · funext i
    rw [hf _ (by omega), hrow]
  · funext j
    rw [hf _ (by omega), hcol]
  · simp [hf 0 (by omega), generalCertificateField]
  · simp [hf 1 (by omega), generalCertificateField]
  · rw [hf 2 (by omega), hf 3 (by omega)]
    dsimp only [generalCertificateField]
    norm_num only
    exact Int.toNat_sub_toNat_neg _
  · rw [hf 4 (by omega), hf 5 (by omega)]
    dsimp only [generalCertificateField]
    norm_num only
    exact Int.toNat_sub_toNat_neg _

end GameTheory.Complexity.Backend

