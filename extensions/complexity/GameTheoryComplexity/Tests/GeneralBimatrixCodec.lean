import GameTheoryComplexity.Backend.GeneralBimatrixCertificateCodec
import GameTheoryComplexity.Backend.GeneralBimatrixVerifierCorrectness
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-! Signed rectangular encodings retain independent payoffs and reject false Nash certificates. -/
namespace GameTheory.Complexity.Backend.Tests

private def rowPayoff (_ : ℕ) (j : ℕ) : ℤ := if j = 0 then -3 else -1
private def colPayoff (_ : ℕ) (j : ℕ) : ℤ := if j = 0 then 2 else -2
private def input : List Bool := encodeGeneralInstance 1 2 3 rowPayoff colPayoff

example : GeneralInstanceValid input := encodeGeneralInstance_valid 1 2 3 _ _ (by decide)
  (by decide) (by decide)
example : generalRowCount input = 1 ∧ generalColCount input = 2 ∧
    generalCoefficientBits input = 3 := by simp [input]
example : decodeGeneralPayoff false input 0 0 = -3 := by
  exact decodeGeneralPayoff_encode 1 2 3 _ _ false 0 0 (by decide) (by decide) (by decide)
example : decodeGeneralPayoff true input 0 0 = 2 := by
  exact decodeGeneralPayoff_encode 1 2 3 _ _ true 0 0 (by decide) (by decide) (by decide)
example : decodeGeneralPayoff false input 0 1 = -1 := by
  exact decodeGeneralPayoff_encode 1 2 3 _ _ false 0 1 (by decide) (by decide) (by decide)
example : decodeGeneralPayoff true input 0 1 = -2 := by
  exact decodeGeneralPayoff_encode 1 2 3 _ _ true 0 1 (by decide) (by decide) (by decide)

private def certificate : GameTheory.Finite.BimatrixCertificate 1 2 where
  rowWeights _ := 1
  colWeights j := if j.val = 0 then 1 else 0
  rowDenominator := 1
  colDenominator := 1
  rowUtilityNumerator := -3
  colUtilityNumerator := 2

private theorem certificate_fits : certificate.FitsWidth 4 := by
  unfold GameTheory.Finite.BimatrixCertificate.FitsWidth
  decide
example : decodeGeneralCertificate 1 2 4 (encodeGeneralCertificate 4 certificate) =
    certificate := decodeGeneralCertificate_encode _ certificate_fits
example : (encodeGeneralCertificate 4 certificate).length = 36 := by
  exact encodeGeneralCertificate_length 4 certificate
example : generalNatField 4 2 (encodeGeneralCertificate 4 certificate) = 0 ∧
    generalNatField 4 3 (encodeGeneralCertificate 4 certificate) = 3 ∧
    generalNatField 4 4 (encodeGeneralCertificate 4 certificate) = 2 ∧
    generalNatField 4 5 (encodeGeneralCertificate 4 certificate) = 0 := by decide

example : GameTheory.Finite.verifyBimatrixCertificate
    (fun i j => rowPayoff i.val j.val) (fun i j => colPayoff i.val j.val) certificate = true :=
  by decide
example : GameTheory.Finite.verifyBimatrixCertificate
    (fun i j => rowPayoff i.val j.val) (fun i j => colPayoff i.val j.val)
    { certificate with rowDenominator := 2 } = false := by decide
example : GameTheory.Finite.verifyBimatrixCertificate
    (fun i j => rowPayoff i.val j.val) (fun i j => colPayoff i.val j.val)
    { certificate with
      colWeights := fun j : Fin 2 => if j.val = 1 then 1 else 0
      rowUtilityNumerator := -1
      colUtilityNumerator := -2 } = false := by decide

example : ¬ GeneralInstanceValid [true, false, true, true, false, true, true, true] := by decide
example : ¬ GeneralInstanceValid [] := by decide

-- Signed utility fields may overlap: their difference is the mathematical value.
example : decodeGeneralCertificate 1 2 4
    (encodeGeneralFields 4 9 (fun index =>
      if index = 2 then 1 else if index = 3 then 4 else generalCertificateField certificate index)) =
    certificate := by
  unfold decodeGeneralCertificate certificate
  congr 1 <;> try rfl
  · funext i; fin_cases i; rfl
  · funext j; fin_cases j <;> rfl

private theorem certificateWidth_ge_four : 4 ≤ generalCertificateWidth input.length := by
  decide

private theorem fits_width_mono {c : GameTheory.Finite.BimatrixCertificate 1 2}
    (hc : c.FitsWidth 4) : c.FitsWidth (generalCertificateWidth input.length) := by
  have hp := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) certificateWidth_ge_four
  obtain ⟨hd, he, hr, hs, hu, hv⟩ := hc
  exact ⟨hd.trans_le hp, he.trans_le hp, fun i => (hr i).trans_le hp,
    fun j => (hs j).trans_le hp, hu.trans_le hp, hv.trans_le hp⟩

private theorem decoded_row_payoff :
    (fun (i : Fin 1) (j : Fin 2) => decodeGeneralPayoff false input i.val j.val) =
      fun i j => rowPayoff i.val j.val := by
  funext i j
  exact decodeGeneralPayoff_encode 1 2 3 _ _ false i.val j.val i.isLt j.isLt
    (by fin_cases i; fin_cases j <;> decide)

private theorem decoded_col_payoff :
    (fun (i : Fin 1) (j : Fin 2) => decodeGeneralPayoff true input i.val j.val) =
      fun i j => colPayoff i.val j.val := by
  funext i j
  exact decodeGeneralPayoff_encode 1 2 3 _ _ true i.val j.val i.isLt j.isLt
    (by fin_cases i; fin_cases j <;> decide)

private theorem input_valid : GeneralInstanceValid input :=
  encodeGeneralInstance_valid 1 2 3 _ _ (by decide) (by decide) (by decide)

set_option backward.isDefEq.respectTransparency false in
private theorem encoded_verdict_iff (c : GameTheory.Finite.BimatrixCertificate 1 2)
    (hc : c.FitsWidth 4) :
    generalBimatrixVerdict ![input, encodeGeneralCertificate
      (generalCertificateWidth input.length) c] = [true] ↔
      c.Valid (fun i j => rowPayoff i.val j.val) (fun i j => colPayoff i.val j.val) := by
  rw [generalBimatrixVerdict_eq_true_iff]
  simp only [input_valid, true_and, not_true_eq_false, false_and, or_false]
  have hlen : (encodeGeneralCertificate (generalCertificateWidth input.length) c).length =
      (6 + generalRowCount input + generalColCount input) * generalCertificateWidth input.length := by
    simp [input]
  simp only [hlen, true_and]
  change (decodeGeneralCertificate 1 2 (generalCertificateWidth input.length)
    (encodeGeneralCertificate (generalCertificateWidth input.length) c)).Valid _ _ ↔ _
  rw [decodeGeneralCertificate_encode c (fits_width_mono hc)]
  change c.Valid (fun (i : Fin 1) (j : Fin 2) => decodeGeneralPayoff false input i.val j.val)
    (fun (i : Fin 1) (j : Fin 2) => decodeGeneralPayoff true input i.val j.val) ↔ _
  rw [decoded_row_payoff, decoded_col_payoff]

-- The actual polynomial-time verifier accepts the signed rectangular instance.
example : generalBimatrixVerdict ![input,
    encodeGeneralCertificate (generalCertificateWidth input.length) certificate] = [true] := by
  apply (encoded_verdict_iff certificate certificate_fits).mpr
  decide

-- The actual verifier rejects an incorrect signed best-response numerator.
example : generalBimatrixVerdict ![input,
    encodeGeneralCertificate (generalCertificateWidth input.length)
      { certificate with rowUtilityNumerator := -2 }] ≠ [true] := by
  intro h
  have hc := (encoded_verdict_iff _
    (by unfold GameTheory.Finite.BimatrixCertificate.FitsWidth; decide)).mp h
  exact (by decide : ¬ _) hc

private def dominatedCertificate : GameTheory.Finite.BimatrixCertificate 1 2 :=
  { certificate with
    colWeights := fun j : Fin 2 => if j.val = 1 then 1 else 0
    rowUtilityNumerator := -1
    colUtilityNumerator := -2 }

-- Correct denominator sums do not excuse assigning positive weight to a dominated column.
example : generalBimatrixVerdict ![input,
    encodeGeneralCertificate (generalCertificateWidth input.length) dominatedCertificate] ≠ [true] := by
  intro h
  have hc := (encoded_verdict_iff _
    (by unfold GameTheory.Finite.BimatrixCertificate.FitsWidth; decide)).mp h
  exact (by decide : ¬ _) hc

private def secondColPayoff (_ : ℕ) (j : ℕ) : ℤ := if j = 0 then -2 else 2
private def secondInput : List Bool := encodeGeneralInstance 1 2 3 rowPayoff secondColPayoff
private def secondCertificate : GameTheory.Finite.BimatrixCertificate 1 2 :=
  { certificate with
    colWeights := fun j : Fin 2 => if j.val = 1 then 1 else 0
    rowUtilityNumerator := -1 }

-- Occupying the second column detects accidental transposition of a rectangular payoff matrix.
set_option backward.isDefEq.respectTransparency false in
example : generalBimatrixVerdict ![secondInput,
    encodeGeneralCertificate (generalCertificateWidth secondInput.length) secondCertificate] = [true] := by
  apply (generalBimatrixVerdict_eq_true_iff _ _).mpr
  left
  refine ⟨encodeGeneralInstance_valid 1 2 3 _ _ (by decide) (by decide) (by decide), ?_, ?_⟩
  · simp [secondInput]
  · have hlen : secondInput.length = input.length := by simp [secondInput, input]
    have hc : secondCertificate.FitsWidth (generalCertificateWidth secondInput.length) := by
      rw [hlen]
      apply fits_width_mono
      unfold GameTheory.Finite.BimatrixCertificate.FitsWidth
      decide
    change (decodeGeneralCertificate 1 2 (generalCertificateWidth secondInput.length)
      (encodeGeneralCertificate (generalCertificateWidth secondInput.length) secondCertificate)).Valid _ _
    rw [decodeGeneralCertificate_encode _ hc]
    have hA : (fun (i : Fin 1) (j : Fin 2) => decodeGeneralPayoff false secondInput i.val j.val) =
        fun i j => rowPayoff i.val j.val := by
      funext i j
      exact decodeGeneralPayoff_encode 1 2 3 _ _ false i.val j.val i.isLt j.isLt
        (by fin_cases i; fin_cases j <;> decide)
    have hB : (fun (i : Fin 1) (j : Fin 2) => decodeGeneralPayoff true secondInput i.val j.val) =
        fun i j => secondColPayoff i.val j.val := by
      funext i j
      exact decodeGeneralPayoff_encode 1 2 3 _ _ true i.val j.val i.isLt j.isLt
        (by fin_cases i; fin_cases j <;> decide)
    change secondCertificate.Valid
      (fun (i : Fin 1) (j : Fin 2) => decodeGeneralPayoff false secondInput i.val j.val)
      (fun (i : Fin 1) (j : Fin 2) => decodeGeneralPayoff true secondInput i.val j.val)
    rw [hA, hB]
    decide

end GameTheory.Complexity.Backend.Tests


