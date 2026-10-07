import GameTheoryComplexity.Backend.BinaryCertificateArithmetic
import GameTheoryComplexity.Backend.BimatrixCertificateVerifier
import GameTheoryComplexity.Backend.BimatrixCertificateVerifierCorrectness
import GameTheoryComplexity.Backend.NashCertificateEncoding
import GameTheoryComplexity.Backend.NashNP
import GameTheory.Finite.BimatrixNashCertificateCorrectness

/-! Binary carry, padded codecs, actual table parsing, and malformed numerator
controls for the payoff-constrained mixed-equilibrium certificate. -/

namespace GameTheory.Complexity.Tests.NashCertificate

open GameTheory.Complexity.Backend
open GameTheory.Finite GameTheory.Finite.BimatrixTable

example : binaryCertificateAdd ![[true, true, true], [true]] =
    [false, false, false, true] := by decide

example : binaryCertificateLE ![[true, true, false], [false, false, true]] =
    [true] := by decide

example : binaryCertificateLE ![[true, false, false], [true]] = [true] := by decide

example : binaryCertificateVerifier ![[], []] = [false] := by decide

example : binaryCertificateVerifier ![[], List.replicate 91 false] = [false] := by decide

example : binaryCertificateVerifier ![[], List.replicate 93 false] = [false] := by decide

example : binaryCertificateVerifier ![[], List.replicate 92 false] = [false] := by decide

example : nashPairedVerdict [] = [false] := by decide

def oneCertificate : NumeratorCertificate 1 :=
  ⟨fun _ => 1, fun _ => 1, 1, 1, 1, 1⟩

example : (encodeNashCertificate 4 oneCertificate).length = 24 := by
  rw [encodeNashCertificate_length]

example : decodeNashCertificate 1 4 (encodeNashCertificate 4 oneCertificate) =
    oneCertificate := by
  exact decodeNashCertificate_encode _ _ (by decide) (by decide) (by decide)
    (by decide) (fun _ => by change 1 < 2 ^ 4; decide)
    (fun _ => by change 1 < 2 ^ 4; decide)

def positiveTable : List Bool := encodeTable 1 (fun _ _ => 1)

def tableCertificate : NumeratorCertificate (decodeDimension positiveTable) :=
  ⟨fun _ => 1, fun _ => 1, 1, 1, 1, 1⟩

theorem tableCertificate_accepts :
    verifyNashNumerators (fun i j => decodedPayoff positiveTable i j) tableCertificate =
      true := by decide

theorem positiveTable_has_high_payoff_nash : positiveTable ∈ unitPayoffLanguage :=
  mem_unitPayoffLanguage_of_verify positiveTable tableCertificate tableCertificate_accepts

/-- Simplex equations and threshold bounds hold, but the supported payoff is
one rather than the claimed two. Support equality must reject this certificate. -/
def wrongSupportPayoff : NumeratorCertificate (decodeDimension positiveTable) :=
  ⟨fun _ => 1, fun _ => 1, 1, 1, 2, 1⟩

example : verifyNashNumerators (fun i j => decodedPayoff positiveTable i j)
    wrongSupportPayoff = false := by decide

private theorem one_bounded (input : List Bool) :
    1 < 2 ^ (certificateWidthWord input).length := by
  have hw : 1 ≤ (certificateWidthWord input).length := by
    rw [certificateWidthWord_length]
    omega
  exact (by decide : 1 < (2 : ℕ) ^ 1).trans_le (pow_le_pow_right' (by decide) hw)

private theorem two_bounded (input : List Bool) :
    2 < 2 ^ (certificateWidthWord input).length := by
  have hw : 2 ≤ (certificateWidthWord input).length := by
    rw [certificateWidthWord_length]
    omega
  exact (by decide : 2 < (2 : ℕ) ^ 2).trans_le (pow_le_pow_right' (by decide) hw)

def positiveWord : List Bool :=
  encodeNashCertificate (certificateWidthWord positiveTable).length tableCertificate

private theorem positiveWord_parses :
    decodeNashCertificate (decodeDimension positiveTable)
      (certificateWidthWord positiveTable).length positiveWord = tableCertificate := by
  exact decodeNashCertificate_encode _ _ (one_bounded _) (one_bounded _)
    (one_bounded _) (one_bounded _) (fun _ => one_bounded _) (fun _ => one_bounded _)

private theorem positiveWord_length :
    positiveWord.length = (4 + 2 * decodeDimension positiveTable) *
      (certificateWidthWord positiveTable).length := by
  simpa only [positiveWord, Nat.add_comm] using encodeNashCertificate_length
    (certificateWidthWord positiveTable).length tableCertificate

theorem positive_machine_accepts :
    binaryCertificateVerifier ![positiveTable, positiveWord] = [true] := by
  rw [binaryCertificateVerifier_eq_true_iff, positiveWord_parses]
  exact ⟨positiveWord_length,
    (verifyNashNumerators_eq_true_iff _ _).mp tableCertificate_accepts⟩

private theorem rejected_of_not_accepted (input cert : List Bool)
    (h : binaryCertificateVerifier ![input, cert] ≠ [true]) :
    binaryCertificateVerifier ![input, cert] = [false] := by
  rcases binaryCertificateVerifier_flag ![input, cert] with ht | hf
  · exact False.elim (h ht)
  · exact hf

theorem wrong_supported_payoff_machine_rejects :
    binaryCertificateVerifier ![positiveTable,
      encodeNashCertificate (certificateWidthWord positiveTable).length wrongSupportPayoff] =
        [false] := by
  apply rejected_of_not_accepted
  intro h
  have hv := (binaryCertificateVerifier_eq_true_iff _ _).mp h |>.2
  rw [decodeNashCertificate_encode _ _ (one_bounded _) (one_bounded _)
    (two_bounded _) (one_bounded _) (fun _ => one_bounded _) (fun _ => one_bounded _)] at hv
  have hbad : ¬ wrongSupportPayoff.Valid (fun i j => decodedPayoff positiveTable i j) := by
    decide
  exact hbad hv

theorem extra_bit_machine_rejects :
    binaryCertificateVerifier ![positiveTable, positiveWord ++ [false]] = [false] := by
  apply rejected_of_not_accepted
  intro h
  have hl := (binaryCertificateVerifier_eq_true_iff _ _).mp h |>.1
  rw [List.length_append, List.length_singleton, positiveWord_length] at hl
  omega

theorem missing_bit_machine_rejects :
    binaryCertificateVerifier ![positiveTable, positiveWord.drop 1] = [false] := by
  apply rejected_of_not_accepted
  intro h
  have hl := (binaryCertificateVerifier_eq_true_iff _ _).mp h |>.1
  rw [List.length_drop] at hl
  have hlen := positiveWord_length
  have hpositive : 0 < positiveWord.length := by
    rw [hlen, certificateWidthWord_length]
    apply Nat.mul_pos
    · omega
    · omega
  omega

example : nashCertificateField 4 0 [true] = [true] := by decide

example : nashCertificateField 4 1 [true] = [] := by decide

theorem zero_dimension_rejects (A : Fin 0 → Fin 0 → ℤ) (c : NumeratorCertificate 0) :
    verifyNashNumerators A c = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  rcases (verifyNashNumerators_eq_true_iff A c).mp h with ⟨hpos, _, hsum, _⟩
  simp at hsum
  omega

end GameTheory.Complexity.Tests.NashCertificate
