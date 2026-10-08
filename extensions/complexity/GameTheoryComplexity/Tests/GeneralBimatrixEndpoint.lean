import GameTheoryComplexity.BimatrixNash

/-! Endpoint serialization controls for signed rectangular inputs and the
malformed-input boundary of the emission theorem. -/
namespace GameTheory.Complexity.Tests.GeneralBimatrixEndpoint
open Backend GameTheory.Finite GameTheory.Math

private def input : List Bool :=
  encodeGeneralInstance 1 2 3 (fun _ j => if j = 0 then -3 else 2)
    (fun _ j => if j = 0 then 1 else -2)

-- Any certified non-source complementary basis of this independently signed
-- rectangular game supplies a word accepted by the existing binary relation.
example (basis : GeneralBimatrixShiftedBasis input)
    (hc : ComplementaryLabels.IsComplementary basis.nonbasic)
    (hs : basis ≠ bimatrixSourceBasis
      (fun i j => decodeGeneralPayoff false input i.val j.val +
        ((2 : ℤ) ^ generalCoefficientBits input + 1))
      (fun i j => decodeGeneralPayoff true input i.val j.val +
        ((2 : ℤ) ^ generalCoefficientBits input + 1))) :
    generalBimatrixRelation input (generalBimatrixEndpointWord input basis) :=
  generalBimatrixEndpointWord_accept input
    (encodeGeneralInstance_valid 1 2 3 _ _ (by decide) (by decide) (by decide)) basis hc hs

-- Source bases are excluded from honest endpoint emission; a source word on
-- an empty malformed input also cannot replace the designated empty fallback.
example (basis : GeneralBimatrixShiftedBasis []) :
    ¬ generalBimatrixRelation [] (generalBimatrixEndpointWord [] basis) := by
  intro h
  have heq := (generalBimatrixRelation_invalid_iff [] _ (by decide)).mp h
  have hl := congrArg List.length heq
  simp only [generalBimatrixEndpointWord, encodeGeneralCertificate_length, List.length_nil] at hl
  have hp : 0 < (6 + generalRowCount [] + generalColCount []) * generalCertificateWidth 0 :=
    Nat.mul_pos (by omega) (by unfold generalCertificateWidth; omega)
  exact (Nat.ne_of_gt hp) hl

example : generalBimatrixRelation [] [] := Or.inr ⟨by decide, rfl⟩

end GameTheory.Complexity.Tests.GeneralBimatrixEndpoint
