import GameTheoryComplexity.Backend.GeneralBimatrixProblem
import GameTheory.Finite.BimatrixCramerCertificate

/-! Serialize the equilibrium at a supplied complementary endpoint.
The binary word uses the existing relation and preserves the endpoint through
a common Cramer denominator. No algorithmic cost is asserted for this map. -/
namespace GameTheory.Complexity.Backend
open GameTheory.Finite GameTheory.Math

/-- Feasible bases of the decoded game after its fixed positive payoff shift. -/
abbrev GeneralBimatrixShiftedBasis (input : List Bool) :=
  BimatrixBasis
    (fun i : Fin (generalRowCount input) => fun j : Fin (generalColCount input) =>
      decodeGeneralPayoff false input i.val j.val + ((2 : ℤ) ^ generalCoefficientBits input + 1))
    (fun i : Fin (generalRowCount input) => fun j : Fin (generalColCount input) =>
      decodeGeneralPayoff true input i.val j.val + ((2 : ℤ) ^ generalCoefficientBits input + 1))

/-- Encode the certificate of this basis, undoing the fixed payoff shifts. -/
def generalBimatrixEndpointWord (input : List Bool) (basis : GeneralBimatrixShiftedBasis input) :
    List Bool :=
  encodeGeneralCertificate (generalCertificateWidth input.length)
    (basis.cramerCertificate ((2 : ℤ) ^ generalCoefficientBits input + 1)
      ((2 : ℤ) ^ generalCoefficientBits input + 1))

/-- Every non-source complementary endpoint emits an accepted answer for the
same decoded game, without selecting a different equilibrium. -/
theorem generalBimatrixEndpointWord_accept (input : List Bool)
    (hi : GeneralInstanceValid input) (basis : GeneralBimatrixShiftedBasis input)
    (hc : ComplementaryLabels.IsComplementary basis.nonbasic)
    (hs : basis ≠ bimatrixSourceBasis
      (fun i j => decodeGeneralPayoff false input i.val j.val +
        ((2 : ℤ) ^ generalCoefficientBits input + 1))
      (fun i j => decodeGeneralPayoff true input i.val j.val +
        ((2 : ℤ) ^ generalCoefficientBits input + 1))) :
    generalBimatrixRelation input (generalBimatrixEndpointWord input basis) := by
  obtain ⟨hvalid, hwidth⟩ := shiftedCramerCertificate_valid_fitsWidth
    (fun i j => decodeGeneralPayoff false input i.val j.val)
    (fun i j => decodeGeneralPayoff true input i.val j.val)
    (generalCoefficientBits input)
    (fun i j => (decodeGeneralPayoff_natAbs_lt false input i.val j.val).le)
    (fun i j => (decodeGeneralPayoff_natAbs_lt true input i.val j.val).le)
    basis hc hs
  have hpow := Nat.pow_le_pow_right (by decide : 0 < 2)
    (bimatrixCertificateWidth_le_general input)
  obtain ⟨hdp, hdq, hp, hq, hu, hv⟩ := hwidth
  have hw : (basis.cramerCertificate ((2 : ℤ) ^ generalCoefficientBits input + 1)
      ((2 : ℤ) ^ generalCoefficientBits input + 1)).FitsWidth
      (generalCertificateWidth input.length) :=
    ⟨hdp.trans_le hpow, hdq.trans_le hpow, fun i => (hp i).trans_le hpow,
      fun j => (hq j).trans_le hpow, hu.trans_le hpow, hv.trans_le hpow⟩
  refine Or.inl ⟨hi, encodeGeneralCertificate_length _ _, ?_⟩
  change (decodeGeneralCertificate _ _ _ (encodeGeneralCertificate _ _)).Valid _ _
  rwa [decodeGeneralCertificate_encode _ hw]

end GameTheory.Complexity.Backend
