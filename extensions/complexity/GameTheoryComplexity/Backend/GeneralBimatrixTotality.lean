import GameTheoryComplexity.Backend.GeneralBimatrixFNP
import GameTheory.Finite.BimatrixPathCertificate

/-! Total serialized bimatrix Nash search. A finite complementary path supplies
bounded certificates on valid inputs; malformed words retain the empty answer. -/
namespace GameTheory.Complexity.Backend
open _root_.Complexity

/-- Every binary input has an accepted answer, using finite complementary paths
for honest nonempty games and the designated fallback otherwise. -/
theorem generalBimatrixRelation_total (input : List Bool) :
    ∃ certificate, generalBimatrixRelation input certificate := by
  by_cases hi : GeneralInstanceValid input
  · obtain ⟨c, hc, hwidth⟩ := GameTheory.Finite.exists_bounded_bimatrixCertificate_via_path
      (fun i j => decodeGeneralPayoff false input i.val j.val)
      (fun i j => decodeGeneralPayoff true input i.val j.val)
      (generalCoefficientBits input) hi.1 hi.2.1
      (fun i j => (decodeGeneralPayoff_natAbs_lt false input i.val j.val).le)
      (fun i j => (decodeGeneralPayoff_natAbs_lt true input i.val j.val).le)
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2)
      (bimatrixCertificateWidth_le_general input)
    obtain ⟨hdp, hdq, hp, hq, hu, hv⟩ := hwidth
    have hw : c.FitsWidth (generalCertificateWidth input.length) :=
      ⟨hdp.trans_le hpow, hdq.trans_le hpow, fun i => (hp i).trans_le hpow,
        fun j => (hq j).trans_le hpow, hu.trans_le hpow, hv.trans_le hpow⟩
    refine ⟨encodeGeneralCertificate (generalCertificateWidth input.length) c,
      Or.inl ⟨hi, encodeGeneralCertificate_length _ c, ?_⟩⟩
    rwa [decodeGeneralCertificate_encode c hw]
  · exact ⟨[], Or.inr ⟨hi, rfl⟩⟩

/-- Polynomial verification, polynomial balance, and path-based totality give
membership in the upstream total search class. -/
theorem generalBimatrixRelation_mem_TFNP : generalBimatrixRelation ∈ TFNP :=
  ⟨generalBimatrixRelation_mem_FNP, generalBimatrixRelation_total⟩

end GameTheory.Complexity.Backend
