import GameTheoryComplexity.Backend.GeneralBimatrixCertificateCodec
import GameTheory.Finite.BimatrixCertificateCompleteness
import Complexitylib.Classes.NP.Witness

/-! Binary Nash search for independent signed rectangular payoff matrices.
Malformed instances have exactly the empty answer. Honest answers decode to
the library's ordinary mixed Nash equilibria. -/
namespace GameTheory.Complexity.Backend
open _root_.Complexity

/-- Exact binary certificate validity, with an explicit malformed-input fallback. -/
def generalBimatrixRelation (input certificate : List Bool) : Prop :=
  (GeneralInstanceValid input ∧
    certificate.length = (6 + generalRowCount input + generalColCount input) *
      generalCertificateWidth input.length ∧
    (decodeGeneralCertificate (generalRowCount input) (generalColCount input)
      (generalCertificateWidth input.length) certificate).Valid
      (fun i j => decodeGeneralPayoff false input i.val j.val)
      (fun i j => decodeGeneralPayoff true input i.val j.val)) ∨
  (¬GeneralInstanceValid input ∧ certificate = [])

/-- The exact output length is bounded by a cubic polynomial of input length. -/
theorem generalBimatrixRelation_polyBalanced : PolyBalanced generalBimatrixRelation := by
  refine ⟨(2 * Polynomial.X + 6) *
    ((2 * Polynomial.X + 2) * (8 * Polynomial.X + 6) + 1), ?_⟩
  intro input certificate hc
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_ofNat,
    Polynomial.eval_X, Polynomial.eval_one]
  rcases hc with ⟨_, hl, _⟩ | ⟨_, rfl⟩
  · rw [hl]
    apply Nat.mul_le_mul_right
    have hm := generalRowRuler_length_le input
    have hn := generalColRuler_length_le input
    change 6 + (generalRowRuler input).length + (generalColRuler input).length ≤ _
    omega
  · simp

/-- The serialized field width covers the mathematical certificate bound. -/
theorem bimatrixCertificateWidth_le_general (input : List Bool) :
    GameTheory.bimatrixCertificateWidth (generalRowCount input) (generalColCount input)
      (generalCoefficientBits input) ≤ generalCertificateWidth input.length := by
  have hm := generalRowRuler_length_le input
  have hn := generalColRuler_length_le input
  have hh := generalBitsRuler_length_le input
  unfold GameTheory.bimatrixCertificateWidth generalCertificateWidth
  apply Nat.add_le_add_right
  apply Nat.mul_le_mul
  · unfold generalRowCount generalColCount; omega
  · unfold generalRowCount generalColCount generalCoefficientBits; omega

/-- Real Nash existence implies an exactly serialized bounded answer.
This theorem uses a supplied equilibrium and imports no analytic existence theorem. -/
theorem generalBimatrixRelation_exists_of_nash (input : List Bool)
    (hi : GeneralInstanceValid input)
    (p : PMF (Fin (generalRowCount input))) (q : PMF (Fin (generalColCount input)))
    (hnash : GameTheory.IsNash
      (GameTheory.MatrixGame.form (Fin (generalRowCount input))
        (Fin (generalColCount input))).mixed
      (GameTheory.euPreference (GameTheory.MatrixGame.bimatrixUtility
        (fun i j => (decodeGeneralPayoff false input i.val j.val : ℝ))
        (fun i j => (decodeGeneralPayoff true input i.val j.val : ℝ))))
      (GameTheory.MatrixGame.mixedProfile p q)) :
    ∃ certificate, generalBimatrixRelation input certificate := by
  obtain ⟨c, hc, hwidth⟩ := GameTheory.exists_bounded_bimatrixCertificate
    (fun i j => decodeGeneralPayoff false input i.val j.val)
    (fun i j => decodeGeneralPayoff true input i.val j.val)
    (generalCoefficientBits input)
    (fun i j => (decodeGeneralPayoff_natAbs_lt false input i.val j.val).le)
    (fun i j => (decodeGeneralPayoff_natAbs_lt true input i.val j.val).le) p q hnash
  have hpow := Nat.pow_le_pow_right (by decide : 0 < 2)
    (bimatrixCertificateWidth_le_general input)
  obtain ⟨hdp, hdq, hp, hq, hu, hv⟩ := hwidth
  have hw : c.FitsWidth (generalCertificateWidth input.length) :=
    ⟨hdp.trans_le hpow, hdq.trans_le hpow, fun i => (hp i).trans_le hpow,
      fun j => (hq j).trans_le hpow, hu.trans_le hpow, hv.trans_le hpow⟩
  refine ⟨encodeGeneralCertificate (generalCertificateWidth input.length) c,
    Or.inl ⟨hi, encodeGeneralCertificate_length _ c, ?_⟩⟩
  rwa [decodeGeneralCertificate_encode c hw]

/-- On valid instances, accepted answers are exactly witnesses of canonical
mixed Nash existence for both decoded payoff matrices. -/
theorem generalBimatrixRelation_exists_iff_nash (input : List Bool)
    (hi : GeneralInstanceValid input) :
    (∃ certificate, generalBimatrixRelation input certificate) ↔
    ∃ (p : PMF (Fin (generalRowCount input))) (q : PMF (Fin (generalColCount input))),
      GameTheory.IsNash
        (GameTheory.MatrixGame.form (Fin (generalRowCount input))
          (Fin (generalColCount input))).mixed
        (GameTheory.euPreference (GameTheory.MatrixGame.bimatrixUtility
          (fun i j => (decodeGeneralPayoff false input i.val j.val : ℝ))
          (fun i j => (decodeGeneralPayoff true input i.val j.val : ℝ))))
        (GameTheory.MatrixGame.mixedProfile p q) := by
  constructor
  · rintro ⟨certificate, hc⟩
    rcases hc with ⟨_, _, hc⟩ | ⟨hn, _⟩
    · exact GameTheory.Finite.BimatrixCertificate.hasNash_of_valid _ _ _ hc
    · exact (hn hi).elim
  · rintro ⟨p, q, hnash⟩
    exact generalBimatrixRelation_exists_of_nash input hi p q hnash

/-- Malformed instances admit precisely the empty answer. -/
theorem generalBimatrixRelation_invalid_iff (input certificate : List Bool)
    (hi : ¬GeneralInstanceValid input) :
    generalBimatrixRelation input certificate ↔ certificate = [] := by
  simp [generalBimatrixRelation, hi]

end GameTheory.Complexity.Backend
