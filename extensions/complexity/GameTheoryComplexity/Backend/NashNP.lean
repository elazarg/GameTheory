module

public import GameTheoryComplexity.Backend.NashCertificateEncoding
public import GameTheoryComplexity.Backend.NashWitnessCompleteness
public import GameTheoryComplexity.Backend.BimatrixCertificateVerifier
public import GameTheoryComplexity.Backend.BimatrixCertificateVerifierCorrectness
public import Complexity.Computability.Complexity.Classes.TFNP

@[expose] public section

/-! Native polynomial verification of bounded rational Nash certificates against
canonical decoded table games. Typed machine arguments include the full input
and witness; the Boolean verdict is the actual fixed-format binary verifier. -/

namespace GameTheory.Complexity.Backend
open GameTheory.Math (constrainedNashCertificateWidth)

open Turing.MultiTapeTM Cslib.Complexity
open GameTheory.Finite GameTheory.Finite.BimatrixTable

/-- Exact-length binary witnesses checked against the actual total table decoder. -/
def nashCertificateRelation (input certificate : List Bool) : Prop :=
  certificate.length = (2 * decodeDimension input + 4) *
      (constrainedNashCertificateWidth input.length) ∧
    (decodeNashCertificate (decodeDimension input)
      (constrainedNashCertificateWidth input.length) certificate).Valid
      (fun i j => decodedPayoff input i j)

/-- Every accepted certificate is bounded by a cubic polynomial of input length. -/
theorem nashCertificateRelation_polyBalanced :
    ∃ p : Polynomial ℕ, ∀ input certificate, nashCertificateRelation input certificate →
      certificate.length ≤ p.eval input.length := by
  refine ⟨(2 * Polynomial.X + 4) * (14 * Polynomial.X ^ 2 + 36 * Polynomial.X + 23),
    fun input certificate h => ?_⟩
  rw [h.1]
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_ofNat,
    Polynomial.eval_X, Polynomial.eval_pow]
  unfold constrainedNashCertificateWidth
  exact Nat.mul_le_mul_right _ (by have hq := decodeDimension_le_length input; omega)

/-- The finite binary witness relation characterizes canonical constrained Nash
existence, rather than a separate certificate-defined equilibrium notion. -/
theorem unitPayoffLanguage_iff_exists_nashCertificate (input : List Bool) :
    input ∈ unitPayoffLanguage ↔ ∃ certificate, nashCertificateRelation input certificate := by
  constructor
  · intro h
    obtain ⟨c, hc, hDp, hDq, hU, hV, ha, hb⟩ :=
      exists_bounded_decoded_nashNumerators input h
    refine ⟨encodeNashCertificate (constrainedNashCertificateWidth input.length) c,
      encodeNashCertificate_length _ c, ?_⟩
    rwa [decodeNashCertificate_encode (constrainedNashCertificateWidth input.length)
      c hDp hDq hU hV ha hb]
  · rintro ⟨certificate, _, hc⟩
    exact NumeratorCertificate.hasNash_of_valid _ _ hc

/-- Boolean verification of the complete input and exact binary certificate. -/
def nashCertificateVerdict (input certificate : List Bool) : Bool :=
  (binaryCertificateVerifier ![input, certificate]).headD false

/-- Native argument framing and every bit of the verifier's computation are charged. -/
@[fun_prop] theorem nashCertificateVerdict_polyTime
    {α : Type} {enc : α ↪ List Bool} {input certificate : α → List Bool}
    (hi : ComputableInPolyTime input enc encBits)
    (hc : ComputableInPolyTime certificate enc encBits) :
    ComputableInPolyTime (fun a => nashCertificateVerdict (input a) (certificate a))
      enc encBool := by
  have hargs : ComputableInPolyTime (fun a => ![input a, certificate a]) enc (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact hi
    · exact hc
  have hhead : ComputableInPolyTime (fun word : List Bool => word.headD false)
      encBits encBool := .headD false
  exact hhead.comp (binaryCertificateVerifier_polyTime.comp hargs)

/-- The actual verifier agrees with the canonical finite witness relation. -/
theorem binaryCertificateVerifier_accept_iff_relation (input certificate : List Bool) :
    binaryCertificateVerifier ![input, certificate] = [true] ↔
      nashCertificateRelation input certificate := by
  simpa only [nashCertificateRelation, certificateWidthWord_length, Nat.add_comm] using
    binaryCertificateVerifier_eq_true_iff input certificate

/-- The native Boolean verdict decides exactly the canonical finite witness relation. -/
theorem nashCertificateVerdict_accept (input certificate : List Bool) :
    nashCertificateVerdict input certificate = true ↔ nashCertificateRelation input certificate := by
  rw [← binaryCertificateVerifier_accept_iff_relation]
  rcases binaryCertificateVerifier_flag ![input, certificate] with h | h <;>
    simp [nashCertificateVerdict, h]

/-- Canonical equilibrium certificates have native bounded search and verification evidence. -/
theorem nashCertificateRelation_mem_FNP : nashCertificateRelation ∈ FNP encBits := by
  refine ⟨nashCertificateRelation_polyBalanced, fun p => nashCertificateVerdict p.1 p.2,
    nashCertificateVerdict_polyTime (ComputableInPolyTime.fst encBits encBits)
      (ComputableInPolyTime.snd encBits encBits), fun input certificate => ?_⟩
  exact (nashCertificateVerdict_accept input certificate).symm

/-- Payoff-one mixed Nash existence in canonical explicit table games belongs to native NP. -/
theorem unitPayoffLanguage_mem_NP : unitPayoffLanguage ∈ NP encBits := by
  apply mem_NP_iff_exists_FNP.mpr
  refine ⟨nashCertificateRelation, nashCertificateRelation_mem_FNP, ?_⟩
  ext input
  exact (unitPayoffLanguage_iff_exists_nashCertificate input).symm

end GameTheory.Complexity.Backend
