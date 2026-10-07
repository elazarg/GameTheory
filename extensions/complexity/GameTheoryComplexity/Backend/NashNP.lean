import GameTheoryComplexity.Backend.BinaryCertificateFold
import GameTheoryComplexity.Backend.NashCertificateEncoding
import GameTheoryComplexity.Backend.NashWitnessCompleteness
import GameTheoryComplexity.Backend.BimatrixCertificateVerifier
import GameTheoryComplexity.Backend.BimatrixCertificateVerifierCorrectness
import Complexitylib.Classes.Containments.Internal.FPBridge
import Complexitylib.Classes.NP.WitnessConstruction
import Complexitylib.Classes.P.NormalForm

/-! Canonical paired inputs for the polynomial-time equilibrium certificate
verifier. Re-encoding rejects malformed pairs before consulting the verifier. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham
open GameTheory.Finite GameTheory.Finite.BimatrixTable

/-- Exact-length binary witnesses checked against the actual total table decoder. -/
def nashCertificateRelation (input certificate : List Bool) : Prop :=
  certificate.length = (2 * decodeDimension input + 4) *
      (14 * input.length ^ 2 + 36 * input.length + 23) ∧
    (decodeNashCertificate (decodeDimension input)
      (14 * input.length ^ 2 + 36 * input.length + 23) certificate).Valid
      (fun i j => decodedPayoff input i j)

/-- Every accepted certificate is bounded by a cubic polynomial of input length. -/
theorem nashCertificateRelation_polyBalanced : PolyBalanced nashCertificateRelation := by
  refine ⟨(2 * Polynomial.X + 4) * (14 * Polynomial.X ^ 2 + 36 * Polynomial.X + 23),
    fun input certificate h => ?_⟩
  rw [h.1]
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_ofNat,
    Polynomial.eval_X, Polynomial.eval_pow]
  exact Nat.mul_le_mul_right _ (by have hq := decodeDimension_le_length input; omega)

/-- The finite binary witness relation characterizes canonical constrained Nash
existence, rather than a separate certificate-defined equilibrium notion. -/
theorem unitPayoffLanguage_iff_exists_nashCertificate (input : List Bool) :
    input ∈ unitPayoffLanguage ↔ ∃ certificate, nashCertificateRelation input certificate := by
  constructor
  · intro h
    obtain ⟨c, hc, hDp, hDq, hU, hV, ha, hb⟩ :=
      exists_bounded_decoded_nashNumerators input h
    refine ⟨encodeNashCertificate (14 * input.length ^ 2 + 36 * input.length + 23) c,
      encodeNashCertificate_length _ c, ?_⟩
    rwa [decodeNashCertificate_encode _ c hDp hDq hU hV ha hb]
  · rintro ⟨certificate, _, hc⟩
    exact NumeratorCertificate.hasNash_of_valid _ _ hc

private def canonicalPairedVerifier (f : (Fin 2 → List Bool) → List Bool)
    (z : List Bool) : List Bool :=
  andBit (eqFlag z (pair (pairFst z) (pairSnd z))) (f ![pairFst z, pairSnd z])

private theorem canonicalPairedVerifier_mem_FP
    (f : (Fin 2 → List Bool) → List Bool) (hf : FPn f) :
    canonicalPairedVerifier f ∈ FP := by
  obtain ⟨g, hg, heq⟩ := hf
  have henc : (fun z => encodeVec ![pairFst z, pairSnd z]) ∈ FP := by
    exact pairFn_mem_FP (pairFn_mem_FP const_nil_mem_FP pairSnd_mem_FP) pairFst_mem_FP
  have hbody : (fun z => f ![pairFst z, pairSnd z]) ∈ FP := by
    have hh := mem_FP_comp henc hg
    simpa only [Function.comp_def, heq] using hh
  exact andBitFn_mem_FP
    (eqFlagFn_mem_FP id_mem_FP (pairFn_mem_FP pairFst_mem_FP pairSnd_mem_FP)) hbody

private theorem canonicalPairedVerifier_eq_true_iff
    (f : (Fin 2 → List Bool) → List Bool)
    (hflag : ∀ v, f v = [true] ∨ f v = [false]) (z : List Bool) :
    canonicalPairedVerifier f z = [true] ↔
      z = pair (pairFst z) (pairSnd z) ∧ f ![pairFst z, pairSnd z] = [true] := by
  rw [canonicalPairedVerifier, andBit_eq_true_iff (eqFlag_flag _ _) (hflag _),
    eqFlag_eq_true_iff]

/-- A deterministic paired-input verifier rejects malformed pair encodings and
then checks the exact binary equilibrium certificate. -/
def nashPairedVerdict : List Bool → List Bool :=
  canonicalPairedVerifier binaryCertificateVerifier

/-- The complete paired verifier, including pair validation, is polynomial time. -/
theorem nashPairedVerdict_mem_FP : nashPairedVerdict ∈ FP :=
  canonicalPairedVerifier_mem_FP _ binaryCertificateVerifier_mem_FPn

/-- One deterministic machine verifies every paired input with polynomial work. -/
theorem exists_nashPairedVerdict_machine :
    ∃ (k : ℕ) (machine : TM k) (bound : Polynomial ℕ),
      machine.ComputesInTime nashPairedVerdict bound.eval :=
  mem_FP_iff_computesInTime_polynomial.mp nashPairedVerdict_mem_FP

theorem nashPairedVerdict_flag (z : List Bool) :
    nashPairedVerdict z = [true] ∨ nashPairedVerdict z = [false] :=
  andBit_flag _ _

/-- The actual verifier agrees with the canonical finite witness relation. -/
theorem binaryCertificateVerifier_accept_iff_relation (input certificate : List Bool) :
    binaryCertificateVerifier ![input, certificate] = [true] ↔
      nashCertificateRelation input certificate := by
  simpa only [nashCertificateRelation, certificateWidthWord_length, Nat.add_comm] using
    binaryCertificateVerifier_eq_true_iff input certificate

/-- Pair validation and certificate verification decide the exact paired language. -/
theorem nashPairedVerdict_eq_true_iff_mem_pairLang (z : List Bool) :
    nashPairedVerdict z = [true] ↔ z ∈ pairLang nashCertificateRelation := by
  rw [nashPairedVerdict,
    canonicalPairedVerifier_eq_true_iff _ binaryCertificateVerifier_flag]
  constructor
  · rintro ⟨hz, hcert⟩
    exact ⟨pairFst z, pairSnd z, hz,
      (binaryCertificateVerifier_accept_iff_relation _ _).mp hcert⟩
  · rintro ⟨input, certificate, rfl, hcert⟩
    simp only [pairFst_pair, pairSnd_pair]
    exact ⟨trivial, (binaryCertificateVerifier_accept_iff_relation _ _).mpr hcert⟩

/-- The paired certificate language has an actual polynomial-time decider. -/
theorem nashCertificateRelation_pairLang_mem_P : pairLang nashCertificateRelation ∈ P := by
  apply mem_P_of_decisionFn nashPairedVerdict_mem_FP
  intro z
  rw [← nashPairedVerdict_eq_true_iff_mem_pairLang]
  rcases nashPairedVerdict_flag z with h | h <;> simp [h]

/-- Equilibrium certificates are polynomially balanced and polynomially verifiable. -/
theorem nashCertificateRelation_mem_FNP : nashCertificateRelation ∈ FNP :=
  ⟨nashCertificateRelation_polyBalanced, nashCertificateRelation_pairLang_mem_P⟩

/-- Canonical payoff-one mixed Nash existence for explicit symmetric integer
tables belongs to NP through a certified binary guess-and-verify machine. -/
theorem unitPayoffLanguage_mem_NP : unitPayoffLanguage ∈ NP :=
  NP.mem_NP_of_FNP nashCertificateRelation_mem_FNP
    unitPayoffLanguage_iff_exists_nashCertificate

end GameTheory.Complexity.Backend
