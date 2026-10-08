import GameTheoryComplexity.Backend.BinaryCertificateArithmetic
import Complexitylib.Classes.Containments.Internal.FPBridge
import Complexitylib.Classes.P.NormalForm
import Complexitylib.Classes.NP.WitnessConstruction

/-! Canonical binary pairing lifts a multi-input verifier to a word machine.
Re-encoding checks the serialization before the component verifier is consulted. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham

/-- Validate the pair encoding and run the two-input Boolean verifier. -/
def canonicalPairedVerifier (f : (Fin 2 → List Bool) → List Bool)
    (z : List Bool) : List Bool :=
  andBit (eqFlag z (pair (pairFst z) (pairSnd z))) (f ![pairFst z, pairSnd z])

/-- Pair validation preserves actual polynomial-time machine certificates. -/
theorem canonicalPairedVerifier_mem_FP
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

/-- Every paired verifier produces one Boolean flag. -/
theorem canonicalPairedVerifier_flag
    (f : (Fin 2 → List Bool) → List Bool) (z : List Bool) :
    canonicalPairedVerifier f z = [true] ∨ canonicalPairedVerifier f z = [false] :=
  andBit_flag _ _

/-- Acceptance requires a canonical pair and acceptance of its components. -/
theorem canonicalPairedVerifier_eq_true_iff
    (f : (Fin 2 → List Bool) → List Bool)
    (hflag : ∀ v, f v = [true] ∨ f v = [false]) (z : List Bool) :
    canonicalPairedVerifier f z = [true] ↔
      z = pair (pairFst z) (pairSnd z) ∧ f ![pairFst z, pairSnd z] = [true] := by
  rw [canonicalPairedVerifier, andBit_eq_true_iff (eqFlag_flag _ _) (hflag _),
    eqFlag_eq_true_iff]

end GameTheory.Complexity.Backend
