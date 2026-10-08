import GameTheoryComplexity.Backend.GeneralBimatrixVerifier

/-! Polynomial-time machine certificates for the complete binary rectangular-game
verifier. Explicit action counts and binary field widths bound every loop. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham

theorem generalInstanceLengthRuler_cobham : Cobham fun v : Fin 1 → List Bool =>
    generalInstanceLengthRuler (v 0) :=
  Cobham.appendFn
    (Cobham.appendFn
      (Cobham.appendFn (Cobham.appendFn generalRowRuler_cobham generalColRuler_cobham)
        generalBitsRuler_cobham) (Cobham.const [true, true, true]))
    (Cobham.comp₂ Cobham.smash (Cobham.const (List.replicate 4 true))
      (Cobham.comp₂ Cobham.smash
        (Cobham.comp₂ Cobham.smash generalRowRuler_cobham generalColRuler_cobham)
        generalBitsRuler_cobham))

theorem generalInstanceFlag_cobham : Cobham fun v : Fin 1 → List Bool =>
    generalInstanceFlag (v 0) :=
  Cobham.andFn (Cobham.notFn (eqFlag_mem generalRowRuler_cobham Cobham.empty))
    (Cobham.andFn (Cobham.notFn (eqFlag_mem generalColRuler_cobham Cobham.empty))
    (Cobham.andFn (Cobham.notFn (eqFlag_mem generalBitsRuler_cobham Cobham.empty))
      (lenEqFlag_mem (.proj 0) generalInstanceLengthRuler_cobham)))

private theorem generalCertificateEqual_cobham : Cobham fun v : Fin 2 → List Bool =>
    certificateEqualWord (v 0) (v 1) :=
  Cobham.andFn binaryCertificateLE_cobham
    (Cobham.comp₂ binaryCertificateLE_cobham (.proj 1) (.proj 0))

theorem generalValidCertificateVerdict_cobham : Cobham generalValidCertificateVerdict := by
  have hm : Cobham fun v : Fin 2 → List Bool => generalRowRuler (v 0) :=
    Cobham.comp generalRowRuler_cobham fun _ => .proj 0
  have hn : Cobham fun v : Fin 2 → List Bool => generalColRuler (v 0) :=
    Cobham.comp generalColRuler_cobham fun _ => .proj 0
  have hw : Cobham fun v : Fin 2 → List Bool => generalWidthRuler (v 0) :=
    Cobham.comp generalWidthRuler_cobham fun _ => .proj 0
  have hf (i : ℕ) : Cobham fun v : Fin 2 → List Bool =>
      generalCertificateFieldWord ![List.replicate i true, v 0, v 1] :=
    Cobham.comp₃ generalCertificateFieldWord_cobham
      (Cobham.const (List.replicate i true)) (.proj 0) (.proj 1)
  exact Cobham.andFn
    (lenEqFlag_mem (.proj 1) (Cobham.comp₂ Cobham.smash
      (Cobham.appendFn (Cobham.appendFn hm hn) (Cobham.const (List.replicate 6 true))) hw))
    (Cobham.andFn (Cobham.notFn (Cobham.comp₂ generalCertificateEqual_cobham (hf 0) Cobham.empty))
    (Cobham.andFn (Cobham.notFn (Cobham.comp₂ generalCertificateEqual_cobham (hf 1) Cobham.empty))
    (Cobham.andFn (Cobham.comp₂ generalCertificateEqual_cobham (generalWeightSumWord_cobham false) (hf 0))
    (Cobham.andFn (Cobham.comp₂ generalCertificateEqual_cobham (generalWeightSumWord_cobham true) (hf 1))
    (Cobham.andFn (generalAllChecks_cobham false) (generalAllChecks_cobham true))))))

/-- The full relation checker has a genuine polynomial-time string-machine certificate. -/
theorem generalBimatrixVerdict_cobham : Cobham generalBimatrixVerdict := by
  have hi : Cobham fun v : Fin 2 → List Bool => generalInstanceFlag (v 0) :=
    Cobham.comp generalInstanceFlag_cobham fun _ => .proj 0
  exact Cobham.orFn (Cobham.andFn hi generalValidCertificateVerdict_cobham)
    (Cobham.andFn (Cobham.notFn hi) (eqFlag_mem (.proj 1) Cobham.empty))

/-- Polynomial-time membership concerns serialized binary input length. -/
theorem generalBimatrixVerdict_mem_FPn : FPn generalBimatrixVerdict :=
  cobham_iff_FPn.mp generalBimatrixVerdict_cobham

/-- The full checker always emits exactly a Boolean verdict. -/
theorem generalBimatrixVerdict_flag (v : Fin 2 → List Bool) :
    generalBimatrixVerdict v = [true] ∨ generalBimatrixVerdict v = [false] := by
  have h : (generalBimatrixVerdict v).length = 1 := orBit_length _ _
  rcases List.length_eq_one_iff.mp h with ⟨b, hb⟩
  cases b <;> simp [hb]

end GameTheory.Complexity.Backend
