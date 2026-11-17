module

public import GameTheoryComplexity.Backend.GeneralBimatrixCodec
public import GameTheoryComplexity.Backend.BimatrixCertificateVerifier

@[expose] public section

/-! Polynomial-time parsers for the three unary headers of a rectangular binary game. -/
namespace GameTheory.Complexity.Backend
open Cslib.BitString Turing.MultiTapeTM

private theorem codecInput_polyTime :
    ComputableInPolyTime (fun v : Fin 1 → List Bool => v 0)
      (encPi encBits) encBits := .pi_apply encBits (0 : Fin 1)

/-- The initial unary row header is polynomial-time. -/
@[fun_prop] theorem generalRowRuler_polyTime :
    ComputableInPolyTime (fun v : Fin 1 → List Bool => generalRowRuler (v 0))
      (encPi encBits) encBits := by
  have h := certificateDimensionWord_polyTime.comp codecInput_polyTime
  apply ComputableInPolyTime.of_tidy
  apply h.tidy.of_enc_eq
  intro v
  rfl

/-- Parsing the column header after the first delimiter is polynomial-time. -/
@[fun_prop] theorem generalColRuler_polyTime :
    ComputableInPolyTime (fun v : Fin 1 → List Bool => generalColRuler (v 0))
      (encPi encBits) encBits := by
  have hrow := generalRowRuler_polyTime
  have hrowLen := ComputableInPolyTime.length_bits_comp hrow
  have hdelimiter := ComputableInPolyTime.bitsAppend hrow (.const [false])
  have hoffset := ComputableInPolyTime.length_bits_comp hdelimiter
  have hdrop := ComputableInPolyTime.bitsDropWithInput codecInput_polyTime hoffset
  have h := certificateDimensionWord_polyTime.comp hdrop
  apply ComputableInPolyTime.of_tidy
  apply h.tidy.of_enc_eq
  intro v
  simp [generalColRuler, certificateDimensionWord, List.length_append]

/-- Parsing the coefficient-width header is polynomial-time. -/
@[fun_prop] theorem generalBitsRuler_polyTime :
    ComputableInPolyTime (fun v : Fin 1 → List Bool => generalBitsRuler (v 0))
      (encPi encBits) encBits := by
  have hrow := generalRowRuler_polyTime
  have hcol := generalColRuler_polyTime
  have hrowLen := ComputableInPolyTime.length_bits_comp hrow
  have hcolLen := ComputableInPolyTime.length_bits_comp hcol
  have hoffset := ComputableInPolyTime.unary_add'
    (ComputableInPolyTime.unary_add' hrowLen hcolLen) (.const 2)
  have hdrop := ComputableInPolyTime.bitsDropWithInput codecInput_polyTime hoffset
  have h := certificateDimensionWord_polyTime.comp hdrop
  apply ComputableInPolyTime.of_tidy
  apply h.tidy.of_enc_eq
  intro v
  rfl

/-- Removing the three headers and delimiters is polynomial-time. -/
@[fun_prop] theorem generalPayload_polyTime :
    ComputableInPolyTime (fun v : Fin 1 → List Bool => generalPayload (v 0))
      (encPi encBits) encBits := by
  have hrow := generalRowRuler_polyTime
  have hcol := generalColRuler_polyTime
  have hbits := generalBitsRuler_polyTime
  have hrowLen := ComputableInPolyTime.length_bits_comp hrow
  have hcolLen := ComputableInPolyTime.length_bits_comp hcol
  have hbitsLen := ComputableInPolyTime.length_bits_comp hbits
  have hoffset := ComputableInPolyTime.unary_add'
    (ComputableInPolyTime.unary_add' (ComputableInPolyTime.unary_add' hrowLen hcolLen)
      hbitsLen) (.const 3)
  exact ComputableInPolyTime.bitsDropWithInput codecInput_polyTime hoffset

end GameTheory.Complexity.Backend
