module

public import GameTheoryComplexity.Backend.BimatrixCoordinateColor
public import GameTheoryComplexity.Backend.BrouwerNashReduction
public import GameTheoryComplexity.Backend.BrouwerNashSelectorCorrectness

@[expose] public section

/-! An actual polynomial-time reduction from canonical Brouwer search to rectangular Nash search. -/
namespace GameTheory.Complexity.Backend.BrouwerNashHardness
open Turing.MultiTapeTM Cslib.Complexity Cslib.Circuits Cslib.BitString
open BrouwerNashLayout BrouwerNashProgram

/-- Every accepted Nash answer yields a Brouwer answer through a certified polynomial machine. -/
theorem exists_brouwerToBimatrixReduction :
    SearchReducible encBits encBits brouwerRelation generalBimatrixRelation := by
  obtain ⟨codes, hcodes, hcompiled⟩ := BimatrixCoordinateColor.exists_compiled_gridColorCircuits
  have compiled_wf (flag : Fin 2) (source : List Bool) (raw : List (CircuitFormat.signature.Op × List ℕ))
      (hd : CircuitFormat.decode? (codes flag source) = some raw) :
      Program.IsCodeFrom CircuitFormat.signature (arity (CircuitWords.first source).length) 0 raw := by
    obtain ⟨compiled, _, hdecode, hw, _, _, _⟩ := hcompiled flag source
    have he : compiled = raw := Option.some.inj (hdecode.symm.trans hd)
    subst compiled
    exact hw
  apply BrouwerNashReduction.exists_reduction_of_selectors codes
    (BrouwerNashSelector.coefficientQuery codes) (BrouwerNashSelector.kindQuery codes)
    hcodes hcompiled (BrouwerNashSelector.coefficientQuery_polyTime codes hcodes)
      (BrouwerNashSelector.kindQuery_polyTime codes hcodes)
  · intro source raw₀ raw₁ hd₀ hd₁ i r
    have hc₀ := CircuitFormat.encode_of_decode hd₀
    have hc₁ := CircuitFormat.encode_of_decode hd₁
    have hw₀ := compiled_wf 0 source raw₀ hd₀
    have hw₁ := compiled_wf 1 source raw₁ hd₁
    let d := BrouwerNashHeaders.sourceFn BrouwerNashHeaders.dimensionRuler codes source
    have hd := BrouwerNashHeaders.sourceDimension_length_of_decode
      codes source raw₀ raw₁ hd₀ hd₁
    have hi : (d.drop (d.length - i.val)).length = i.val := by
      rw [List.length_drop, hd]
      have hil := i.isLt
      omega
    have hr : ((d ++ d).drop (d.length * 2 - r.val)).length = r.val := by
      rw [List.length_drop, List.length_append, hd]
      have hrl := r.isLt
      omega
    simpa only [BrouwerNashSelector.coefficientQuery] using
      (BrouwerNashSelectorCorrectness.coefficientWord_value
      (d.drop (d.length - i.val)) ((d ++ d).drop (d.length * 2 - r.val)) source
      (codes 0 source) (codes 1 source) raw₀ raw₁ hc₀ hc₁ hw₀ hw₁ i hi r hr)
  · intro source raw₀ raw₁ hd₀ hd₁ i
    have hp₀ := circuitUnaryPrefix_length_of_decode _ _ hd₀
    have hp₁ := circuitUnaryPrefix_length_of_decode _ _ hd₁
    have hw₀ := compiled_wf 0 source raw₀ hd₀
    have hw₁ := compiled_wf 1 source raw₁ hd₁
    let d := BrouwerNashHeaders.sourceFn BrouwerNashHeaders.dimensionRuler codes source
    have hd := BrouwerNashHeaders.sourceDimension_length_of_decode
      codes source raw₀ raw₁ hd₀ hd₁
    have hi : (d.drop (d.length - i.val)).length = i.val := by
      rw [List.length_drop, hd]
      have hil := i.isLt
      omega
    simpa only [BrouwerNashSelector.kindQuery] using
      (BrouwerNashSelectorKind.kindWord_value (d.drop (d.length - i.val)) source
      (codes 0 source) (codes 1 source) raw₀ raw₁ hp₀ hp₁ hw₀ hw₁ i hi)

end GameTheory.Complexity.Backend.BrouwerNashHardness
