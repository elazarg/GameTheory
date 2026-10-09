import GameTheoryComplexity.Backend.BimatrixCoordinateColor
import GameTheoryComplexity.Backend.BrouwerNashReduction
import GameTheoryComplexity.Backend.BrouwerNashSelectorCorrectness

/-! An actual polynomial-time reduction from canonical Brouwer search to rectangular Nash search. -/
namespace GameTheory.Complexity.Backend.BrouwerNashHardness
open _root_.Complexity _root_.Complexity.CircuitCode
open BrouwerNashLayout BrouwerNashProgram

/-- Every accepted Nash answer yields a Brouwer answer through a certified polynomial machine. -/
theorem exists_brouwerToBimatrixReduction :
    Nonempty (SearchReduction brouwerRelation generalBimatrixRelation) := by
  obtain ⟨codes, hFP, hcompiled⟩ := BimatrixCoordinateColor.exists_compiled_gridColorCircuits
  have compiled_wf (flag : Fin 2) (source : List Bool) (raw : RawCircuit)
      (hd : RawCircuit.decode? (codes flag source) = some raw) :
      raw.WellFormed (arity (pairFst source).length) := by
    obtain ⟨compiled, hdecode, hw, _⟩ := hcompiled flag source
    have he : compiled = raw := Option.some.inj (hdecode.symm.trans hd)
    subst compiled
    exact hw
  apply BrouwerNashReduction.exists_reduction_of_selectors codes
    (BrouwerNashSelector.coefficientQuery codes) (BrouwerNashSelector.kindQuery codes)
    hFP hcompiled (BrouwerNashSelector.coefficientQuery_mem_FPn codes hFP)
      (BrouwerNashSelector.kindQuery_mem_FPn codes hFP)
  · intro source raw₀ raw₁ hd₀ hd₁ i r
    have hc₀ := (RawCircuit.decode?_eq_some_iff (codes 0 source) raw₀).mp hd₀
    have hc₁ := (RawCircuit.decode?_eq_some_iff (codes 1 source) raw₁).mp hd₁
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
    exact BrouwerNashSelectorCorrectness.coefficientWord_value
      (d.drop (d.length - i.val)) ((d ++ d).drop (d.length * 2 - r.val)) source
      (codes 0 source) (codes 1 source) raw₀ raw₁ hc₀ hc₁ hw₀ hw₁ i hi r hr
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
    exact BrouwerNashSelectorKind.kindWord_value (d.drop (d.length - i.val)) [] source
      (codes 0 source) (codes 1 source) raw₀ raw₁ hp₀ hp₁ hw₀ hw₁ i hi

end GameTheory.Complexity.Backend.BrouwerNashHardness
