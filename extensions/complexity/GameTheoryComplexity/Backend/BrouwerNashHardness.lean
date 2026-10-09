import GameTheoryComplexity.Backend.BimatrixCoordinateColor
import GameTheoryComplexity.Backend.BrouwerNashReduction
import GameTheoryComplexity.Backend.BrouwerNashSelectorCorrectness

/-! An actual polynomial-time reduction from canonical Brouwer search to rectangular Nash search. -/
namespace GameTheory.Complexity.Backend.BrouwerNashHardness
open _root_.Complexity _root_.Complexity.CircuitCode
open BrouwerNashLayout BrouwerNashProgram

private theorem decoded_prefix_length (code : List Bool) (raw : RawCircuit)
    (hd : RawCircuit.decode? code = some raw) :
    (circuitUnaryPrefix code).length = raw.length := by
  rw [(RawCircuit.decode?_eq_some_iff code raw).mp hd, RawCircuit.encode,
    circuitUnaryPrefix_encode, List.length_replicate]

/-- Every accepted Nash answer yields a Brouwer answer through a certified polynomial machine. -/
theorem exists_brouwerToBimatrixReduction :
    Nonempty (SearchReduction brouwerRelation generalBimatrixRelation) := by
  obtain ⟨codes, hFP, hcompiled⟩ := BimatrixCoordinateColor.exists_compiled_gridColorCircuits
  apply BrouwerNashReduction.exists_reduction_of_selectors codes
    (BrouwerNashSelector.coefficientQuery codes) (BrouwerNashSelector.kindQuery codes)
    hFP hcompiled (BrouwerNashSelector.coefficientQuery_mem_FPn codes hFP)
      (BrouwerNashSelector.kindQuery_mem_FPn codes hFP)
  · intro source raw₀ raw₁ hd₀ hd₁ i r
    have hc₀ := (RawCircuit.decode?_eq_some_iff (codes 0 source) raw₀).mp hd₀
    have hc₁ := (RawCircuit.decode?_eq_some_iff (codes 1 source) raw₁).mp hd₁
    obtain ⟨compiled₀, hdecode₀, hw₀, _⟩ := hcompiled 0 source
    obtain ⟨compiled₁, hdecode₁, hw₁, _⟩ := hcompiled 1 source
    have he₀ : compiled₀ = raw₀ := Option.some.inj (hdecode₀.symm.trans hd₀)
    have he₁ : compiled₁ = raw₁ := Option.some.inj (hdecode₁.symm.trans hd₁)
    subst compiled₀ compiled₁
    let d := BrouwerNashHeaders.sourceFn BrouwerNashHeaders.dimensionRuler codes source
    have hd : d.length = dimension (pairFst source).length raw₀.length raw₁.length := by
      have h := BrouwerNashHeaders.dimensionRuler_length
        ![source, codes 0 source, codes 1 source]
      change d.length = dimension (pairFst source).length
        (circuitUnaryPrefix (codes 0 source)).length
        (circuitUnaryPrefix (codes 1 source)).length at h
      rwa [decoded_prefix_length _ _ hd₀, decoded_prefix_length _ _ hd₁] at h
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
    have hp₀ := decoded_prefix_length _ _ hd₀
    have hp₁ := decoded_prefix_length _ _ hd₁
    obtain ⟨compiled₀, hdecode₀, hw₀, _⟩ := hcompiled 0 source
    obtain ⟨compiled₁, hdecode₁, hw₁, _⟩ := hcompiled 1 source
    have he₀ : compiled₀ = raw₀ := Option.some.inj (hdecode₀.symm.trans hd₀)
    have he₁ : compiled₁ = raw₁ := Option.some.inj (hdecode₁.symm.trans hd₁)
    subst compiled₀ compiled₁
    let d := BrouwerNashHeaders.sourceFn BrouwerNashHeaders.dimensionRuler codes source
    have hd : d.length = dimension (pairFst source).length raw₀.length raw₁.length := by
      have h := BrouwerNashHeaders.dimensionRuler_length
        ![source, codes 0 source, codes 1 source]
      change d.length = dimension (pairFst source).length
        (circuitUnaryPrefix (codes 0 source)).length
        (circuitUnaryPrefix (codes 1 source)).length at h
      rwa [hp₀, hp₁] at h
    have hi : (d.drop (d.length - i.val)).length = i.val := by
      rw [List.length_drop, hd]
      have hil := i.isLt
      omega
    exact BrouwerNashSelectorKind.kindWord_value (d.drop (d.length - i.val)) [] source
      (codes 0 source) (codes 1 source) raw₀ raw₁ hp₀ hp₁ hw₀ hw₁ i hi

end GameTheory.Complexity.Backend.BrouwerNashHardness
