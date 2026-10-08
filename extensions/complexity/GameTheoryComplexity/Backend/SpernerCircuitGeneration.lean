import GameTheoryComplexity.Backend.PointerCircuitGeneration
import GameTheoryComplexity.Backend.SpernerProblem
import Complexitylib.Classes.P.Cobham.Internal.Extract

/-! Two-bit color computations are compiled by the common uniform pointer
compiler. Extra output coordinates are padding; the color decoder reads only
the first two bits. The ruler retains the square grid's coordinate width. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham

/-- Only the first two bits affect the decoded grid color. -/
theorem decodeGridColor_take_two (word : List Bool) :
    decodeGridColor (word.take 2) = decodeGridColor word := by
  cases word with
  | nil => rfl
  | cons first rest => cases rest <;> rfl

private def paddedColor (color : List Bool → List Bool → List Bool)
    (input vertex : List Bool) : List Bool :=
  (color input vertex ++ List.replicate vertex.length false).take vertex.length

private theorem paddedColor_length (color : List Bool → List Bool → List Bool)
    (input vertex : List Bool) : (paddedColor color input vertex).length = vertex.length := by
  simp [paddedColor]

private theorem paddedColor_pair_mem_FP {color : List Bool → List Bool → List Bool}
    (hc : (fun z => color (pairFst z) (pairSnd z)) ∈ FP) :
    (fun z => paddedColor color (pairFst z) (pairSnd z)) ∈ FP := by
  have hz : (fun z => List.replicate (pairSnd z).length false) ∈ FP := by
    simpa only [List.length_singleton, Nat.one_mul] using
      mulLenFn_mem_FP (constFn_mem_FP [false]) pairSnd_mem_FP
  apply CobhamFP_subset_FP
  exact takeFn (FP_subset_CobhamFP pairSnd_mem_FP)
    (FP_subset_CobhamFP (appendFn_mem_FP hc hz))

private theorem paddedColor_take_two (color : List Bool → List Bool → List Bool)
    (hc : ∀ input vertex, (color input vertex).length = 2)
    (input vertex : List Bool) (hv : 2 ≤ vertex.length) :
    (paddedColor color input vertex).take 2 = color input vertex := by
  simp only [paddedColor, List.take_take, Nat.min_eq_left hv]
  rw [← hc input vertex, List.take_left]

/-- A uniform two-bit color evaluator has an actual polynomial-time serialized
Sperner circuit generator, with exact color bits on extended coordinate words. -/
theorem exists_spernerCircuitInstance (ruler : List Bool → List Bool)
    (color : List Bool → List Bool → List Bool) (hr : ruler ∈ FP)
    (hc : (fun z => color (pairFst z) (pairSnd z)) ∈ FP)
    (hlen : ∀ input vertex, (color input vertex).length = 2) :
    ∃ f : List Bool → List Bool, f ∈ FP ∧ ∀ input,
      pairFst (f input) = ruler input ∧ ∀ vertex,
        vertex.length = 2 * ((ruler input).length + 1) →
          (evaluateCircuitVector (pairSnd (f input)) vertex).take 2 = color input vertex := by
  let coordinateRuler := fun input => (ruler input ++ [false]) ++ (ruler input ++ [false])
  have hcoord : coordinateRuler ∈ FP :=
    appendFn_mem_FP (appendFn_mem_FP hr (constFn_mem_FP [false]))
      (appendFn_mem_FP hr (constFn_mem_FP [false]))
  obtain ⟨g, hg, heval⟩ := exists_pointerCircuitInstance coordinateRuler
    (paddedColor color) (paddedColor color) hcoord (paddedColor_pair_mem_FP hc)
    (paddedColor_pair_mem_FP hc) (paddedColor_length color) (paddedColor_length color)
  let f := fun input => pair (ruler input) (pairFst (pairSnd (g input)))
  have hf : f ∈ FP := pairFn_mem_FP hr
    (mem_FP_comp (mem_FP_comp hg pairSnd_mem_FP) pairFst_mem_FP)
  refine ⟨f, hf, fun input => ⟨by simp [f], fun vertex hv => ?_⟩⟩
  have hwidth : (coordinateRuler input).length = 2 * ((ruler input).length + 1) := by
    simp [coordinateRuler]; omega
  have hn : 0 < (coordinateRuler input).length := by rw [hwidth]; omega
  have h := ((heval input hn).2 vertex (hv.trans hwidth.symm)).1
  change evaluateCircuitVector (pairFst (pairSnd (g input))) vertex =
    paddedColor color input vertex at h
  simp only [f, pairSnd_pair]
  rw [h]
  exact paddedColor_take_two color hlen input vertex (by omega)

/-- The emitted instance's interior coloring is precisely the supplied color
computation on the two extended fixed-width coordinate fields. -/
theorem exists_spernerColorInstance (ruler : List Bool → List Bool)
    (color : List Bool → List Bool → List Bool) (hr : ruler ∈ FP)
    (hc : (fun z => color (pairFst z) (pairSnd z)) ∈ FP)
    (hlen : ∀ input vertex, (color input vertex).length = 2) :
    ∃ f : List Bool → List Bool, f ∈ FP ∧ ∀ input,
      pairFst (f input) = ruler input ∧ ∀ x y,
        gridInteriorColor (ruler input).length (evaluateCircuitVector (pairSnd (f input)))
            x y =
          decodeGridColor (color input (Nat.toBitsLE ((ruler input).length + 1) x ++
            Nat.toBitsLE ((ruler input).length + 1) y)) := by
  obtain ⟨f, hf, h⟩ := exists_spernerCircuitInstance ruler color hr hc hlen
  refine ⟨f, hf, fun input => ⟨(h input).1, fun x y => ?_⟩⟩
  have he := (h input).2
    (Nat.toBitsLE ((ruler input).length + 1) x ++
      Nat.toBitsLE ((ruler input).length + 1) y) (by simp; omega)
  unfold gridInteriorColor
  rw [← decodeGridColor_take_two, he]

end GameTheory.Complexity.Backend
