module

public import GameTheoryComplexity.Backend.CircuitVectorEmission
public import GameTheoryComplexity.Backend.SpernerProblem

@[expose] public section

/-! Two-bit color computations are compiled by the native uniform circuit
vector emitter. Extra output coordinates are padding; the color decoder reads only
the first two bits. The ruler retains the square grid's coordinate width. -/

namespace GameTheory.Complexity.Backend

open Turing.MultiTapeTM ComputableInPolyTime Cslib.BitString

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

private theorem paddedColor_polyTime {color : List Bool → List Bool → List Bool}
    (hc : ComputableInPolyTime (fun p : List Bool × List Bool => color p.1 p.2)
      (encPair encBits encBits) encBits) :
    ComputableInPolyTime (fun p : List Bool × List Bool => paddedColor color p.1 p.2)
      (encPair encBits encBits) encBits := by
  have hw := length_bits.comp (snd encBits encBits)
  exact bitsTakeWithInput (bitsAppend hc ((bitsReplicate false).comp hw)) hw

private theorem paddedColor_take_two (color : List Bool → List Bool → List Bool)
    (hc : ∀ input vertex, (color input vertex).length = 2)
    (input vertex : List Bool) (hv : 2 ≤ vertex.length) :
    (paddedColor color input vertex).take 2 = color input vertex := by
  simp only [paddedColor, List.take_take, Nat.min_eq_left hv]
  rw [← hc input vertex, List.take_left]

/-- A native two-bit color machine yields one uniform serialized color-circuit instance. -/
theorem exists_spernerCircuitInstance (ruler : List Bool → List Bool)
    (color : List Bool → List Bool → List Bool)
    (hr : ComputableInPolyTime ruler encBits encBits)
    (hc : ComputableInPolyTime (fun p : List Bool × List Bool => color p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ input vertex, (color input vertex).length = 2) :
    ∃ f : List Bool → List Bool, ComputableInPolyTime f encBits encBits ∧ ∀ input,
      CircuitWords.first (f input) = ruler input ∧ ∀ vertex,
        vertex.length = 2 * ((ruler input).length + 1) →
          (evaluateCircuitVector (CircuitWords.rest (f input)) vertex).take 2 = color input vertex := by
  let n := fun input => 2 * ((ruler input).length + 1)
  have hn : ComputableInPolyTime n encBits encUnary := by
    have hwidth := bitsAppend (bitsAppend hr (const [false])) (bitsAppend hr (const [false]))
    simpa only [n, Function.comp_def, List.length_append, List.length_singleton, two_mul] using
      length_bits.comp hwidth
  obtain ⟨codes, hcodes, heval⟩ := exists_circuitVector hn (paddedColor_polyTime hc)
    (fun input vertex hv => (paddedColor_length color input vertex).trans hv)
  let f := fun input => CircuitWords.encodePair (ruler input) (codes input)
  refine ⟨f, CircuitWords.encodePair_polyTime.comp (hr.prod hcodes), fun input => ?_⟩
  refine ⟨by simp only [f, CircuitWords.first_encodePair], fun vertex hv => ?_⟩
  simp only [f, CircuitWords.rest_encodePair]
  rw [heval input vertex hv]
  exact paddedColor_take_two color hlen input vertex (by omega)

/-- The emitted instance's interior coloring is precisely the supplied color
computation on the two extended fixed-width coordinate fields. -/
theorem exists_spernerColorInstance (ruler : List Bool → List Bool)
    (color : List Bool → List Bool → List Bool)
    (hr : ComputableInPolyTime ruler encBits encBits)
    (hc : ComputableInPolyTime (fun p : List Bool × List Bool => color p.1 p.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ input vertex, (color input vertex).length = 2) :
    ∃ f : List Bool → List Bool, ComputableInPolyTime f encBits encBits ∧ ∀ input,
      CircuitWords.first (f input) = ruler input ∧ ∀ x y,
        gridInteriorColor (ruler input).length (evaluateCircuitVector (CircuitWords.rest (f input)))
            x y =
          decodeGridColor (color input (lowBits ((ruler input).length + 1) x ++
            lowBits ((ruler input).length + 1) y)) := by
  obtain ⟨f, hf, h⟩ := exists_spernerCircuitInstance ruler color hr hc hlen
  refine ⟨f, hf, fun input => ⟨(h input).1, fun x y => ?_⟩⟩
  have he := (h input).2
    (lowBits ((ruler input).length + 1) x ++
      lowBits ((ruler input).length + 1) y) (by simp; omega)
  unfold gridInteriorColor
  rw [← decodeGridColor_take_two, he]

end GameTheory.Complexity.Backend
