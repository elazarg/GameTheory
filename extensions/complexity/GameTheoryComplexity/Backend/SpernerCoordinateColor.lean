module

public import GameTheoryComplexity.Backend.SpernerProblem
public import GameTheoryComplexity.Backend.NativeCircuitFamilies

@[expose] public section

/-! Direct coordinate queries reuse the canonical boundary-corrected coloring.
Coordinates occupy two extended little-endian fields without triangle tags.
Native uniform raw circuits hardwire the source and retain checked gate tuples
with their bounded final output wires. -/

namespace GameTheory.Complexity.Backend

open Cslib.Circuits Cslib.BitString Turing.MultiTapeTM WordOperations

/-- Query the canonical source coloring on two extended coordinate fields. -/
def gridCoordinateColor (input vertex : List Bool) : List Bool :=
  let ruler := CircuitWords.first input
  boundaryColorBits ruler (evaluateCircuitVector (CircuitWords.rest input))
    (vertex.take (ruler.length + 1)) (vertex.drop (ruler.length + 1))

/-- Canonical coordinate words recover the source grid coloring, including boundaries. -/
theorem gridCoordinateColor_encode (input : List Bool) (x y : ℕ)
    (hx : x ≤ 2 ^ (CircuitWords.first input).length)
    (hy : y ≤ 2 ^ (CircuitWords.first input).length) :
    gridCoordinateColor input
      (lowBits ((CircuitWords.first input).length + 1) x ++
        lowBits ((CircuitWords.first input).length + 1) y) =
      encodeGridColor (spernerColor input x y) := by
  have ht : (lowBits ((CircuitWords.first input).length + 1) x ++
      lowBits ((CircuitWords.first input).length + 1) y).take
        ((CircuitWords.first input).length + 1) =
      lowBits ((CircuitWords.first input).length + 1) x := by
    exact List.take_left' (by simp)
  have hd : (lowBits ((CircuitWords.first input).length + 1) x ++
      lowBits ((CircuitWords.first input).length + 1) y).drop
        ((CircuitWords.first input).length + 1) =
      lowBits ((CircuitWords.first input).length + 1) y := by
    exact List.drop_left' (by simp)
  dsimp only [gridCoordinateColor]
  rw [ht, hd]
  exact boundaryColorBits_encode _ _ x y hx hy

/-- Direct coordinate queries retain the actual encoding of both word producers. -/
@[fun_prop] theorem gridCoordinateColor_polyTime
    {Input : Type} {inputEncoding : Input ↪ List Bool} {input vertex : Input → List Bool}
    (hi : ComputableInPolyTime input inputEncoding encBits)
    (hv : ComputableInPolyTime vertex inputEncoding encBits) :
    ComputableInPolyTime (fun a => gridCoordinateColor (input a) (vertex a))
      inputEncoding encBits := by
  have hr := CircuitWords.first_polyTime.comp hi
  have hc := CircuitWords.rest_polyTime.comp hi
  have hw := ComputableInPolyTime.unary_succ.comp (ComputableInPolyTime.length_bits_comp hr)
  have hx := ComputableInPolyTime.bitsTakeWithInput hv hw
  have hy := ComputableInPolyTime.bitsDropWithInput hv hw
  exact boundaryColorBits_polyTime hr hx hy
    (fun a => evaluateCircuitVector (CircuitWords.rest (input a)))
    (evaluateCircuitVector_polyTime hc (ComputableInPolyTime.bitsAppend hx hy))

private theorem select_color (flag x y : List Bool)
    (hx : ∃ c, x = encodeGridColor c) (hy : ∃ c, y = encodeGridColor c) :
    ∃ c, select flag x y = encodeGridColor c := by
  cases flag with
  | nil => exact hy
  | cons b flag =>
    cases b
    · exact hy
    · exact hx

/-- Every query is a canonical color, including malformed sources and coordinates. -/
theorem gridCoordinateColor_canonical (input vertex : List Bool) :
    ∃ c, gridCoordinateColor input vertex = encodeGridColor c := by
  unfold gridCoordinateColor boundaryColorBits
  apply select_color
  · apply select_color <;> exact ⟨_, rfl⟩
  · apply select_color
    · exact ⟨_, rfl⟩
    · apply select_color <;> exact ⟨_, rfl⟩

/-- Every direct coordinate query returns exactly two color flags. -/
theorem gridCoordinateColor_length (input vertex : List Bool) :
    (gridCoordinateColor input vertex).length = 2 := by
  obtain ⟨c, hc⟩ := gridCoordinateColor_canonical input vertex
  rw [hc]
  rfl

/-- Two native generators hardwire the source into checked raw color circuits.
Each output wire is bounded and is the final copied gate of its program. -/
theorem exists_gridCoordinateColorCircuitCodes :
    ∃ codes : Fin 2 → List Bool → List Bool,
      (∀ i, ComputableInPolyTime (codes i) encBits encBits) ∧
      ∀ i input,
        ∃ gates : List (CircuitFormat.signature.Op × List ℕ),
          ∃ output : Fin (2 * ((CircuitWords.first input).length + 1) + gates.length),
            CircuitFormat.decode? (codes i input) = some gates ∧
            Program.IsCodeFrom CircuitFormat.signature
              (2 * ((CircuitWords.first input).length + 1)) 0 gates ∧ gates ≠ [] ∧
            output.val = 2 * ((CircuitWords.first input).length + 1) + gates.length - 1 ∧
            ∀ vertex, vertex.length = 2 * ((CircuitWords.first input).length + 1) →
              CircuitFormat.evalOutput vertex gates output.val =
                (gridCoordinateColor input vertex).getD i.val false := by
  let n := fun input : List Bool => 2 * ((CircuitWords.first input).length + 1)
  have hn : ComputableInPolyTime n encBits encUnary :=
    ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 2)
      (ComputableInPolyTime.unary_succ.comp
        (ComputableInPolyTime.length_bits_comp CircuitWords.first_polyTime))
  have hF : ComputableInPolyTime (fun p : List Bool × List Bool =>
      gridCoordinateColor p.1 p.2) (encPair encBits encBits) encBits :=
    gridCoordinateColor_polyTime (ComputableInPolyTime.fst encBits encBits)
      (ComputableInPolyTime.snd encBits encBits)
  have hpos : ∀ input, 0 < n input := by intro input; dsimp only [n]; omega
  obtain ⟨compiled, hcompiled, _, hraw⟩ :=
    NativeCircuitFamilies.exists_uniformRawCircuitCodes hn (ComputableInPolyTime.const 2) hF hpos
  let codes := fun (i : Fin 2) (input : List Bool) => (compiled input).getD i.val []
  have hcodes : ∀ i, ComputableInPolyTime (codes i) encBits encBits := by
    intro i
    exact ComputableInPolyTime.listGetDWithInput hcompiled (ComputableInPolyTime.const i.val) []
  refine ⟨codes, hcodes, ?_⟩
  intro i input
  obtain ⟨gates, output, hdecode, hvalid, hnonempty, hlast, heval⟩ := hraw input i
  refine ⟨gates, output, ?_, hvalid, hnonempty, hlast, ?_⟩
  · simpa only [codes, List.getD_eq_getElem?_getD] using hdecode
  · intro vertex hv
    have hview : List.ofFn
        (fun j : Fin (n input) => vertex.getD j.val false) = vertex := by
      apply List.ext_getElem (by simp only [List.length_ofFn, hv]; rfl)
      intro j _ hj
      simp only [List.getElem_ofFn]
      exact List.getD_eq_getElem vertex false hj
    have h := heval (fun j : Fin (n input) => vertex.getD j.val false)
    rw [hview] at h
    exact h

end GameTheory.Complexity.Backend
