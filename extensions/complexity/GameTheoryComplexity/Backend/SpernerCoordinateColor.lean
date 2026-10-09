import GameTheoryComplexity.Backend.SpernerProblem
import GameTheoryComplexity.Backend.UniformCircuitSpecialization

/-! Direct coordinate queries reuse the canonical boundary-corrected coloring.
Coordinates occupy two extended little-endian fields, without triangle tags. Each color flag
has a polynomial-time circuit generator with the serialized source hardwired. -/

namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham EndOfLineMachineOps
open _root_.Complexity.CircuitCode

/-- Query the canonical source coloring on two extended little-endian coordinate fields. -/
def gridCoordinateColor (input vertex : List Bool) : List Bool :=
  let ruler := pairFst input
  boundaryColorBits ruler (evaluateCircuitVector (pairSnd input))
    (vertex.take (ruler.length + 1)) (vertex.drop (ruler.length + 1))

/-- Canonical coordinate encodings recover the source grid coloring, including boundaries. -/
theorem gridCoordinateColor_encode (input : List Bool) (x y : ℕ)
    (hx : x ≤ 2 ^ (pairFst input).length) (hy : y ≤ 2 ^ (pairFst input).length) :
    gridCoordinateColor input
      (Nat.toBitsLE ((pairFst input).length + 1) x ++
        Nat.toBitsLE ((pairFst input).length + 1) y) =
      encodeGridColor (spernerColor input x y) := by
  have ht : (Nat.toBitsLE ((pairFst input).length + 1) x ++
      Nat.toBitsLE ((pairFst input).length + 1) y).take ((pairFst input).length + 1) =
      Nat.toBitsLE ((pairFst input).length + 1) x := by
    exact List.take_left' (by simp)
  have hd : (Nat.toBitsLE ((pairFst input).length + 1) x ++
      Nat.toBitsLE ((pairFst input).length + 1) y).drop ((pairFst input).length + 1) =
      Nat.toBitsLE ((pairFst input).length + 1) y := by
    exact List.drop_left' (by simp)
  dsimp only [gridCoordinateColor]
  rw [ht, hd]
  exact boundaryColorBits_encode _ _ x y hx hy

/-- Direct coordinate queries compose polynomial-time source and coordinate producers. -/
theorem gridCoordinateColorFn_mem_FP {input vertex : List Bool → List Bool}
    (hi : input ∈ FP) (hv : vertex ∈ FP) :
    (fun z => gridCoordinateColor (input z) (vertex z)) ∈ FP := by
  have hr := mem_FP_comp hi pairFst_mem_FP
  have hs := mem_FP_comp hi pairSnd_mem_FP
  have hw := appendFn_mem_FP hr (constFn_mem_FP [false])
  have hx : (fun z => (vertex z).take ((pairFst (input z)).length + 1)) ∈ FP := by
    apply CobhamFP_subset_FP
    exact (takeFn (FP_subset_CobhamFP hw) (FP_subset_CobhamFP hv)).of_eq fun z => by
      simp
  have hy : (fun z => (vertex z).drop ((pairFst (input z)).length + 1)) ∈ FP := by
    apply CobhamFP_subset_FP
    exact (dropFn (FP_subset_CobhamFP hw) (FP_subset_CobhamFP hv)).of_eq fun z => by
      simp
  have hq := mem_FP_comp (pairFn_mem_FP hs (appendFn_mem_FP hx hy))
    evaluateCircuitVector_pair_mem_FP
  apply boundaryColorBitsFn_mem_FP hr hx hy (fun z => evaluateCircuitVector (pairSnd (input z)))
  simpa only [Function.comp_def, pairFst_pair, pairSnd_pair] using hq

/-- Paired direct coordinate queries have an actual polynomial-time certificate. -/
theorem gridCoordinateColor_pair_mem_FP :
    (fun z => gridCoordinateColor (pairFst z) (pairSnd z)) ∈ FP :=
  gridCoordinateColorFn_mem_FP pairFst_mem_FP pairSnd_mem_FP

/-- Read one of the two canonical color flags from a paired source and coordinate word. -/
def gridCoordinateColorBit (i : Fin 2) (z : List Bool) : Bool :=
  bitOf (gridCoordinateColor (pairFst z) (pairSnd z)) i.val

/-- Each canonical color flag has an actual polynomial-time certificate. -/
theorem gridCoordinateColorBit_mem_FP (i : Fin 2) :
    (fun z => [gridCoordinateColorBit i z]) ∈ FP := by
  have h := Cobham.comp₂ Cobham.bitAtFn
    (FP_subset_CobhamFP (constFn_mem_FP (List.replicate i.val true)))
    (FP_subset_CobhamFP gridCoordinateColor_pair_mem_FP)
  apply CobhamFP_subset_FP
  exact h.of_eq fun z => by simp [bitAt_eq, gridCoordinateColorBit]

private theorem select_color (flag x y : List Bool)
    (hx : ∃ c, x = encodeGridColor c) (hy : ∃ c, y = encodeGridColor c) :
    ∃ c, caseBit₀ flag x y = encodeGridColor c := by
  cases flag with
  | nil => exact hy
  | cons b flag => cases b <;> assumption

/-- Every query result is a canonical color, including malformed sources and coordinates. -/
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

/-- Two polynomial-time generators hardwire the source and retain extended coordinate inputs. -/
theorem exists_gridCoordinateColorCircuitGenerators :
    ∃ codes : Fin 2 → List Bool → List Bool,
      (∀ i, codes i ∈ FP) ∧ ∀ i input vertex,
        vertex.length = 2 * ((pairFst input).length + 1) →
          evalFamilyCode (codes i input) vertex =
            some (bitOf (gridCoordinateColor input vertex) i) := by
  classical
  choose gen hgen heval using fun i : Fin 2 =>
    exists_prefixCircuitGenerator (gridCoordinateColorBit i) (gridCoordinateColorBit_mem_FP i)
  let ruler := fun input : List Bool =>
    (pairFst input ++ [false]) ++ (pairFst input ++ [false])
  have hr : ruler ∈ FP := appendFn_mem_FP
    (appendFn_mem_FP pairFst_mem_FP (constFn_mem_FP [false]))
    (appendFn_mem_FP pairFst_mem_FP (constFn_mem_FP [false]))
  let codes := fun i input => gen i (pair (ruler input) (pair input []))
  refine ⟨codes, fun i => ?_, ?_⟩
  · have hid : (fun z : List Bool => z) ∈ FP := CobhamFP_subset_FP (Cobham.proj 0)
    exact mem_FP_comp (pairFn_mem_FP hr (pairFn_mem_FP hid (constFn_mem_FP []))) (hgen i)
  · intro i input vertex hv
    have hlen : (ruler input).length = 2 * ((pairFst input).length + 1) := by
      simp [ruler]
      omega
    have hp : 0 < (ruler input).length := by rw [hlen]; omega
    have h := heval i (ruler input) (pair input []) vertex hp (hv.trans hlen.symm)
    have happ : pair input [] ++ vertex = pair input vertex := by simp [pair]
    rw [happ] at h
    simpa only [gridCoordinateColorBit, pairFst_pair, pairSnd_pair] using h

/-- Removing the family tag yields canonical raw circuits ready for paired gate programs. -/
theorem exists_gridCoordinateColorRawCircuitGenerators :
    ∃ codes : Fin 2 → List Bool → List Bool,
      (∀ i, codes i ∈ FP) ∧ ∀ i input,
        ∃ raw : RawCircuit, RawCircuit.decode? (codes i input) = some raw ∧
          raw.WellFormed (2 * ((pairFst input).length + 1)) ∧
          ∀ vertex, vertex.length = 2 * ((pairFst input).length + 1) →
            raw.eval? vertex = some (bitOf (gridCoordinateColor input vertex) i) := by
  obtain ⟨gen, hgen, heval⟩ := exists_gridCoordinateColorCircuitGenerators
  let codes := fun i input => (gen i input).tail
  refine ⟨codes, fun i => ?_, ?_⟩
  · apply CobhamFP_subset_FP
    exact Cobham.tailFn (FP_subset_CobhamFP (hgen i))
  · intro i input
    let n := 2 * ((pairFst input).length + 1)
    have hn : 0 < n := by dsimp [n]; omega
    have he := heval i input (List.replicate n false) (List.length_replicate ..)
    have ht : List.replicate n false ≠ [] := by
      exact List.length_pos_iff.mp (by simpa using hn)
    have hsome : (evalFamilyCode (gen i input) (List.replicate n false)).isSome := by
      rw [he]
      rfl
    obtain ⟨raw, hcode, hwell⟩ :=
      (evalFamilyCode_isSome_iff_of_ne_nil _ _ ht).mp hsome
    have hdecode : RawCircuit.decode? raw.encode = some raw :=
      (RawCircuit.decode?_eq_some_iff _ _).mpr rfl
    refine ⟨raw, ?_, ?_, ?_⟩
    · change RawCircuit.decode? (gen i input).tail = some raw
      rw [hcode]
      exact hdecode
    · simpa only [List.length_replicate] using hwell
    · intro vertex hv
      have hvne : vertex ≠ [] := List.length_pos_iff.mp (by rw [hv]; exact hn)
      have hh := heval i input vertex hv
      rw [hcode] at hh
      simpa [evalFamilyCode, hvne, evalCode, hdecode] using hh

end GameTheory.Complexity.Backend
