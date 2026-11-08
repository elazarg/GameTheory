module

public import GameTheoryComplexity.Backend.CircuitVectorMachine
public import GameTheoryComplexity.Backend.NativeCircuitFamilies

@[expose] public section

/-! Polynomial-time emission of serialized circuit vectors from native scalar
code producers. Coordinates appear in ascending order and retain the producer's
exact codes. Uniform native circuit families realize word endomorphisms on their
prescribed finite input cubes.
-/

namespace GameTheory.Complexity.Backend

open Turing.MultiTapeTM

/-- Emit one scalar circuit code per coordinate, querying its index in unary. -/
def emitCircuitVector {α : Type} (g : α → ℕ → List Bool) (input : α) (width : ℕ) :
    List Bool :=
  encodeVectorCodes ((List.range width).map (g input))

/-- Jointly efficient scalar producers emit vectors from efficient input and width producers. -/
@[fun_prop] theorem emitCircuitVector_polyTime {α Input : Type}
    {enc : α ↪ List Bool} {inputEncoding : Input ↪ List Bool}
    {g : α → ℕ → List Bool} {input : Input → α} {width : Input → ℕ}
    (hg : ComputableInPolyTime (fun p : α × ℕ => g p.1 p.2)
      (encPair enc encUnary) encBits)
    (hinput : ComputableInPolyTime input inputEncoding enc)
    (hwidth : ComputableInPolyTime width inputEncoding encUnary) :
    ComputableInPolyTime (fun a => emitCircuitVector g (input a) (width a))
      inputEncoding encBits := by
  have hstep : ComputableInPolyTime (fun p : Input × ℕ => g (input p.1) p.2)
      (encPair inputEncoding encUnary) encBits :=
    hg.comp ((hinput.comp (ComputableInPolyTime.fst inputEncoding encUnary)).prod
      (ComputableInPolyTime.snd inputEncoding encUnary))
  have hcodes := ComputableInPolyTime.mapWithInput
    (f := fun (a : Input) (i : ℕ) => g (input a) i)
    (ComputableInPolyTime.range.comp hwidth) hstep
  exact encodeVectorCodes_polyTime.comp hcodes

/-- Each coordinate recovers the scalar producer's exact serialized code. -/
theorem emitCircuitVector_codeAt {α : Type} (g : α → ℕ → List Bool) (input : α)
    (width i : ℕ) (hi : i < width) :
    circuitVectorCodeAt (emitCircuitVector g input width) i = g input i := by
  simp [emitCircuitVector, circuitVectorCodeAt_encode, hi]

/-- Evaluating the emitted vector agrees coordinatewise with the tagged scalar codes. -/
theorem evaluateCircuitVector_emit {α : Type} (g : α → ℕ → List Bool) (input : α)
    (vertex : List Bool) :
    evaluateCircuitVector (emitCircuitVector g input vertex.length) vertex =
      (List.range vertex.length).map fun i =>
        (CircuitFormat.evalTagged? (g input i) vertex).getD false := by
  unfold evaluateCircuitVector
  apply List.map_congr_left
  intro i hi
  rw [emitCircuitVector_codeAt g input vertex.length i (List.mem_range.mp hi)]

/-- A uniformly polynomial-time word endomorphism has a uniformly emitted
serialized circuit vector agreeing with it on its prescribed input cube. -/
theorem exists_circuitVector {α : Type} {enc : α ↪ List Bool}
    {n : α → ℕ} {F : α × List Bool → List Bool}
    (hn : ComputableInPolyTime n enc encUnary)
    (hF : ComputableInPolyTime F (encPair enc encBits) encBits)
    (hlen : ∀ a u, u.length = n a → (F (a, u)).length = n a) :
    ∃ vector : α → List Bool,
      ComputableInPolyTime vector enc encBits ∧
      ∀ a u, u.length = n a → evaluateCircuitVector (vector a) u = F (a, u) := by
  obtain ⟨codes, hcodes, hcount, hsem⟩ :=
    NativeCircuitFamilies.exists_uniformCircuitCodes hn hn hF
  refine ⟨fun a => encodeVectorCodes (codes a), encodeVectorCodes_polyTime.comp hcodes, ?_⟩
  intro a u hu
  have hview : List.ofFn (fun j : Fin (n a) => u.getD j.val false) = u := by
    apply List.ext_getElem (by simp only [List.length_ofFn, hu])
    intro i _ hi
    simp only [List.getElem_ofFn]
    exact List.getD_eq_getElem u false hi
  rw [evaluateCircuitVector_encode]
  apply List.ext_getElem (by simp only [List.length_map, List.length_range, hlen a u hu, hu])
  intro i hi htarget
  have hin : i < n a := by
    simpa only [List.length_map, List.length_range, hu] using hi
  have hcode : i < (codes a).length := by rw [hcount a]; exact hin
  have hbit := hsem a (fun j : Fin (n a) => u.getD j.val false) ⟨i, hin⟩
  rw [hview] at hbit
  simp only [List.getElem_map, List.getElem_range]
  simp only [getElem?_pos (codes a) i hcode, Option.getD_some] at hbit ⊢
  rw [hbit, Option.getD_some, List.getD_eq_getElem _ _ htarget]

end GameTheory.Complexity.Backend
