module

public import GameTheoryComplexity.Backend.CircuitCompiler
public import Complexity.Computability.Complexity.Problems.CircuitValue.Compilation

@[expose] public section

/-! Uniform polynomial-time families of serialized scalar circuits.
The native circuit constructor supplies one shared program and an ordered output
wire list. Mapping the tagged serializer over that list preserves construction
cost and handles every input width, including empty inputs.
-/

namespace GameTheory.Complexity.Backend.NativeCircuitFamilies

open Cslib.Circuits Turing.MultiTapeTM

private theorem serializedOutput_at {width outputs : ℕ}
    (c : Circuit Boolean.signature width outputs) (j : Fin outputs) :
    (((c.code.2.map fun wire =>
        CircuitCompiler.serializeTaggedCode width c.code.1 wire)[j.val]?).getD []) =
      CircuitCompiler.compile c j := by
  simp only [Circuit.code, List.getElem?_map, List.getElem?_ofFn, Fin.is_lt,
    ↓reduceDIte, Option.map_some, Option.getD_some, CircuitCompiler.compile]

/-- Every native polynomial-time word family has uniformly constructed scalar
circuit words for its prescribed output coordinates. Short results are padded
with false, matching the native circuit compiler's output semantics. -/
theorem exists_uniformCircuitCodes {α : Type} {enc : α ↪ List Bool}
    {n m : α → ℕ} {F : α × List Bool → List Bool}
    (hn : ComputableInPolyTime n enc encUnary)
    (hm : ComputableInPolyTime m enc encUnary)
    (hF : ComputableInPolyTime F (encPair enc encBits) encBits) :
    ∃ codes : α → List (List Bool),
      ComputableInPolyTime codes enc (encList encBits) ∧
      (∀ a, (codes a).length = m a) ∧
      ∀ a (x : Fin (n a) → Bool) (j : Fin (m a)),
        CircuitFormat.evalTagged? (((codes a)[j.val]?).getD []) (List.ofFn x) =
          some ((F (a, List.ofFn x)).getD j.val false) := by
  obtain ⟨circuits, hcode, hsem⟩ :=
    Cslib.Complexity.CircuitValue.exists_uniformCircuitFamily hn hm hF
  let codes (a : α) : List (List Bool) :=
    (circuits a).code.2.map fun wire =>
      CircuitCompiler.serializeTaggedCode (n a) (circuits a).code.1 wire
  have hgates : ComputableInPolyTime (fun a => (circuits a).code.1)
      enc (encList Boolean.encGate) := hcode.fst'
  have houtputs : ComputableInPolyTime (fun a => (circuits a).code.2)
      enc (encList encNat) := hcode.snd'
  have hstep : ComputableInPolyTime
      (fun p : α × ℕ =>
        CircuitCompiler.serializeTaggedCode (n p.1) (circuits p.1).code.1 p.2)
      (encPair enc encNat) encBits :=
    CircuitCompiler.serializeTaggedCode_polyTime
      (hn.comp (ComputableInPolyTime.fst enc encNat))
      (hgates.comp (ComputableInPolyTime.fst enc encNat))
      (ComputableInPolyTime.snd enc encNat)
  have hcodes : ComputableInPolyTime codes enc (encList encBits) :=
    ComputableInPolyTime.mapWithInput
      (f := fun (a : α) (wire : ℕ) =>
        CircuitCompiler.serializeTaggedCode (n a) (circuits a).code.1 wire)
      houtputs hstep
  refine ⟨codes, hcodes, ?_, ?_⟩
  · intro a
    simp [codes, Circuit.code]
  · intro a x j
    have hout : ((codes a)[j.val]?).getD [] = CircuitCompiler.compile (circuits a) j :=
      serializedOutput_at (circuits a) j
    rw [hout, CircuitCompiler.compile_eval, hsem a x j]

end GameTheory.Complexity.Backend.NativeCircuitFamilies
