module

public import GameTheoryComplexity.Backend.CircuitCompiler
public import Complexity.Computability.Complexity.Problems.CircuitValue.Compilation

@[expose] public section

/-! Uniform polynomial-time families of serialized scalar circuits.
The native circuit constructor supplies one shared program and an ordered output
wire list. Mapping the tagged serializer over that list preserves construction
cost and handles every input width, including empty inputs. Positive-width raw
families also provide checked gate tuples and their exact final output wires.
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

private theorem rawCompilation_correct {width outputs : ℕ} (hwidth : 0 < width)
    (c : Circuit Boolean.signature width outputs) (j : Fin outputs) :
    ∃ gates : List (CircuitFormat.signature.Op × List ℕ),
      ∃ output : Fin (width + gates.length),
        CircuitFormat.decode?
          (CircuitCompiler.serializeCode width c.code.1 (c.outputs j).toNat) = some gates ∧
        Program.IsCodeFrom CircuitFormat.signature width 0 gates ∧ gates ≠ [] ∧
        output.val = width + gates.length - 1 ∧
        ∀ values : Fin width → Bool,
          CircuitFormat.evalOutput (List.ofFn values) gates output.val =
            c.eval Boolean.interpretation values j := by
  have hdecoded : (Program.ofCode width c.program.code).isSome := by simp
  have hsource := Program.isSome_ofCode_iff.mp hdecoded
  have houtput : (c.outputs j).toNat < width + c.code.1.length := by
    change (c.outputs j).toNat < width + c.program.code.length
    rw [Program.length_code]
    exact Wire.toNat_lt (c.outputs j)
  let gates := CircuitCompiler.compileCode width c.code.1 (c.outputs j).toNat
  have hvalid : Program.IsCodeFrom CircuitFormat.signature width 0 gates :=
    CircuitCompiler.compileCode_valid hwidth _ _ hsource houtput
  have harity : ∀ gate ∈ gates, gate.2.length = 2 := by
    intro gate hg
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
    exact (hvalid.getElem i hi).1
  have hnonempty : gates ≠ [] := by simp [gates, CircuitCompiler.compileCode]
  have hlength : gates.length = c.code.1.length + 1 := by
    simp [gates, CircuitCompiler.compileCode, CircuitCompiler.translateProgram]
  let output : Fin (width + gates.length) := ⟨width + gates.length - 1, by omega⟩
  refine ⟨gates, output, CircuitFormat.decode?_encode gates harity, hvalid, hnonempty, rfl, ?_⟩
  intro values
  rw [Circuit.eval_eq_getD c Boolean.interpretation false values j]
  change (evalCode CircuitFormat.interpretation false (List.ofFn values) gates).getD
    (width + gates.length - 1) false =
      (evalCode Boolean.interpretation false (List.ofFn values) c.code.1).getD
        (c.outputs j).toNat false
  rw [show evalCode CircuitFormat.interpretation false (List.ofFn values) gates =
      evalCode Boolean.interpretation false (List.ofFn values) c.code.1 ++
        [(evalCode Boolean.interpretation false (List.ofFn values) c.code.1).getD
          (c.outputs j).toNat false] from
    CircuitCompiler.compileCode_trace c.code.1 (c.outputs j).toNat hsource houtput _]
  have htraceLength :
      (evalCode Boolean.interpretation false (List.ofFn values) c.code.1).length =
        width + c.code.1.length := by simp
  have hindex : width + gates.length - 1 =
      (evalCode Boolean.interpretation false (List.ofFn values) c.code.1).length := by omega
  rw [hindex, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]

/-- Positive-width native word families have uniformly serialized raw circuits.
The official topology certificate covers every gate's arity and references; the
selected final output is bounded in its native wire type. -/
theorem exists_uniformRawCircuitCodes {α : Type} {enc : α ↪ List Bool}
    {n m : α → ℕ} {F : α × List Bool → List Bool}
    (hn : ComputableInPolyTime n enc encUnary)
    (hm : ComputableInPolyTime m enc encUnary)
    (hF : ComputableInPolyTime F (encPair enc encBits) encBits)
    (hpos : ∀ a, 0 < n a) :
    ∃ codes : α → List (List Bool),
      ComputableInPolyTime codes enc (encList encBits) ∧
      (∀ a, (codes a).length = m a) ∧
      ∀ a (j : Fin (m a)),
        ∃ gates : List (CircuitFormat.signature.Op × List ℕ),
          ∃ output : Fin (n a + gates.length),
            CircuitFormat.decode? (((codes a)[j.val]?).getD []) = some gates ∧
            Program.IsCodeFrom CircuitFormat.signature (n a) 0 gates ∧ gates ≠ [] ∧
            output.val = n a + gates.length - 1 ∧
            ∀ values : Fin (n a) → Bool,
              CircuitFormat.evalOutput (List.ofFn values) gates output.val =
                (F (a, List.ofFn values)).getD j.val false := by
  obtain ⟨circuits, hcode, hsem⟩ :=
    Cslib.Complexity.CircuitValue.exists_uniformCircuitFamily hn hm hF
  let codes (a : α) : List (List Bool) :=
    (circuits a).code.2.map fun wire =>
      CircuitCompiler.serializeCode (n a) (circuits a).code.1 wire
  have hgates : ComputableInPolyTime (fun a => (circuits a).code.1)
      enc (encList Boolean.encGate) := hcode.fst'
  have houtputs : ComputableInPolyTime (fun a => (circuits a).code.2)
      enc (encList encNat) := hcode.snd'
  have hstep : ComputableInPolyTime
      (fun p : α × ℕ =>
        CircuitCompiler.serializeCode (n p.1) (circuits p.1).code.1 p.2)
      (encPair enc encNat) encBits :=
    CircuitCompiler.serializeCode_polyTime
      (hn.comp (ComputableInPolyTime.fst enc encNat))
      (hgates.comp (ComputableInPolyTime.fst enc encNat))
      (ComputableInPolyTime.snd enc encNat)
  have hcodes : ComputableInPolyTime codes enc (encList encBits) :=
    ComputableInPolyTime.mapWithInput
      (f := fun (a : α) (wire : ℕ) =>
        CircuitCompiler.serializeCode (n a) (circuits a).code.1 wire)
      houtputs hstep
  refine ⟨codes, hcodes, ?_, ?_⟩
  · intro a
    simp [codes, Circuit.code]
  · intro a j
    have hout : ((codes a)[j.val]?).getD [] =
        CircuitCompiler.serializeCode (n a) (circuits a).code.1
          ((circuits a).outputs j).toNat := by
      simp only [codes, Circuit.code, List.getElem?_map, List.getElem?_ofFn, Fin.is_lt,
        ↓reduceDIte, Option.map_some, Option.getD_some]
    obtain ⟨gates, output, hdecode, hvalid, hnonempty, hlast, heval⟩ :=
      rawCompilation_correct (hpos a) (circuits a) j
    refine ⟨gates, output, ?_, hvalid, hnonempty, hlast, ?_⟩
    · rw [hout]
      exact hdecode
    · intro values
      rw [heval values, hsem a values j]

end GameTheory.Complexity.Backend.NativeCircuitFamilies
