module

public import GameTheoryComplexity.Backend.CircuitFormat
public import Complexity.Computability.Circuit.Boolean.EvaluationTime
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
public import Mathlib.Data.List.GetD

@[expose] public section

/-! Compile native De Morgan circuits into the serialized two-input gate signature.
One source gate produces one target gate, preserving all existing wire numbers.
Raw references are capped before unary serialization.
-/

namespace GameTheory.Complexity.Backend.CircuitCompiler

open Cslib.Circuits Turing.MultiTapeTM

/-- Bound a raw wire number without allocating a unary representation. -/
def capRef (bound ref : ℕ) : ℕ := min ref bound

/-- Capping preserves every reference within the available wire budget. -/
theorem capRef_eq {bound ref : ℕ} (h : ref ≤ bound) : capRef bound ref = ref :=
  Nat.min_eq_left h

/-- Translate one native Boolean gate, reading missing raw arguments as wire zero. -/
def translateGate (bound : ℕ) (gate : Boolean.Op × List ℕ) :
    CircuitFormat.signature.Op × List ℕ :=
  match gate.1 with
  | .const b => ((!b, false, true), [0, 0])
  | .not => ((true, true, true),
      [capRef bound (gate.2.getD 0 0), capRef bound (gate.2.getD 0 0)])
  | .and => ((true, false, false),
      [capRef bound (gate.2.getD 0 0), capRef bound (gate.2.getD 1 0)])
  | .or => ((false, false, false),
      [capRef bound (gate.2.getD 0 0), capRef bound (gate.2.getD 1 0)])

/-- Every translated gate has the concrete binary arity, even on malformed input. -/
@[simp] theorem translateGate_arity (bound : ℕ) (gate : Boolean.Op × List ℕ) :
    (translateGate bound gate).2.length = 2 := by
  rcases gate with ⟨op, args⟩
  cases op <;> rfl

/-- On a valid source line, the translation reads only already available wires. -/
theorem translateGate_refs {width position : ℕ} (hwidth : 0 < width)
    (bound : ℕ) (gate : Boolean.Op × List ℕ)
    (h : gate.2.length = Boolean.signature.Arity gate.1 ∧
      ∀ ref ∈ gate.2, ref < width + position) :
    ∀ ref ∈ (translateGate bound gate).2, ref < width + position := by
  rcases gate with ⟨op, args⟩
  have hread (i : ℕ) (hi : i < args.length) :
      capRef bound (args.getD i 0) < width + position := by
    rw [List.getD_eq_getElem args 0 hi]
    exact (Nat.min_le_left _ _).trans_lt (h.2 _ (List.getElem_mem _))
  cases op with
  | const b =>
    have hz : 0 < width + position := by omega
    simpa [translateGate] using hz
  | not =>
    have h0 := hread 0 (by have := h.1; change args.length = 1 at this; omega)
    simpa [translateGate] using h0
  | and =>
    have h0 := hread 0 (by have := h.1; change args.length = 2 at this; omega)
    have h1 := hread 1 (by have := h.1; change args.length = 2 at this; omega)
    simpa [translateGate] using And.intro h0 h1
  | or =>
    have h0 := hread 0 (by have := h.1; change args.length = 2 at this; omega)
    have h1 := hread 1 (by have := h.1; change args.length = 2 at this; omega)
    simpa [translateGate] using And.intro h0 h1

/-- Translate a native program code with a shared bound on raw wire numbers. -/
def translateProgram (bound : ℕ) (gates : List (Boolean.Op × List ℕ)) :
    List (CircuitFormat.signature.Op × List ℕ) :=
  gates.map (translateGate bound)

/-- Gate translation preserves the arity and backward-reference invariant. -/
theorem translateProgram_valid {width position : ℕ} (hwidth : 0 < width)
    (bound : ℕ) (gates : List (Boolean.Op × List ℕ))
    (h : Program.IsCodeFrom Boolean.signature width position gates) :
    Program.IsCodeFrom CircuitFormat.signature width position
      (translateProgram bound gates) := by
  induction gates generalizing position with
  | nil => trivial
  | cons gate gates ih =>
    exact ⟨⟨translateGate_arity bound gate, translateGate_refs hwidth bound gate h.1⟩,
      ih h.2⟩

/-- The whole-program wire budget leaves valid native source references unchanged. -/
theorem capRef_eq_of_valid {width : ℕ} {gates : List (Boolean.Op × List ℕ)}
    (h : Program.IsCodeFrom Boolean.signature width 0 gates)
    {position ref : ℕ} (hposition : position < gates.length)
    (href : ref ∈ gates[position].2) :
    capRef (width + gates.length) ref = ref := by
  apply capRef_eq
  have hbound := (h.getElem position hposition).2 ref href
  omega

/-- Translating a well-formed gate preserves its value on every wire-value list. -/
theorem translateGate_eval (bound : ℕ) (gate : Boolean.Op × List ℕ)
    (harity : gate.2.length = Boolean.signature.Arity gate.1)
    (href : ∀ ref ∈ gate.2, ref ≤ bound) (values : List Bool) :
    evalCode CircuitFormat.interpretation false values [translateGate bound gate] =
      evalCode Boolean.interpretation false values [gate] := by
  rcases gate with ⟨op, args⟩
  cases op with
  | const b =>
    cases b <;> simp [evalCode, translateGate, CircuitFormat.interpretation,
      CircuitFormat.opValue, Boolean.interpretation]
  | not =>
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp harity
    have ha := capRef_eq (href a (by simp))
    simp [evalCode, translateGate, ha, CircuitFormat.interpretation,
      CircuitFormat.opValue, Boolean.interpretation]
  | and =>
    obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp harity
    have ha := capRef_eq (href a (by simp))
    have hb := capRef_eq (href b (by simp))
    simp [evalCode, translateGate, ha, hb, CircuitFormat.interpretation,
      CircuitFormat.opValue, Boolean.interpretation]
  | or =>
    obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp harity
    have ha := capRef_eq (href a (by simp))
    have hb := capRef_eq (href b (by simp))
    simp [evalCode, translateGate, ha, hb, CircuitFormat.interpretation,
      CircuitFormat.opValue, Boolean.interpretation]

/-- Translation preserves the complete native wire trace, including its input prefix. -/
theorem translateProgram_eval {width position bound : ℕ}
    (gates : List (Boolean.Op × List ℕ))
    (h : Program.IsCodeFrom Boolean.signature width position gates)
    (hbound : width + position + gates.length ≤ bound) (values : List Bool) :
    evalCode CircuitFormat.interpretation false values (translateProgram bound gates) =
      evalCode Boolean.interpretation false values gates := by
  induction gates generalizing position values with
  | nil => rfl
  | cons gate gates ih =>
    have href : ∀ ref ∈ gate.2, ref ≤ bound := by
      intro ref hr
      have := h.1.2 ref hr
      simp only [List.length_cons] at hbound
      omega
    change evalCode CircuitFormat.interpretation false
        (evalCode CircuitFormat.interpretation false values [translateGate bound gate])
        (translateProgram bound gates) =
      evalCode Boolean.interpretation false
        (evalCode Boolean.interpretation false values [gate]) gates
    rw [translateGate_eval bound gate h.1.1 href values]
    exact ih h.2 (by simp only [List.length_cons] at hbound; omega) _

/-- Compile a raw native program and copy its selected output into the final gate. -/
def compileCode (width : ℕ) (gates : List (Boolean.Op × List ℕ)) (output : ℕ) :
    List (CircuitFormat.signature.Op × List ℕ) :=
  let bound := width + gates.length
  translateProgram bound gates ++
    [((true, false, false), [capRef bound output, capRef bound output])]

/-- Serialize capped raw native code in the concrete scalar format. -/
def serializeCode (width : ℕ) (gates : List (Boolean.Op × List ℕ)) (output : ℕ) :
    List Bool :=
  CircuitFormat.encode (compileCode width gates output)

/-- Empty-input programs carry their answer explicitly; positive widths carry a scalar program. -/
def serializeTaggedCode (width : ℕ) (gates : List (Boolean.Op × List ℕ)) (output : ℕ) :
    List Bool :=
  if width = 0 then [false, Boolean.evalOutput [] gates output]
  else true :: serializeCode width gates output

/-- A positive-width valid native source with an existing output compiles to valid code. -/
theorem compileCode_valid {width : ℕ} (hwidth : 0 < width)
    (gates : List (Boolean.Op × List ℕ)) (output : ℕ)
    (h : Program.IsCodeFrom Boolean.signature width 0 gates)
    (houtput : output < width + gates.length) :
    Program.IsCodeFrom CircuitFormat.signature width 0 (compileCode width gates output) := by
  apply Program.isCodeFrom_append 0 _ _ |>.2
  refine ⟨translateProgram_valid hwidth _ gates h, ⟨⟨rfl, ?_⟩, trivial⟩⟩
  intro ref href
  have heq : ref = capRef (width + gates.length) output := by
    simpa using href
  subst ref
  simp only [translateProgram, List.length_map, Nat.zero_add]
  exact (Nat.min_le_left output (width + gates.length)).trans_lt houtput

/-- Compilation adds exactly the selected native output to the preserved wire trace. -/
theorem compileCode_trace {width : ℕ} (gates : List (Boolean.Op × List ℕ))
    (output : ℕ) (h : Program.IsCodeFrom Boolean.signature width 0 gates)
    (houtput : output < width + gates.length) (values : List Bool) :
    evalCode CircuitFormat.interpretation false values (compileCode width gates output) =
      evalCode Boolean.interpretation false values gates ++
        [(evalCode Boolean.interpretation false values gates).getD output false] := by
  rw [compileCode, evalCode_append_singleton,
    translateProgram_eval gates h (by omega) values]
  simp [CircuitFormat.interpretation, CircuitFormat.opValue, capRef_eq houtput.le]

/-- The strict concrete scalar decoder returns the selected native source value. -/
theorem compileCode_eval {width : ℕ} (hwidth : 0 < width)
    (gates : List (Boolean.Op × List ℕ)) (output : ℕ)
    (h : Program.IsCodeFrom Boolean.signature width 0 gates)
    (houtput : output < width + gates.length) (values : List Bool)
    (hvalues : values.length = width) :
    CircuitFormat.eval? width (CircuitFormat.encode (compileCode width gates output)) values =
      some ((evalCode Boolean.interpretation false values gates).getD output false) := by
  have hvalid := compileCode_valid hwidth gates output h houtput
  have harity : ∀ gate ∈ compileCode width gates output, gate.2.length = 2 := by
    intro gate hg
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
    exact (hvalid.getElem i hi).1
  have hdecode := CircuitFormat.decode?_encode (compileCode width gates output) harity
  have hcheck : codeCheck CircuitFormat.signature width (compileCode width gates output) = true :=
    codeCheck_eq_true_iff.mpr hvalid
  have hnonempty : compileCode width gates output ≠ [] := by
    simp [compileCode]
  have hlength : (compileCode width gates output).length = gates.length + 1 := by
    simp [compileCode, translateProgram]
  have heval : CircuitFormat.evalOutput values (compileCode width gates output)
      (width + (compileCode width gates output).length - 1) =
      (evalCode Boolean.interpretation false values gates).getD output false := by
    rw [CircuitFormat.evalOutput, compileCode_trace gates output h houtput values, hlength]
    have hlen : (evalCode Boolean.interpretation false values gates).length =
        width + gates.length := by simp only [length_evalCode, hvalues]
    have hindex : width + (gates.length + 1) - 1 =
        (evalCode Boolean.interpretation false values gates).length := by omega
    rw [hindex, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
  simp [CircuitFormat.eval?, hvalues, hdecode, hnonempty, hcheck, heval]

/-- Serialize one selected native circuit output in the concrete scalar format. -/
def compile {width outputs : ℕ} (c : Circuit Boolean.signature width outputs)
    (output : Fin outputs) : List Bool :=
  serializeTaggedCode width c.code.1 (c.outputs output).toNat

/-- Tagged serialized compilation agrees with typed native evaluation at every input width. -/
theorem compile_eval {width outputs : ℕ}
    (c : Circuit Boolean.signature width outputs) (output : Fin outputs)
    (values : Fin width → Bool) :
    CircuitFormat.evalTagged? (compile c output) (List.ofFn values) =
      some (c.eval Boolean.interpretation values output) := by
  cases width with
  | zero =>
    rw [Circuit.eval_eq_evalOutput c values output]
    simp [compile, serializeTaggedCode, CircuitFormat.evalTagged?]
  | succ width =>
    have hdecoded : (Program.ofCode (width + 1) c.program.code).isSome := by simp
    have hsource := Program.isSome_ofCode_iff.mp hdecoded
    have houtput : (c.outputs output).toNat < width + 1 + c.code.1.length := by
      change (c.outputs output).toNat < width + 1 + c.program.code.length
      rw [Program.length_code]
      exact Wire.toNat_lt (c.outputs output)
    have hinput : (List.ofFn values).isEmpty = false := by simp
    rw [Circuit.eval_eq_getD c Boolean.interpretation false values output]
    simpa only [compile, serializeTaggedCode, Nat.succ_ne_zero, ↓reduceIte,
      CircuitFormat.evalTagged?, hinput, Bool.false_eq_true, List.length_ofFn, serializeCode] using
      compileCode_eval (by omega) c.code.1 (c.outputs output).toNat hsource houtput
        (List.ofFn values) (by simp)

private theorem encodeUnary_polyTime {Input : Type} {input : Input ↪ List Bool}
    {value : Input → ℕ} (hvalue : ComputableInPolyTime value input encUnary) :
    ComputableInPolyTime (fun a => CircuitFormat.encodeUnary (value a)) input encBits :=
  ComputableInPolyTime.bitsAppend ((ComputableInPolyTime.bitsReplicate true).comp hvalue)
    (ComputableInPolyTime.const [false])

private theorem capRef_polyTime {Input : Type} {input : Input ↪ List Bool}
    {bound ref : Input → ℕ}
    (hbound : ComputableInPolyTime bound input encUnary)
    (href : ComputableInPolyTime ref input encNat) :
    ComputableInPolyTime (fun a => capRef (bound a) (ref a)) input encUnary := by
  have h := ComputableInPolyTime.binary_min_unary' hbound href
  convert h using 1
  funext a
  exact Nat.min_comm _ _

private theorem encodeGate_polyTime {Input : Type} {input : Input ↪ List Bool}
    {op : Input → CircuitFormat.signature.Op} {left right : Input → ℕ}
    (hop : ComputableInPolyTime op input CircuitFormat.encOp)
    (hleft : ComputableInPolyTime left input encUnary)
    (hright : ComputableInPolyTime right input encUnary) :
    ComputableInPolyTime (fun a => CircuitFormat.encodeGate (op a) (left a) (right a))
      input encBits := by
  have hflags : ComputableInPolyTime
      (fun a => [(op a).1, (op a).2.1, (op a).2.2]) input encBits :=
    (ComputableInPolyTime.of_finite (encIn := CircuitFormat.encOp) (encOut := encBits)
      (fun flags : CircuitFormat.signature.Op => [flags.1, flags.2.1, flags.2.2])).comp hop
  exact ComputableInPolyTime.bitsAppend
    (ComputableInPolyTime.bitsAppend hflags (encodeUnary_polyTime hleft))
    (encodeUnary_polyTime hright)

private theorem encodeTranslatedGate_polyTime :
    ComputableInPolyTime (fun p : ℕ × (Boolean.Op × List ℕ) =>
      let gate := translateGate p.1 p.2
      CircuitFormat.encodeGate gate.1 (gate.2.getD 0 0) (gate.2.getD 1 0))
      (encPair encUnary Boolean.encGate) encBits := by
  have hbound := ComputableInPolyTime.fst encUnary Boolean.encGate
  have hop := (ComputableInPolyTime.snd encUnary Boolean.encGate).fst'
  have hargs := (ComputableInPolyTime.snd encUnary Boolean.encGate).snd'
  have h0 := capRef_polyTime hbound
    (ComputableInPolyTime.listGetDWithInput hargs (ComputableInPolyTime.const 0) 0)
  have h1 := capRef_polyTime hbound
    (ComputableInPolyTime.listGetDWithInput hargs (ComputableInPolyTime.const 1) 0)
  have hflags : ComputableInPolyTime
      (fun p : ℕ × (Boolean.Op × List ℕ) => (translateGate 0 (p.2.1, [])).1)
      (encPair encUnary Boolean.encGate) CircuitFormat.encOp :=
    (ComputableInPolyTime.of_finite (encIn := Boolean.encOp) (encOut := CircuitFormat.encOp)
      (fun op : Boolean.Op => (translateGate 0 (op, [])).1)).comp hop
  have hconst : ComputableInPolyTime
      (fun p : ℕ × (Boolean.Op × List ℕ) => match p.2.1 with
        | .const _ => true | _ => false)
      (encPair encUnary Boolean.encGate) encBool :=
    (ComputableInPolyTime.of_finite (encIn := Boolean.encOp) (encOut := encBool)
      (fun op : Boolean.Op => match op with | .const _ => true | _ => false)).comp hop
  have hnot : ComputableInPolyTime
      (fun p : ℕ × (Boolean.Op × List ℕ) => decide (p.2.1 = .not))
      (encPair encUnary Boolean.encGate) encBool :=
    (ComputableInPolyTime.of_finite (encIn := Boolean.encOp) (encOut := encBool)
      (fun op : Boolean.Op => decide (op = .not))).comp hop
  have h := encodeGate_polyTime hflags
    (hconst.ite (ComputableInPolyTime.const 0) h0)
    (hconst.ite (ComputableInPolyTime.const 0) (hnot.ite h0 h1))
  convert h using 1
  funext p
  rcases p with ⟨bound, op, args⟩
  cases op <;> rfl

private theorem serializeCode_eq (width : ℕ) (gates : List (Boolean.Op × List ℕ))
    (output : ℕ) :
    serializeCode width gates output =
      (CircuitFormat.encodeUnary (gates.length + 1) ++
        gates.flatMap (fun gate =>
          let translated := translateGate (width + gates.length) gate
          CircuitFormat.encodeGate translated.1
            (translated.2.getD 0 0) (translated.2.getD 1 0))) ++
        CircuitFormat.encodeGate (true, false, false)
          (capRef (width + gates.length) output) (capRef (width + gates.length) output) := by
  have hall : (compileCode width gates output).all (fun gate => gate.2.length == 2) = true := by
    simp [compileCode, translateProgram]
  rw [serializeCode, CircuitFormat.encode, ite_eq_left hall]
  simp [compileCode, translateProgram, List.flatMap_map, List.append_assoc]

/-- Capped serialization is polynomial-time on every raw native program code.
The unary wire budget bounds allocations even when binary references are invalid. -/
@[fun_prop] theorem serializeCode_polyTime {Input : Type} {input : Input ↪ List Bool}
    {width output : Input → ℕ} {gates : Input → List (Boolean.Op × List ℕ)}
    (hwidth : ComputableInPolyTime width input encUnary)
    (hgates : ComputableInPolyTime gates input (encList Boolean.encGate))
    (houtput : ComputableInPolyTime output input encNat) :
    ComputableInPolyTime (fun a => serializeCode (width a) (gates a) (output a))
      input encBits := by
  have hlength := (ComputableInPolyTime.length_list Boolean.encGate).comp hgates
  have hbudget := ComputableInPolyTime.unary_add' hwidth hlength
  have hgate : ComputableInPolyTime
      (fun p : Input × (Boolean.Op × List ℕ) =>
        let gate := translateGate (width p.1 + (gates p.1).length) p.2
        CircuitFormat.encodeGate gate.1 (gate.2.getD 0 0) (gate.2.getD 1 0))
      (encPair input Boolean.encGate) encBits :=
    encodeTranslatedGate_polyTime.comp
      ((hbudget.comp (ComputableInPolyTime.fst input Boolean.encGate)).prod
        (ComputableInPolyTime.snd input Boolean.encGate))
  have hbody := ComputableInPolyTime.flatMapToBitsWithInput
    (f := fun (a : Input) (gate : Boolean.Op × List ℕ) =>
      let translated := translateGate (width a + (gates a).length) gate
      CircuitFormat.encodeGate translated.1
        (translated.2.getD 0 0) (translated.2.getD 1 0)) hgates hgate
  have hheader := encodeUnary_polyTime (ComputableInPolyTime.unary_succ.comp hlength)
  have hcap := capRef_polyTime hbudget houtput
  have hcopy := encodeGate_polyTime (ComputableInPolyTime.const (true, false, false)) hcap hcap
  have h := ComputableInPolyTime.bitsAppend
    (ComputableInPolyTime.bitsAppend hheader hbody) hcopy
  simpa only [serializeCode_eq, Function.comp_apply] using h

/-- Tagged compilation is polynomial-time on all raw codes, including empty input width. -/
@[fun_prop] theorem serializeTaggedCode_polyTime {Input : Type} {input : Input ↪ List Bool}
    {width output : Input → ℕ} {gates : Input → List (Boolean.Op × List ℕ)}
    (hwidth : ComputableInPolyTime width input encUnary)
    (hgates : ComputableInPolyTime gates input (encList Boolean.encGate))
    (houtput : ComputableInPolyTime output input encNat) :
    ComputableInPolyTime (fun a => serializeTaggedCode (width a) (gates a) (output a))
      input encBits := by
  have hvalue : ComputableInPolyTime
      (fun a => Boolean.evalOutput [] (gates a) (output a)) input encBool :=
    Boolean.computableInPolyTime_evalOutput (ComputableInPolyTime.const []) hgates houtput
  have hzero := ComputableInPolyTime.bitsCons (ComputableInPolyTime.const false)
    (ComputableInPolyTime.bitsCons hvalue (ComputableInPolyTime.const []))
  have hpositive := ComputableInPolyTime.bitsCons (ComputableInPolyTime.const true)
    (serializeCode_polyTime hwidth hgates houtput)
  have h := (ComputableInPolyTime.decide_eq' hwidth (ComputableInPolyTime.const 0)).ite
    hzero hpositive
  simpa only [serializeTaggedCode, decide_eq_true_eq] using h

end GameTheory.Complexity.Backend.CircuitCompiler
