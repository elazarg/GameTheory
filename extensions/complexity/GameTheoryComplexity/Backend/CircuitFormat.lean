module

public import Complexity.Computability.Circuit.Encoding.Check
public import Complexity.Computability.Circuit.Encoding.Evaluation
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
public import Mathlib.Data.List.Basic

@[expose] public section

/-! The serialized Boolean circuit format uses binary AND/OR gates with an
optional negation on each argument. Its gates are ordinary native circuit codes
over a fixed finite signature; native evaluation and validation provide the
semantics and polynomial-time certificates. -/

namespace GameTheory.Complexity.Backend.CircuitFormat

open Cslib.Circuits Turing.MultiTapeTM
open ComputableInPolyTime

/-- The operation bit selects AND or OR; the other bits negate the two inputs. -/
abbrev signature : Signature where
  Op := Bool × Bool × Bool
  Arity _ := 2

/-- The value of one operation on its two arguments. -/
def opValue (op : signature.Op) (left right : Bool) : Bool :=
  let left := op.2.1.xor left
  let right := op.2.2.xor right
  if op.1 then left && right else left || right

/-- The concrete operation flags interpreted in the native circuit semantics. -/
def interpretation : Interpretation signature Bool :=
  fun op inputs => opValue op (inputs 0) (inputs 1)

/-- The native intermediate encoding of the three operation flags. -/
abbrev encOp : signature.Op ↪ List Bool :=
  encPair encBool (encPair encBool encBool)

/-- Native gate codes store operation flags and binary wire numbers. -/
abbrev encGate : (signature.Op × List ℕ) ↪ List Bool :=
  Circuit.encGate encOp

/-- The native intermediate encoding of an ordered gate list. -/
abbrev encProgram : List (signature.Op × List ℕ) ↪ List Bool :=
  encList encGate

/-- Native circuit codes include the ordered gates and designated output wires. -/
abbrev encCode : (List (signature.Op × List ℕ) × List ℕ) ↪ List Bool :=
  Circuit.encCode encOp

private theorem computableInPolyTime_step :
    ComputableInPolyTime (fun p : List Bool × (signature.Op × List ℕ) =>
      p.1 ++ [interpretation p.2.1 fun a => p.2.2[a.val]?.elim false (p.1.getD · false)])
      (encPair encBits encGate) encBits := by
  have hargs (i : ℕ) : ComputableInPolyTime (fun p : List Bool × (signature.Op × List ℕ) =>
      p.2.2[i]?.elim false (p.1.getD · false)) (encPair encBits encGate) encBool :=
    optionElimWithInput (getElem? (snd _ _).snd' (const i)) (const false)
      (listGetD_binary false (fst _ _).fst' (snd _ _))
  have hvalue : ComputableInPolyTime (fun p : List Bool × (signature.Op × List ℕ) =>
      opValue p.2.1 (p.2.2[0]?.elim false (p.1.getD · false))
        (p.2.2[1]?.elim false (p.1.getD · false)))
      (encPair encBits encGate) encBool :=
    (of_finite (encIn := encPair encOp (encPair encBool encBool))
      fun p : signature.Op × Bool × Bool => opValue p.1 p.2.1 p.2.2).comp
      ((snd _ _).fst'.prod ((hargs 0).prod (hargs 1)))
  exact bitsAppend (fst _ _) (bitsCons hvalue (const []))

/-- Native gate-list evaluation is polynomial-time, including binary wire lookup. -/
@[fun_prop]
theorem computableInPolyTime_evalCode {α : Type} {encIn : α ↪ List Bool}
    {input : α → List Bool} {gates : α → List (signature.Op × List ℕ)}
    (hinput : ComputableInPolyTime input encIn encBits)
    (hgates : ComputableInPolyTime gates encIn encProgram) :
    ComputableInPolyTime (fun a => evalCode interpretation false (input a) (gates a))
      encIn encBits :=
  foldl_of_bounded_growth hgates hinput computableInPolyTime_step (growth := 1) fun _ _ => by simp

/-- Read an output wire after native evaluation; missing wires have value false. -/
def evalOutput (input : List Bool) (gates : List (signature.Op × List ℕ)) (wire : ℕ) : Bool :=
  (evalCode interpretation false input gates).getD wire false

/-- Reading an efficiently computed binary output position is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_evalOutput {α : Type} {encIn : α ↪ List Bool}
    {input : α → List Bool} {gates : α → List (signature.Op × List ℕ)} {wire : α → ℕ}
    (hinput : ComputableInPolyTime input encIn encBits)
    (hgates : ComputableInPolyTime gates encIn encProgram)
    (hwire : ComputableInPolyTime wire encIn encNat) :
    ComputableInPolyTime (fun a => evalOutput (input a) (gates a) (wire a)) encIn encBool :=
  listGetD_binary false (computableInPolyTime_evalCode hinput hgates) hwire

/-- Native validation checks the arity and every backward wire reference. -/
@[fun_prop]
theorem computableInPolyTime_codeCheck {α : Type} {encIn : α ↪ List Bool}
    {width : α → ℕ} {gates : α → List (signature.Op × List ℕ)}
    (hwidth : ComputableInPolyTime width encIn encUnary)
    (hgates : ComputableInPolyTime gates encIn encProgram) :
    ComputableInPolyTime (fun a => codeCheck signature (width a) (gates a)) encIn encBool :=
  Cslib.Circuits.computableInPolyTime_codeCheck (const 2) hwidth hgates

/-- Terminated unary fields are one bit per unit followed by a zero delimiter. -/
def encodeUnary (n : ℕ) : List Bool :=
  List.replicate n true ++ [false]

/-- Parse one terminated unary field, retaining the unconsumed suffix. -/
def decodeUnaryPrefix? : List Bool → Option (ℕ × List Bool)
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest => (decodeUnaryPrefix? rest).map fun p => (p.1 + 1, p.2)

@[simp]
theorem decodeUnaryPrefix?_encode (n : ℕ) (rest : List Bool) :
    decodeUnaryPrefix? (encodeUnary n ++ rest) = some (n, rest) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa only [encodeUnary, List.replicate_succ, List.cons_append,
      decodeUnaryPrefix?, Option.map_some] using
      congrArg (Option.map fun p : ℕ × List Bool => (p.1 + 1, p.2)) ih

/-- A decoded unary prefix accounts for every bit before its returned suffix. -/
theorem decodeUnaryPrefix?_sound {bits rest : List Bool} {n : ℕ}
    (h : decodeUnaryPrefix? bits = some (n, rest)) :
    bits = encodeUnary n ++ rest := by
  induction bits generalizing n rest with
  | nil => simp [decodeUnaryPrefix?] at h
  | cons bit bits ih =>
    cases bit with
    | false =>
      change some (0, bits) = some (n, rest) at h
      cases h
      rfl
    | true =>
      cases hp : decodeUnaryPrefix? bits with
      | none => simp [decodeUnaryPrefix?, hp] at h
      | some parsed =>
        obtain ⟨k, suffix⟩ := parsed
        simp only [decodeUnaryPrefix?, hp, Option.map_some, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [ih hp]
        simp [encodeUnary, List.replicate_succ, List.append_assoc]

/-- The strict unary decoder inverts exactly its terminated-prefix serializer. -/
theorem decodeUnaryPrefix?_eq_some_iff (bits rest : List Bool) (n : ℕ) :
    decodeUnaryPrefix? bits = some (n, rest) ↔ bits = encodeUnary n ++ rest :=
  ⟨decodeUnaryPrefix?_sound, fun h => by rw [h]; exact decodeUnaryPrefix?_encode n rest⟩

/-- Serialize the three operation flags and the two terminated unary references. -/
def encodeGate (op : signature.Op) (left right : ℕ) : List Bool :=
  [op.1, op.2.1, op.2.2] ++ encodeUnary left ++ encodeUnary right

/-- Parse a gate directly into the native operation-and-argument-list representation. -/
def decodeGatePrefix? :
    List Bool → Option ((signature.Op × List ℕ) × List Bool)
  | op :: negateLeft :: negateRight :: rest => do
      let (left, rest) ← decodeUnaryPrefix? rest
      let (right, rest) ← decodeUnaryPrefix? rest
      pure (((op, negateLeft, negateRight), [left, right]), rest)
  | _ => none

@[simp]
theorem decodeGatePrefix?_encode (op : signature.Op) (left right : ℕ) (rest : List Bool) :
    decodeGatePrefix? (encodeGate op left right ++ rest) =
      some ((op, [left, right]), rest) := by
  rcases op with ⟨op, negateLeft, negateRight⟩
  simp [encodeGate, decodeGatePrefix?, List.append_assoc]

/-- Parse exactly the declared number of gate prefixes. -/
def decodeGates? :
    ℕ → List Bool → Option (List (signature.Op × List ℕ) × List Bool)
  | 0, bits => some ([], bits)
  | count + 1, bits => do
      let (gate, rest) ← decodeGatePrefix? bits
      let (gates, rest) ← decodeGates? count rest
      pure (gate :: gates, rest)

/-- Serialize an ordered native gate list in the concrete byte format.
Native argument lists of arity other than two produce the invalid empty word.
This pure serializer makes no complexity claim for unbounded binary wire numbers. -/
def encode (gates : List (signature.Op × List ℕ)) : List Bool :=
  if gates.all (fun gate => gate.2.length == 2) then
    encodeUnary gates.length ++ gates.flatMap fun gate =>
      encodeGate gate.1 (gate.2.getD 0 0) (gate.2.getD 1 0)
  else []

/-- Decode exactly one gate-count-prefixed byte stream, rejecting trailing garbage. -/
def decode? (bits : List Bool) : Option (List (signature.Op × List ℕ)) :=
  match decodeUnaryPrefix? bits with
  | none => none
  | some (count, rest) =>
      match decodeGates? count rest with
      | some (gates, []) => some gates
      | _ => none

private theorem decodeGates?_encode (gates : List (signature.Op × List ℕ))
    (h : ∀ gate ∈ gates, gate.2.length = 2) (rest : List Bool) :
    decodeGates? gates.length
      ((gates.flatMap fun gate =>
        encodeGate gate.1 (gate.2.getD 0 0) (gate.2.getD 1 0)) ++ rest) =
      some (gates, rest) := by
  revert h
  induction gates generalizing rest with
  | nil =>
    intro _
    rfl
  | cons gate gates ih =>
    intro h
    rcases gate with ⟨op, args⟩
    obtain ⟨left, right, rfl⟩ :=
      List.length_eq_two.mp (h (op, args) (by simp))
    have htail : ∀ gate ∈ gates, gate.2.length = 2 :=
      fun gate hg => h gate (by simp [hg])
    simp only [List.length_cons, List.flatMap_cons, List.getD_cons_zero,
      List.getD_cons_succ, List.append_assoc, decodeGates?,
      decodeGatePrefix?_encode, bind, Option.bind_some]
    rw [ih (rest := rest) htail]
    rfl

/-- Every native gate list with the concrete binary arity round-trips exactly. -/
@[simp]
theorem decode?_encode (gates : List (signature.Op × List ℕ))
    (h : ∀ gate ∈ gates, gate.2.length = 2) :
    decode? (encode gates) = some gates := by
  have hargs : gates.all (fun gate => gate.2.length == 2) = true := by
    apply List.all_eq_true.mpr
    intro gate hg
    simp [h gate hg]
  have hgates :
      decodeGates? gates.length (gates.flatMap fun gate =>
        encodeGate gate.1 (gate.2.getD 0 0) (gate.2.getD 1 0)) =
        some (gates, []) := by
    simpa only [List.append_nil] using decodeGates?_encode gates h []
  rw [encode, ite_eq_left hargs]
  simp only [decode?, decodeUnaryPrefix?_encode, hgates]

/-- Exact-width scalar evaluation rejects syntax errors, empty programs and
every invalid wire topology before using the native total evaluator. -/
def eval? (width : ℕ) (code input : List Bool) : Option Bool := do
  if input.length = width then
    let gates ← decode? code
    if gates.isEmpty || !codeCheck signature width gates then
      none
    else
      some (evalOutput input gates (width + gates.length - 1))
  else
    none

/-- Empty-input codes carry exactly one explicit answer bit after the zero tag.
Nonempty inputs require the positive tag followed by one strict scalar program. -/
def evalTagged? (code input : List Bool) : Option Bool :=
  if input.isEmpty then
    match code with
    | [false, answer] => some answer
    | _ => none
  else
    match code with
    | true :: program => eval? input.length program input
    | _ => none

@[simp]
theorem decode?_nil : decode? [] = none := rfl

@[simp]
theorem decode?_empty : decode? [false] = some [] := rfl

@[simp]
theorem eval?_nil (width : ℕ) (input : List Bool) :
    eval? width [] input = none := by
  simp [eval?, decode?, decodeUnaryPrefix?]

@[simp]
theorem eval?_empty (width : ℕ) (input : List Bool) :
    eval? width [false] input = none := by
  simp [eval?, decode?, decodeUnaryPrefix?, decodeGates?]

@[simp]
theorem evalTagged?_zero (answer : Bool) :
    evalTagged? [false, answer] [] = some answer := rfl

@[simp]
theorem evalTagged?_positive_nil (code : List Bool) :
    evalTagged? (true :: code) [] = none := rfl

@[simp]
theorem evalTagged?_zero_nonempty (answer bit : Bool) (input : List Bool) :
    evalTagged? [false, answer] (bit :: input) = none := rfl

/-- The first zero delimiter gives the same strict unary prefix as recursive parsing. -/
private theorem decodeUnaryPrefix?_eq_index (bits : List Bool) :
    decodeUnaryPrefix? bits =
      if bits.idxOf false < bits.length then
        some (bits.idxOf false, bits.drop (bits.idxOf false + 1))
      else none := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
    cases bit with
    | false => simp [decodeUnaryPrefix?]
    | true =>
      rw [decodeUnaryPrefix?, ih]
      simp only [List.idxOf_cons, List.length_cons]
      by_cases h : bits.idxOf false < bits.length
      · simp [h, List.drop_succ_cons]
      · simp [h]

/-- Strict unary parsing charges delimiter search, unary indexing and suffix extraction. -/
@[fun_prop]
theorem computableInPolyTime_decodeUnaryPrefix :
    ComputableInPolyTime decodeUnaryPrefix? encBits
      (encOption (encPair encUnary encBits)) := by
  have hindex : ComputableInPolyTime (fun bits : List Bool => bits.idxOf false)
      encBits encUnary :=
    idxOfWithInput bitsToList (const false)
  have hrest : ComputableInPolyTime
      (fun bits : List Bool => bits.drop (bits.idxOf false + 1)) encBits encBits :=
    bitsDropWithInput id' (unary_succ.comp hindex)
  have hsome : ComputableInPolyTime
      (fun bits : List Bool => some (bits.idxOf false, bits.drop (bits.idxOf false + 1)))
      encBits (encOption (encPair encUnary encBits)) :=
    (optionSome (encPair encUnary encBits)).comp (hindex.prod hrest)
  have h := (unary_lt' hindex length_bits).ite hsome (const none)
  have heq : decodeUnaryPrefix? = fun bits =>
      if bits.idxOf false < bits.length then
        some (bits.idxOf false, bits.drop (bits.idxOf false + 1)) else none :=
    funext decodeUnaryPrefix?_eq_index
  rw [heq]
  simpa only [decide_eq_true_eq] using h

/-- A unary count read from bytes can be returned in the native binary scalar encoding. -/
@[fun_prop]
theorem computableInPolyTime_decodeUnaryPrefix_binary :
    ComputableInPolyTime decodeUnaryPrefix? encBits
      (encOption (encPair encNat encBits)) := by
  have hvalue : ComputableInPolyTime
      (fun p : List Bool × (ℕ × List Bool) => p.2)
      (encPair encBits (encPair encUnary encBits)) (encPair encNat encBits) :=
    (unary_to_binary.comp (snd _ _).fst').prod (snd _ _).snd'
  have h := computableInPolyTime_decodeUnaryPrefix.optionMapWithInput
    (f := fun (_ : List Bool) (p : ℕ × List Bool) => p) hvalue
  simpa using h

private theorem decodeGatePrefix?_eq_elim (bits : List Bool) :
    decodeGatePrefix? bits =
      if 3 ≤ bits.length then
        (decodeUnaryPrefix? (bits.drop 3)).elim none fun left =>
          (decodeUnaryPrefix? left.2).map fun right =>
            (((bits.getD 0 false, bits.getD 1 false, bits.getD 2 false),
              [left.1, right.1]), right.2)
      else none := by
  rcases bits with _ | ⟨a, bits⟩
  · rfl
  rcases bits with _ | ⟨b, bits⟩
  · rfl
  rcases bits with _ | ⟨c, bits⟩
  · rfl
  simp only [decodeGatePrefix?, List.length_cons, List.drop_succ_cons, List.drop_zero,
    List.getD_cons_zero, List.getD_cons_succ]
  rw [ite_eq_left (by omega)]
  cases hl : decodeUnaryPrefix? bits with
  | none => rfl
  | some left =>
    rcases left with ⟨left, rest⟩
    cases hr : decodeUnaryPrefix? rest with
    | none => simp [bind, hr]
    | some right =>
      rcases right with ⟨right, suffix⟩
      simp [bind, hr]

/-- Gate parsing reads two unary fields and converts them to native binary references.
Both option eliminations charge the complete captured byte word. -/
@[fun_prop]
theorem computableInPolyTime_decodeGatePrefix :
    ComputableInPolyTime decodeGatePrefix? encBits
      (encOption (encPair encGate encBits)) := by
  let valueEncoding := encPair encUnary encBits
  let prefixEncoding := encPair encBits valueEncoding
  have hflags : ComputableInPolyTime
      (fun bits : List Bool => (bits.getD 0 false, bits.getD 1 false, bits.getD 2 false))
      encBits encOp :=
    (bitsGetDWithInput id' (const 0) false).prod
      ((bitsGetDWithInput id' (const 1) false).prod
        (bitsGetDWithInput id' (const 2) false))
  have hleft : ComputableInPolyTime
      (fun bits : List Bool => decodeUnaryPrefix? (bits.drop 3))
      encBits (encOption valueEncoding) :=
    computableInPolyTime_decodeUnaryPrefix.comp (bitsDropWithInput id' (const 3))
  have hright : ComputableInPolyTime
      (fun p : List Bool × (ℕ × List Bool) => decodeUnaryPrefix? p.2.2)
      prefixEncoding (encOption valueEncoding) :=
    computableInPolyTime_decodeUnaryPrefix.comp (snd _ _).snd'
  have hfinish : ComputableInPolyTime
      (fun p : (List Bool × (ℕ × List Bool)) × (ℕ × List Bool) =>
        (((p.1.1.getD 0 false, p.1.1.getD 1 false, p.1.1.getD 2 false),
          [p.1.2.1, p.2.1]), p.2.2))
      (encPair prefixEncoding valueEncoding) (encPair encGate encBits) :=
    ((hflags.comp (fst _ _).fst').prod
      (cons' (unary_to_binary.comp (fst _ _).snd'.fst')
        (cons' (unary_to_binary.comp (snd _ _).fst') (const [])))).prod
      (snd _ _).snd'
  have hsecond := hright.optionMapWithInput
    (f := fun p right =>
      (((p.1.getD 0 false, p.1.getD 1 false, p.1.getD 2 false),
        [p.2.1, right.1]), right.2)) hfinish
  have hbody := hleft.optionElimWithInput
    (body := fun bits left => (decodeUnaryPrefix? left.2).map fun right =>
      (((bits.getD 0 false, bits.getD 1 false, bits.getD 2 false),
        [left.1, right.1]), right.2)) (const none) hsecond
  have h := (unary_le' (const 3) length_bits).ite hbody (const none)
  have heq : decodeGatePrefix? = fun bits =>
      if 3 ≤ bits.length then
        (decodeUnaryPrefix? (bits.drop 3)).elim none fun left =>
          (decodeUnaryPrefix? left.2).map fun right =>
            (((bits.getD 0 false, bits.getD 1 false, bits.getD 2 false),
              [left.1, right.1]), right.2)
      else none := funext decodeGatePrefix?_eq_elim
  rw [heq]
  simpa only [decide_eq_true_eq] using h

private theorem decodeUnaryPrefix?_suffixLength {bits rest : List Bool} {n : ℕ}
    (h : decodeUnaryPrefix? bits = some (n, rest)) : rest.length ≤ bits.length := by
  have heq := congrArg List.length (decodeUnaryPrefix?_sound h)
  simp only [encodeUnary, List.length_append, List.length_replicate,
    List.length_singleton] at heq
  omega

private theorem decodeGatePrefix?_suffixLength {bits rest : List Bool}
    {gate : signature.Op × List ℕ} (h : decodeGatePrefix? bits = some (gate, rest)) :
    rest.length ≤ bits.length := by
  rw [decodeGatePrefix?_eq_elim] at h
  split_ifs at h
  · cases hl : decodeUnaryPrefix? (bits.drop 3) with
    | none => simp [hl] at h
    | some left =>
      rcases left with ⟨left, suffix⟩
      cases hr : decodeUnaryPrefix? suffix with
      | none => simp [hl, hr] at h
      | some right =>
        rcases right with ⟨right, tail⟩
        simp only [hl, Option.elim_some, hr, Option.map_some] at h
        cases h
        have hleft := decodeUnaryPrefix?_suffixLength hl
        have hright := decodeUnaryPrefix?_suffixLength hr
        simp only [List.length_drop] at hleft
        omega
private abbrev parserValueEncoding :
    (List (signature.Op × List ℕ) × List Bool) ↪ List Bool :=
  encPair encProgram encBits

private abbrev parserStateEncoding :
    Option (List (signature.Op × List ℕ) × List Bool) ↪ List Bool :=
  encOption parserValueEncoding

/-- The captured budget bounds every gate-parser call, including unreachable states. -/
private def parserStep (budget : ℕ)
    (state : Option (List (signature.Op × List ℕ) × List Bool)) :
    Option (List (signature.Op × List ℕ) × List Bool) :=
  state.bind fun p => (decodeGatePrefix? (p.2.take budget)).map fun q => (q.1 :: p.1, q.2)

private theorem parserStep_iterate_none (budget count : ℕ) :
    (parserStep budget)^[count] none = none := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simpa only [Function.iterate_succ_apply, parserStep, Option.bind_none] using ih

private theorem parserLoop_spec (budget count : ℕ)
    (acc : List (signature.Op × List ℕ)) (rest : List Bool) (hrest : rest.length ≤ budget) :
    ((parserStep budget)^[count] (some (acc, rest))).map (fun p => (p.1.reverse, p.2)) =
      (decodeGates? count rest).map (fun p => (acc.reverse ++ p.1, p.2)) := by
  induction count generalizing acc rest with
  | zero => simp [decodeGates?]
  | succ count ih =>
    have hcap : rest.take budget = rest := List.take_of_length_le hrest
    have hstep : parserStep budget (some (acc, rest)) =
        (decodeGatePrefix? rest).map (fun q => (q.1 :: acc, q.2)) := by
      simp only [parserStep, Option.bind_some, hcap]
    rw [Function.iterate_succ_apply, hstep]
    cases hp : decodeGatePrefix? rest with
    | none =>
      simp only [Option.map_none, decodeGates?, hp, bind, Option.bind_none]
      exact congrArg (Option.map fun p => (p.1.reverse, p.2))
        (parserStep_iterate_none budget count)
    | some parsed =>
      rcases parsed with ⟨gate, suffix⟩
      simp only [Option.map_some]
      rw [ih (acc := gate :: acc) (rest := suffix)
        ((decodeGatePrefix?_suffixLength hp).trans hrest)]
      simp only [decodeGates?, hp, bind, Option.bind_some]
      cases ht : decodeGates? count suffix with
      | none => simp
      | some parsed =>
        rcases parsed with ⟨gates, tail⟩
        simp [List.reverse_cons, List.append_assoc]

private theorem computableInPolyTime_parserStep :
    ComputableInPolyTime
      (fun p : ℕ × Option (List (signature.Op × List ℕ) × List Bool) => parserStep p.1 p.2)
      (encPair encUnary parserStateEncoding) parserStateEncoding := by
  let outerEncoding := encPair encUnary parserStateEncoding
  let parsedEncoding := encPair encGate encBits
  let callbackEncoding := encPair outerEncoding parserValueEncoding
  have hparse : ComputableInPolyTime
      (fun p : (ℕ × Option (List (signature.Op × List ℕ) × List Bool)) ×
          (List (signature.Op × List ℕ) × List Bool) =>
        decodeGatePrefix? (p.2.2.take p.1.1))
      (encPair outerEncoding parserValueEncoding) (encOption (encPair encGate encBits)) :=
    computableInPolyTime_decodeGatePrefix.comp
      (bitsTakeWithInput (snd outerEncoding parserValueEncoding).snd'
        (fst outerEncoding parserValueEncoding).fst')
  have hfinish : ComputableInPolyTime
      (fun p : ((ℕ × Option (List (signature.Op × List ℕ) × List Bool)) ×
          (List (signature.Op × List ℕ) × List Bool)) ×
          ((signature.Op × List ℕ) × List Bool) =>
        (p.2.1 :: p.1.2.1, p.2.2))
      (encPair (encPair outerEncoding parserValueEncoding) (encPair encGate encBits))
      parserValueEncoding :=
    (cons' (snd callbackEncoding parsedEncoding).fst'
      (fst callbackEncoding parsedEncoding).snd'.fst').prod
        (snd callbackEncoding parsedEncoding).snd'
  have hbody : ComputableInPolyTime
      (fun p : (ℕ × Option (List (signature.Op × List ℕ) × List Bool)) ×
          (List (signature.Op × List ℕ) × List Bool) =>
        (decodeGatePrefix? (p.2.2.take p.1.1)).map fun q => (q.1 :: p.2.1, q.2))
      callbackEncoding parserStateEncoding :=
    hparse.optionMapWithInput
      (f := fun
        (p : (ℕ × Option (List (signature.Op × List ℕ) × List Bool)) ×
          (List (signature.Op × List ℕ) × List Bool))
        (q : (signature.Op × List ℕ) × List Bool) => (q.1 :: p.2.1, q.2)) hfinish
  have h : ComputableInPolyTime
      (fun p : ℕ × Option (List (signature.Op × List ℕ) × List Bool) =>
        p.2.elim none fun state => (decodeGatePrefix? (state.2.take p.1)).map
          fun q => (q.1 :: state.1, q.2)) outerEncoding parserStateEncoding :=
    (snd encUnary parserStateEncoding).optionElimWithInput
    (body := fun
      (p : ℕ × Option (List (signature.Op × List ℕ) × List Bool))
      (state : List (signature.Op × List ℕ) × List Bool) =>
        (decodeGatePrefix? (state.2.take p.1)).map fun q => (q.1 :: state.1, q.2))
      (const (encIn := outerEncoding) (encOut := parserStateEncoding) none) hbody
  have heq :
      (fun p : ℕ × Option (List (signature.Op × List ℕ) × List Bool) => parserStep p.1 p.2) =
      (fun p => p.2.elim none fun state =>
        (decodeGatePrefix? (state.2.take p.1)).map fun q => (q.1 :: state.1, q.2)) := by
    funext p
    rcases p with ⟨budget, state⟩
    cases state <;> rfl
  rw [heq]
  exact h

private theorem parserStep_growth (c d : ℕ)
    (hbound : ∀ bits : List Bool,
      ((encOption (encPair encGate encBits)) (decodeGatePrefix? bits)).length ≤
        c * (bits.length + 1) ^ d)
    (budget : ℕ) (state : Option (List (signature.Op × List ℕ) × List Bool)) :
    (parserStateEncoding (parserStep budget state)).length ≤
      (parserStateEncoding state).length + 4 * (c * (budget + 1) ^ d) + 2 := by
  cases state with
  | none => simp [parserStep, parserStateEncoding]
  | some state =>
    rcases state with ⟨acc, rest⟩
    cases hp : decodeGatePrefix? (rest.take budget) with
    | none => simp [parserStep, hp, parserStateEncoding]
    | some parsed =>
      rcases parsed with ⟨gate, suffix⟩
      have hparser := hbound (rest.take budget)
      rw [hp, encOption_some] at hparser
      simp only [List.length_cons] at hparser
      rw [length_encPair] at hparser
      simp only [encBits_apply] at hparser
      have htake : (rest.take budget).length + 1 ≤ budget + 1 := by
        simp only [List.length_take]
        omega
      have hmono := Nat.mul_le_mul_left c (Nat.pow_le_pow_left htake d)
      have hcombined : 2 * (encGate gate).length + suffix.length ≤
          c * (budget + 1) ^ d := by omega
      simp only [encGate, encOp, length_encPair] at hcombined
      simp only [parserStep, Option.bind_some, hp, Option.map_some, parserStateEncoding,
        encOption_some, List.length_cons, parserValueEncoding, length_encPair, encBits_apply,
        encProgram, encList_cons, List.length_append, length_frame]
      omega

/-- The declared unary gate count drives an actual bounded native parser loop. -/
@[fun_prop]
theorem computableInPolyTime_decodeGates :
    ComputableInPolyTime (fun p : ℕ × List Bool => decodeGates? p.1 p.2)
      (encPair encUnary encBits) (encOption (encPair encProgram encBits)) := by
  obtain ⟨c, d, hbound⟩ :=
    computableInPolyTime_decodeGatePrefix.polyBounded_length.exists_le
  have hbudget : ComputableInPolyTime (fun p : ℕ × List Bool => p.2.length)
      (encPair encUnary encBits) encUnary :=
    length_bits.comp (snd encUnary encBits)
  have hB : PolyBounded (fun p : ℕ × List Bool => ((encPair encUnary encBits) p).length)
      (fun p => p.2.length) := by
    simpa only [encUnary_apply, List.length_replicate] using hbudget.polyBounded_length
  have hgrowth :
      PolyBounded (fun p : ℕ × List Bool => ((encPair encUnary encBits) p).length)
        (fun p => 4 * (c * (p.2.length + 1) ^ d) + 2) :=
    ((PolyBounded.const 4).mul
      ((PolyBounded.const c).mul ((hB.add (.const 1)).pow d))).add (.const 2)
  have hinit : ComputableInPolyTime (fun p : ℕ × List Bool => some ([], p.2))
      (encPair encUnary encBits) parserStateEncoding :=
    (optionSome parserValueEncoding).comp ((const []).prod (snd encUnary encBits))
  have hloop : ComputableInPolyTime
      (fun p : ℕ × List Bool => (parserStep p.2.length)^[p.1] (some ([], p.2)))
      (encPair encUnary encBits) parserStateEncoding :=
    iterateWith_of_bounded_growth
      (par := fun p : ℕ × List Bool => p.2.length)
      (count := fun p : ℕ × List Bool => p.1)
      (init := fun p : ℕ × List Bool => some ([], p.2))
      (step := parserStep) hbudget (fst encUnary encBits) hinit
      computableInPolyTime_parserStep hgrowth
      (fun p state => parserStep_growth c d hbound p.2.length state)
  have hfinish : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × (List (signature.Op × List ℕ) × List Bool) =>
        (p.2.1.reverse, p.2.2))
      (encPair (encPair encUnary encBits) parserValueEncoding) parserValueEncoding :=
    (listReverseWithInput (snd _ _).fst').prod (snd _ _).snd'
  have hresult := hloop.optionMapWithInput
    (f := fun (_ : ℕ × List Bool) (state : List (signature.Op × List ℕ) × List Bool) =>
      (state.1.reverse, state.2)) hfinish
  have heq :
      (fun p : ℕ × List Bool => decodeGates? p.1 p.2) =
      (fun p => ((parserStep p.2.length)^[p.1] (some ([], p.2))).map
        (fun state => (state.1.reverse, state.2))) := by
    funext p
    symm
    simpa using parserLoop_spec p.2.length p.1 [] p.2 (le_refl _)
  rw [heq]
  exact hresult

/-- Strict whole-program decoding charges count parsing, the native gate loop and
the rejection of every nonempty trailing suffix. -/
@[fun_prop]
theorem computableInPolyTime_decode :
    ComputableInPolyTime decode? encBits (encOption encProgram) := by
  let headerEncoding := encPair encUnary encBits
  let outerEncoding := encPair encBits headerEncoding
  let resultEncoding := encOption encProgram
  have hloop : ComputableInPolyTime
      (fun p : List Bool × (ℕ × List Bool) => decodeGates? p.2.1 p.2.2)
      outerEncoding parserStateEncoding :=
    computableInPolyTime_decodeGates.comp (snd encBits headerEncoding)
  have hfinish : ComputableInPolyTime
      (fun p : (List Bool × (ℕ × List Bool)) ×
          (List (signature.Op × List ℕ) × List Bool) =>
        if p.2.2 = [] then some p.2.1 else none)
      (encPair outerEncoding parserValueEncoding) resultEncoding := by
    have htest := decide_eq' (snd outerEncoding parserValueEncoding).snd' (const [])
    have hsome := (optionSome encProgram).comp (snd outerEncoding parserValueEncoding).fst'
    simpa only [Function.comp_def, decide_eq_true_eq] using
      htest.ite hsome (const (encOut := resultEncoding) none)
  have hafterLoop : ComputableInPolyTime
      (fun p : List Bool × (ℕ × List Bool) =>
        (decodeGates? p.2.1 p.2.2).elim none fun value =>
          if value.2 = [] then some value.1 else none) outerEncoding resultEncoding :=
    hloop.optionElimWithInput
      (body := fun (_ : List Bool × (ℕ × List Bool))
        (value : List (signature.Op × List ℕ) × List Bool) =>
          if value.2 = [] then some value.1 else none)
      (const (encOut := resultEncoding) none) hfinish
  have hwhole : ComputableInPolyTime
      (fun bits : List Bool => (decodeUnaryPrefix? bits).elim none fun header =>
        (decodeGates? header.1 header.2).elim none fun value =>
          if value.2 = [] then some value.1 else none) encBits resultEncoding :=
    computableInPolyTime_decodeUnaryPrefix.optionElimWithInput
      (body := fun (_ : List Bool) (header : ℕ × List Bool) =>
        (decodeGates? header.1 header.2).elim none
          fun value => if value.2 = [] then some value.1 else none)
      (const (encOut := resultEncoding) none) hafterLoop
  have heq : decode? = fun bits =>
      (decodeUnaryPrefix? bits).elim none fun header =>
        (decodeGates? header.1 header.2).elim none
          fun value => if value.2 = [] then some value.1 else none := by
    funext bits
    unfold decode?
    cases hd : decodeUnaryPrefix? bits with
    | none => rfl
    | some header =>
      rcases header with ⟨count, rest⟩
      simp only [Option.elim_some]
      cases hg : decodeGates? count rest with
      | none => rfl
      | some parsed =>
        rcases parsed with ⟨gates, tail⟩
        cases tail <;> rfl
  rw [heq]
  exact hwhole

private theorem eval?_eq_elim (width : ℕ) (code input : List Bool) :
    eval? width code input =
      if input.length = width then
        (decode? code).elim none fun gates =>
          if gates.isEmpty || !codeCheck signature width gates then none
          else some (evalOutput input gates (width + gates.length - 1))
      else none := by
  by_cases h : input.length = width
  · simp only [eval?, h, ↓reduceIte]
    cases decode? code <;> rfl
  · simp [eval?, h]

/-- Scalar evaluation charges strict decoding, topology validation and all native gate steps. -/
@[fun_prop]
theorem computableInPolyTime_eval :
    ComputableInPolyTime
      (fun p : ℕ × (List Bool × List Bool) => eval? p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encBits encBits)) (encOption encBool) := by
  let evaluationEncoding := encPair encUnary (encPair encBits encBits)
  let callbackEncoding := encPair evaluationEncoding encProgram
  have hwidth : ComputableInPolyTime
      (fun p : (ℕ × (List Bool × List Bool)) × List (signature.Op × List ℕ) => p.1.1)
      callbackEncoding encUnary :=
    (fst evaluationEncoding encProgram).fst'
  have hgates : ComputableInPolyTime
      (fun p : (ℕ × (List Bool × List Bool)) × List (signature.Op × List ℕ) => p.2)
      callbackEncoding encProgram := snd evaluationEncoding encProgram
  have hinput : ComputableInPolyTime
      (fun p : (ℕ × (List Bool × List Bool)) × List (signature.Op × List ℕ) => p.1.2.2)
      callbackEncoding encBits :=
    (fst evaluationEncoding encProgram).snd'.snd'
  have hlength := (length_list encGate).comp hgates
  have hwire : ComputableInPolyTime
      (fun p : (ℕ × (List Bool × List Bool)) × List (signature.Op × List ℕ) =>
        p.1.1 + p.2.length - 1) callbackEncoding encNat :=
    unary_to_binary.comp (unary_sub' (unary_add' hwidth hlength) (const 1))
  have hvalue := computableInPolyTime_evalOutput hinput hgates hwire
  have hcheck := computableInPolyTime_codeCheck hwidth hgates
  have hempty : ComputableInPolyTime
      (fun p : (ℕ × (List Bool × List Bool)) × List (signature.Op × List ℕ) => p.2.isEmpty)
      callbackEncoding encBool := by
    simpa only [List.beq_nil_eq] using hgates.beq (const [])
  have hprogram : ComputableInPolyTime
      (fun p : (ℕ × (List Bool × List Bool)) × List (signature.Op × List ℕ) =>
        if p.2.isEmpty || !codeCheck signature p.1.1 p.2 then none
        else some (evalOutput p.1.2.2 p.2 (p.1.1 + p.2.length - 1)))
      callbackEncoding (encOption encBool) := by
    have hreject := bool_or.comp (hempty.prod (bool_not.comp hcheck))
    have hsome := (optionSome encBool).comp hvalue
    simpa only [Function.comp_def] using
      hreject.ite (const (encOut := encOption encBool) none) hsome
  have hdecode : ComputableInPolyTime
      (fun p : ℕ × (List Bool × List Bool) => decode? p.2.1)
      evaluationEncoding (encOption encProgram) :=
    computableInPolyTime_decode.comp (snd encUnary (encPair encBits encBits)).fst'
  have hdecoded : ComputableInPolyTime
      (fun p : ℕ × (List Bool × List Bool) =>
        (decode? p.2.1).elim none fun gates =>
          if gates.isEmpty || !codeCheck signature p.1 gates then none
          else some (evalOutput p.2.2 gates (p.1 + gates.length - 1)))
      evaluationEncoding (encOption encBool) :=
    hdecode.optionElimWithInput
      (body := fun (p : ℕ × (List Bool × List Bool))
        (gates : List (signature.Op × List ℕ)) =>
          if gates.isEmpty || !codeCheck signature p.1 gates then none
          else some (evalOutput p.2.2 gates (p.1 + gates.length - 1)))
      (const (encOut := encOption encBool) none) hprogram
  have htest := decide_eq'
    (length_bits.comp (snd encUnary (encPair encBits encBits)).snd')
    (fst encUnary (encPair encBits encBits))
  have hwhole := htest.ite hdecoded (const (encOut := encOption encBool) none)
  have heq :
      (fun p : ℕ × (List Bool × List Bool) => eval? p.1 p.2.1 p.2.2) =
      (fun p => if p.2.2.length = p.1 then
        (decode? p.2.1).elim none fun gates =>
          if gates.isEmpty || !codeCheck signature p.1 gates then none
          else some (evalOutput p.2.2 gates (p.1 + gates.length - 1))
        else none) := by
    funext p
    exact eval?_eq_elim p.1 p.2.1 p.2.2
  rw [heq]
  simpa only [Function.comp_def, decide_eq_true_eq] using hwhole

private theorem evalTagged?_eq_branches (code input : List Bool) :
    evalTagged? code input =
      if input.isEmpty then
        if decide (code.length = 2) && !code.headD false then some (code.getD 1 false) else none
      else
        if code.headD false then eval? input.length code.tail input else none := by
  cases input with
  | cons bit input =>
    cases code with
    | nil => rfl
    | cons tag body => cases tag <;> rfl
  | nil =>
    cases code with
    | nil => rfl
    | cons tag code =>
      cases code with
      | nil => cases tag <;> rfl
      | cons answer tail =>
        cases tail with
        | nil => cases tag <;> rfl
        | cons bit tail => cases tag <;> simp [evalTagged?]

/-- Tagged family evaluation has the same charged native implementation at every width,
including exact empty-input tags and malformed positive-input byte strings. -/
@[fun_prop]
theorem computableInPolyTime_evalTagged :
    ComputableInPolyTime
      (fun p : List Bool × List Bool => evalTagged? p.1 p.2)
      (encPair encBits encBits) (encOption encBool) := by
  have hcode := fst encBits encBits
  have hinput := snd encBits encBits
  have hhead : ComputableInPolyTime
      (fun p : List Bool × List Bool => p.1.headD false) (encPair encBits encBits) encBool :=
    (headD false).comp hcode
  have hzeroTest := bool_and'
    (decide_eq' (length_bits.comp hcode) (const 2)) (bool_not.comp hhead)
  have hzeroValue := (optionSome encBool).comp (bitsGetDWithInput hcode (const 1) false)
  have hzero := hzeroTest.ite hzeroValue (const (encOut := encOption encBool) none)
  have hpositiveCall : ComputableInPolyTime
      (fun p : List Bool × List Bool => eval? p.2.length p.1.tail p.2)
      (encPair encBits encBits) (encOption encBool) :=
    computableInPolyTime_eval.comp
      ((length_bits.comp hinput).prod ((bitsTail.comp hcode).prod hinput))
  have hpositive := hhead.ite hpositiveCall (const (encOut := encOption encBool) none)
  have hwhole := (bitsIsEmpty.comp hinput).ite hzero hpositive
  have heq :
      (fun p : List Bool × List Bool => evalTagged? p.1 p.2) =
      (fun p => if p.2.isEmpty then
        if decide (p.1.length = 2) && !p.1.headD false then some (p.1.getD 1 false) else none
        else if p.1.headD false then eval? p.2.length p.1.tail p.2 else none) := by
    funext p
    exact evalTagged?_eq_branches p.1 p.2
  rw [heq]
  simpa only [Function.comp_def, decide_eq_true_eq] using hwhole

end GameTheory.Complexity.Backend.CircuitFormat
