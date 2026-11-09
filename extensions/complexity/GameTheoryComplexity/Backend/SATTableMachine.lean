module

public import GameTheoryComplexity.Backend.SATTableScanner
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

@[expose] public section

/-! Native polynomial-time certificates for the reverse SAT incidence scanner.
Every source bit is visited. The clause and variable counters use unary encodings,
and the uniform transition certificate charges the complete query and state.
-/

namespace GameTheory.Complexity.Backend

open Turing.MultiTapeTM

private abbrev Query := ℕ × Bool × ℕ

private abbrev queryEncoding : Query ↪ List Bool :=
  encPair encUnary (encPair encBool encUnary)

private abbrev Registers := (ℕ × ℕ) × (Bool × Bool × Bool × Bool × Bool × Bool)

private abbrev registerEncoding : Registers ↪ List Bool :=
  encPair (encPair encUnary encUnary)
    (encPair encBool (encPair encBool (encPair encBool (encPair encBool (encPair encBool encBool)))))

private def registers (state : IncidenceState) : Registers :=
  ((state.clauseIndex, state.variableCount),
    (state.waiting, state.saved, state.sign, state.seenData, state.seenClause, state.hit))

private def registerStep (query : Query) (state : Registers) (bit : Bool) : Registers :=
  let finish := state.2.2.2.2.2.2 ||
    (state.2.2.2.2.1 && decide (state.1.2 = query.1) &&
      decide (state.2.2.2.1 = query.2.1) && decide (state.1.1 = query.2.2))
  if state.2.1 then
    if bit then
      if state.2.2.1 then
        ((state.1.1, state.1.2 + state.2.2.2.2.1.toNat),
          (false, state.2.2.1, bit, true, state.2.2.2.2.2.1, state.2.2.2.2.2.2))
      else
        ((state.1.1 + state.2.2.2.2.2.1.toNat, 0),
          (false, state.2.2.1, state.2.2.2.1, false, true, finish))
    else
      if state.2.2.1 then
        ((state.1.1, 0),
          (false, state.2.2.1, state.2.2.2.1, false, state.2.2.2.2.2.1, finish))
      else
        ((state.1.1, state.1.2 + state.2.2.2.2.1.toNat),
          (false, state.2.2.1, bit, true, state.2.2.2.2.2.1, state.2.2.2.2.2.2))
  else
    (state.1, (true, bit, state.2.2.2.1, state.2.2.2.2.1,
      state.2.2.2.2.2.1, state.2.2.2.2.2.2))

private theorem registerStep_eq (query : Query) (state : IncidenceState) (bit : Bool) :
    registerStep query (registers state) bit =
      registers (state.step query.1 query.2.1 query.2.2 bit) := by
  rcases state with ⟨waiting, saved, clause, count, sign, seen, started, hit⟩
  cases waiting <;> cases saved <;> cases bit <;> cases seen <;> cases started <;>
    rfl

private theorem registerStep_polyTime :
    ComputableInPolyTime
      (fun pair : (Query × Registers) × Bool => registerStep pair.1.1 pair.1.2 pair.2)
      (encPair (encPair queryEncoding registerEncoding) encBool) registerEncoding := by
  unfold registerStep
  fun_prop

private theorem registerStep_growth (query : Query) (state : Registers) (bit : Bool) :
    (registerEncoding (registerStep query state bit)).length ≤
      (registerEncoding state).length + 6 := by
  rcases state with ⟨⟨clause, count⟩, waiting, saved, sign, seen, started, hit⟩
  cases waiting <;> cases saved <;> cases bit <;> cases seen <;> cases started <;>
    simp [registerStep, registerEncoding] <;> omega

private theorem registerFold_eq (query : Query) (state : IncidenceState)
    (input : List Bool) :
    input.foldl (registerStep query) (registers state) =
      registers (input.foldl (IncidenceState.step query.1 query.2.1 query.2.2) state) := by
  induction input generalizing state with
  | nil => rfl
  | cons bit input ih =>
      simp only [List.foldl_cons, registerStep_eq, ih]

private def registerVerdict (query : Query) (state : Registers) : Bool :=
  let finish := state.2.2.2.2.2.2 ||
    (state.2.2.2.2.1 && decide (state.1.2 = query.1) &&
      decide (state.2.2.2.1 = query.2.1) && decide (state.1.1 = query.2.2))
  finish || !state.2.2.2.2.2.1 || decide (state.1.1 < query.2.2)

private theorem registerVerdict_polyTime :
    ComputableInPolyTime (fun pair : Query × Registers => registerVerdict pair.1 pair.2)
      (encPair queryEncoding registerEncoding) encBool := by
  have hlt : ComputableInPolyTime
      (fun pair : Query × Registers => decide (pair.2.1.1 < pair.1.2.2))
      (encPair queryEncoding registerEncoding) encBool :=
    .of_tidy (.unary_lt' (by fun_prop) (by fun_prop))
  unfold registerVerdict
  fun_prop


/-- Certified producers supply the unary query indices and source word. The uniform
transition machine charges all captured query data at every one of the reverse scan's steps. -/
theorem scanIncidence_polyTime
    {Input : Type} {inputEncoding : Input ↪ List Bool}
    {varIndex clauseIndex : Input → ℕ} {sign : Input → Bool} {word : Input → List Bool}
    (hvar : ComputableInPolyTime varIndex inputEncoding encUnary)
    (hsign : ComputableInPolyTime sign inputEncoding encBool)
    (hclause : ComputableInPolyTime clauseIndex inputEncoding encUnary)
    (hword : ComputableInPolyTime word inputEncoding encBits) :
    ComputableInPolyTime
      (fun input => scanIncidence (varIndex input) (sign input) (clauseIndex input) (word input))
      inputEncoding encBool := by
  have hquery : ComputableInPolyTime
      (fun input => (varIndex input, sign input, clauseIndex input))
      inputEncoding queryEncoding := hvar.prod (hsign.prod hclause)
  have hreverse : ComputableInPolyTime (fun input => (word input).reverse)
      inputEncoding encBits := ComputableInPolyTime.bitsReverse.comp hword
  have hfold := ComputableTidilyInPolyTime.foldlWith_of_bounded_growth
    (encA := encBool) (encL := encBits)
    (par := fun input => (varIndex input, sign input, clauseIndex input))
    (list := fun input => (word input).reverse)
    (init := fun _ : Input => registers {}) (step := registerStep)
    hquery.tidy hreverse.tidy (ComputableTidilyInPolyTime.const (registers {}))
    registerStep_polyTime.tidy (growth := fun _ => 6) (.const 6)
    (fun input state bit _ => registerStep_growth _ state bit)
  have hdecision := registerVerdict_polyTime.comp
    (hquery.prod (ComputableInPolyTime.of_tidy hfold))
  have heq :
      (fun input => scanIncidence (varIndex input) (sign input) (clauseIndex input) (word input)) =
      (fun input => registerVerdict (varIndex input, sign input, clauseIndex input)
        ((word input).reverse.foldl
          (registerStep (varIndex input, sign input, clauseIndex input)) (registers {}))) := by
    funext input
    rw [registerFold_eq]
    rfl
  rw [heq]
  exact hdecision


/-- One output bit records the complete scanner verdict on every raw source word. -/
def incidenceVerdictWord (varIndex clauseIndex : ℕ) (sign : Bool)
    (input : List Bool) : List Bool := [scanIncidence varIndex sign clauseIndex input]

@[simp] theorem incidenceVerdictWord_eq (varIndex clauseIndex : ℕ) (sign : Bool)
    (input : List Bool) :
    incidenceVerdictWord varIndex clauseIndex sign input =
      [scanIncidence varIndex sign clauseIndex input] := rfl

/-- The single-bit verdict uses the same fully charged native scan. -/
theorem incidenceVerdictWord_polyTime
    {Input : Type} {inputEncoding : Input ↪ List Bool}
    {varIndex clauseIndex : Input → ℕ} {sign : Input → Bool} {word : Input → List Bool}
    (hvar : ComputableInPolyTime varIndex inputEncoding encUnary)
    (hclause : ComputableInPolyTime clauseIndex inputEncoding encUnary)
    (hsign : ComputableInPolyTime sign inputEncoding encBool)
    (hword : ComputableInPolyTime word inputEncoding encBits) :
    ComputableInPolyTime
      (fun input => incidenceVerdictWord (varIndex input) (clauseIndex input) (sign input) (word input))
      inputEncoding encBits :=
  ComputableInPolyTime.bitsCons (scanIncidence_polyTime hvar hsign hclause hword)
    (ComputableInPolyTime.const [])

end GameTheory.Complexity.Backend
