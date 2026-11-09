/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Complexity.Logics.Propositional.CNF
public import Mathlib.Data.List.Basic
public import Mathlib.Data.List.Induction

@[expose] public section

/-! A unary-variable byte format for canonical CSLib CNF formulas.
Data bits are doubled, literal boundaries are 01 and clause boundaries are 10.
Decoding rejects incomplete pairs, empty literals, nonunary variable bodies and
unfinished clauses. Literal and formula semantics are supplied by CSLib.
-/

namespace GameTheory.Complexity.Backend.SATWords

open Cslib.Logic.PL

/-- One sign bit followed by the variable index in unary. -/
def literalBody (literal : Literal ℕ) : List Bool :=
  literal.2 :: List.replicate literal.1 true

/-- Double the literal body and terminate it with the literal separator. -/
def encodeLiteral (literal : Literal ℕ) : List Bool :=
  ((literalBody literal).flatMap fun bit => [bit, bit]) ++ [false, true]

/-- Encode every literal in clause order, including the empty clause. -/
def encodeClause : Clause ℕ → List Bool
  | [] => []
  | literal :: tail => encodeLiteral literal ++ encodeClause tail

/-- Terminate every encoded clause; the empty formula has the empty encoding. -/
def encodeFormula : CNF ℕ → List Bool
  | [] => []
  | clause :: tail => encodeClause clause ++ [true, false] ++ encodeFormula tail

@[simp] theorem encodeClause_nil : encodeClause [] = [] := rfl

@[simp] theorem encodeClause_cons (literal : Literal ℕ) (clause : Clause ℕ) :
    encodeClause (literal :: clause) = encodeLiteral literal ++ encodeClause clause := rfl

@[simp] theorem encodeFormula_nil : encodeFormula [] = [] := rfl

@[simp] theorem encodeFormula_cons (clause : Clause ℕ) (formula : CNF ℕ) :
    encodeFormula (clause :: formula) =
      encodeClause clause ++ [true, false] ++ encodeFormula formula := rfl

theorem encodeClause_append (left right : Clause ℕ) :
    encodeClause (left ++ right) = encodeClause left ++ encodeClause right := by
  induction left with
  | nil => rfl
  | cons literal left ih => simp only [List.cons_append, encodeClause_cons, ih, List.append_assoc]

theorem encodeFormula_append (left right : CNF ℕ) :
    encodeFormula (left ++ right) = encodeFormula left ++ encodeFormula right := by
  induction left with
  | nil => rfl
  | cons clause left ih => simp only [List.cons_append, encodeFormula_cons, ih, List.append_assoc]

@[simp] theorem encodeLiteral_length (literal : Literal ℕ) :
    (encodeLiteral literal).length = 2 * (literal.1 + 1) + 2 := by
  simp [encodeLiteral, literalBody, List.length_flatMap]; omega

theorem clauseCount_le_encodeFormula_length (formula : CNF ℕ) :
    formula.length ≤ (encodeFormula formula).length := by
  induction formula with
  | nil => exact Nat.le_refl _
  | cons clause formula ih =>
    simp only [encodeFormula_cons, List.length_append, List.length_cons, List.length_nil]
    omega

theorem variable_le_encodeClause_length (literal : Literal ℕ) (clause : Clause ℕ)
    (member : literal ∈ clause) : literal.1 ≤ (encodeClause clause).length := by
  induction clause with
  | nil => simp at member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with rfl | member
    · simp only [encodeClause_cons, List.length_append, encodeLiteral_length]
      omega
    · have bound := ih member
      simp only [encodeClause_cons, List.length_append]
      omega

theorem encodeClause_length_le_encodeFormula_length (clause : Clause ℕ) (formula : CNF ℕ)
    (member : clause ∈ formula) : (encodeClause clause).length ≤ (encodeFormula formula).length := by
  induction formula with
  | nil => simp at member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with rfl | member
    · simp only [encodeFormula_cons, List.length_append]
      omega
    · have bound := ih member
      simp only [encodeFormula_cons, List.length_append]
      omega

/-- Unary variable values are bounded by the encoded input, independently of
the binary encoding used by the native typed SAT problem. -/
theorem variable_le_encodeFormula_length (literal : Literal ℕ) (clause : Clause ℕ)
    (formula : CNF ℕ) (inClause : literal ∈ clause) (inFormula : clause ∈ formula) :
    literal.1 ≤ (encodeFormula formula).length :=
  Nat.le_trans (variable_le_encodeClause_length literal clause inClause)
    (encodeClause_length_le_encodeFormula_length clause formula inFormula)

private inductive Token where
  | data (bit : Bool)
  | literalEnd
  | clauseEnd
  deriving DecidableEq, Repr

private def tokenBytes : Token → List Bool
  | .data bit => [bit, bit]
  | .literalEnd => [false, true]
  | .clauseEnd => [true, false]

private def tokenOfPair : Bool → Bool → Token
  | false, false => .data false
  | true, true => .data true
  | false, true => .literalEnd
  | true, false => .clauseEnd

private def encodeTokens (tokens : List Token) : List Bool := tokens.flatMap tokenBytes

private def tokenize? : List Bool → Option (List Token)
  | [] => some []
  | [_] => none
  | false :: false :: tail => (Token.data false :: ·) <$> tokenize? tail
  | true :: true :: tail => (Token.data true :: ·) <$> tokenize? tail
  | false :: true :: tail => (Token.literalEnd :: ·) <$> tokenize? tail
  | true :: false :: tail => (Token.clauseEnd :: ·) <$> tokenize? tail

private theorem tokenize_pair (first second : Bool) (tail : List Bool) :
    tokenize? (first :: second :: tail) =
      (tokenOfPair first second :: ·) <$> tokenize? tail := by
  cases first <;> cases second <;> rfl

private theorem encodeTokens_cons (token : Token) (tokens : List Token) :
    encodeTokens (token :: tokens) = tokenBytes token ++ encodeTokens tokens := by
  cases token <;> rfl

private theorem encodeTokens_append (left right : List Token) :
    encodeTokens (left ++ right) = encodeTokens left ++ encodeTokens right := by
  induction left with
  | nil => rfl
  | cons token left ih => simp [encodeTokens_cons, ih, List.append_assoc]

private theorem tokenize_encodeTokens (tokens : List Token) :
    tokenize? (encodeTokens tokens) = some tokens := by
  induction tokens with
  | nil => rfl
  | cons token tokens ih =>
    cases token with
    | data bit => cases bit <;> simp [encodeTokens_cons, tokenBytes, tokenize?, ih]
    | literalEnd => simp [encodeTokens_cons, tokenBytes, tokenize?, ih]
    | clauseEnd => simp [encodeTokens_cons, tokenBytes, tokenize?, ih]

private theorem tokenize_sound {word : List Bool} {tokens : List Token}
    (decoded : tokenize? word = some tokens) : word = encodeTokens tokens := by
  induction word using List.twoStepInduction generalizing tokens with
  | nil => cases decoded; rfl
  | singleton bit => simp [tokenize?] at decoded
  | cons_cons first second tail ih _ =>
    rw [tokenize_pair] at decoded
    cases parsed : tokenize? tail with
    | none => simp [parsed] at decoded
    | some rest =>
      have recovered : tokenOfPair first second :: rest = tokens := by
        rw [parsed] at decoded
        exact Option.some.inj decoded
      subst tokens
      rw [encodeTokens_cons, ← ih parsed]
      cases first <;> cases second <;> rfl

private def decodeLiteralBody? : List Bool → Option (Literal ℕ)
  | [] => none
  | sign :: body =>
    if ∀ bit ∈ body, bit = true then some (body.length, sign) else none

private theorem decodeLiteralBody_literalBody (literal : Literal ℕ) :
    decodeLiteralBody? (literalBody literal) = some literal := by
  rcases literal with ⟨varIndex, sign⟩
  simp [literalBody, decodeLiteralBody?]

private theorem decodeLiteralBody_sound {body : List Bool} {literal : Literal ℕ}
    (decoded : decodeLiteralBody? body = some literal) : body = literalBody literal := by
  cases body with
  | nil => simp [decodeLiteralBody?] at decoded
  | cons sign body =>
    simp only [decodeLiteralBody?] at decoded
    split at decoded
    · cases decoded
      have unary : body = List.replicate body.length true := by
        rw [List.eq_replicate_length]
        exact fun bit member => ‹∀ bit ∈ body, bit = true› bit member
      exact congrArg (List.cons sign) unary
    · simp at decoded

private def literalTokens (literal : Literal ℕ) : List Token :=
  (literalBody literal).map Token.data

private def clauseTokens : Clause ℕ → List Token
  | [] => []
  | literal :: tail => literalTokens literal ++ Token.literalEnd :: clauseTokens tail

private def formulaTokens : CNF ℕ → List Token
  | [] => []
  | clause :: tail => clauseTokens clause ++ Token.clauseEnd :: formulaTokens tail

private theorem encodeTokens_data (body : List Bool) :
    encodeTokens (body.map Token.data) = body.flatMap (fun bit => [bit, bit]) := by
  induction body with
  | nil => rfl
  | cons bit body ih => cases bit <;> simp [encodeTokens_cons, tokenBytes, ih]

private theorem encodeTokens_clauseTokens (clause : Clause ℕ) :
    encodeTokens (clauseTokens clause) = encodeClause clause := by
  induction clause with
  | nil => rfl
  | cons literal clause ih =>
    simp [clauseTokens, encodeClause, encodeTokens_append, encodeTokens_cons,
      literalTokens, encodeTokens_data, tokenBytes, encodeLiteral, ih]

private theorem encodeTokens_formulaTokens (formula : CNF ℕ) :
    encodeTokens (formulaTokens formula) = encodeFormula formula := by
  induction formula with
  | nil => rfl
  | cons clause formula ih =>
    simp [formulaTokens, encodeFormula, encodeTokens_append, encodeTokens_cons,
      encodeTokens_clauseTokens, tokenBytes, ih, List.append_assoc]

private theorem clauseTokens_append (left right : Clause ℕ) :
    clauseTokens (left ++ right) = clauseTokens left ++ clauseTokens right := by
  induction left with
  | nil => rfl
  | cons literal left ih => simp [clauseTokens, ih, List.append_assoc]

private theorem formulaTokens_append (left right : CNF ℕ) :
    formulaTokens (left ++ right) = formulaTokens left ++ formulaTokens right := by
  induction left with
  | nil => rfl
  | cons clause left ih => simp [formulaTokens, ih, List.append_assoc]

private def parseTokens :
    List Token → List Bool → Clause ℕ → CNF ℕ → Option (CNF ℕ)
  | [], raw, clause, formula =>
    if raw = [] then
      if clause = [] then some formula.reverse else none
    else none
  | .data bit :: tokens, raw, clause, formula =>
    parseTokens tokens (bit :: raw) clause formula
  | .literalEnd :: tokens, raw, clause, formula =>
    match decodeLiteralBody? raw.reverse with
    | some literal => parseTokens tokens [] (literal :: clause) formula
    | none => none
  | .clauseEnd :: tokens, raw, clause, formula =>
    if raw = [] then parseTokens tokens [] [] (clause.reverse :: formula) else none

private theorem parseTokens_data (body : List Bool) (tokens : List Token)
    (raw : List Bool) (clause : Clause ℕ) (formula : CNF ℕ) :
    parseTokens (body.map Token.data ++ tokens) raw clause formula =
      parseTokens tokens (body.reverse ++ raw) clause formula := by
  induction body generalizing raw with
  | nil => simp
  | cons bit body ih =>
    cases bit <;> simp [parseTokens, ih, List.reverse_cons, List.append_assoc]

private theorem parseTokens_clause (clause : Clause ℕ) (tokens : List Token)
    (previous : Clause ℕ) (formula : CNF ℕ) :
    parseTokens (clauseTokens clause ++ Token.clauseEnd :: tokens) [] previous formula =
      parseTokens tokens [] [] ((previous.reverse ++ clause) :: formula) := by
  induction clause generalizing previous with
  | nil => simp [clauseTokens, parseTokens]
  | cons literal clause ih =>
    simp only [clauseTokens, literalTokens, List.append_assoc]
    rw [parseTokens_data]
    simp [parseTokens, decodeLiteralBody_literalBody, ih,
      List.reverse_cons, List.append_assoc]

private theorem parseTokens_formula (formula : CNF ℕ) (tokens : List Token)
    (previous : CNF ℕ) :
    parseTokens (formulaTokens formula ++ tokens) [] [] previous =
      parseTokens tokens [] [] (formula.reverse ++ previous) := by
  induction formula generalizing previous with
  | nil => simp [formulaTokens]
  | cons clause formula ih =>
    simp only [formulaTokens, List.append_assoc, List.cons_append]
    rw [parseTokens_clause]
    simpa [List.reverse_cons, List.append_assoc] using ih (clause :: previous)

private theorem parseTokens_sound {tokens : List Token} {raw : List Bool}
    {clause : Clause ℕ} {previous formula : CNF ℕ}
    (decoded : parseTokens tokens raw clause previous = some formula) :
    formulaTokens previous.reverse ++ clauseTokens clause.reverse ++
      raw.reverse.map Token.data ++ tokens = formulaTokens formula := by
  induction tokens generalizing raw clause previous formula with
  | nil =>
    cases raw <;> cases clause <;> simp [parseTokens, clauseTokens] at decoded ⊢
    cases decoded
    simp
  | cons token tokens ih =>
    cases token with
    | data bit =>
      simp only [parseTokens] at decoded
      simpa [List.reverse_cons, List.append_assoc] using ih decoded
    | literalEnd =>
      cases body : decodeLiteralBody? raw.reverse with
      | none => simp [parseTokens, body] at decoded
      | some literal =>
        simp only [parseTokens, body] at decoded
        have recovered := decodeLiteralBody_sound body
        simpa [recovered, clauseTokens, clauseTokens_append, literalTokens,
          List.reverse_cons, List.append_assoc] using ih decoded
    | clauseEnd =>
      simp only [parseTokens] at decoded
      split at decoded
      · have rawEmpty : raw = [] := by assumption
        simpa [rawEmpty, formulaTokens, formulaTokens_append, clauseTokens,
          List.reverse_cons, List.append_assoc] using ih decoded
      · simp at decoded

/-- Decode the concrete byte format into the canonical native CNF type. -/
def decodeFormula? (input : List Bool) : Option (CNF ℕ) := do
  let tokens ← tokenize? input
  parseTokens tokens [] [] []

@[simp] theorem decodeFormula_encodeFormula (formula : CNF ℕ) :
    decodeFormula? (encodeFormula formula) = some formula := by
  rw [decodeFormula?, ← encodeTokens_formulaTokens, tokenize_encodeTokens]
  simpa [parseTokens] using parseTokens_formula formula [] []

/-- Successful decoding characterizes the exact canonical byte encoding. -/
theorem decodeFormula_sound {input : List Bool} {formula : CNF ℕ}
    (decoded : decodeFormula? input = some formula) : input = encodeFormula formula := by
  unfold decodeFormula? at decoded
  cases tokens : tokenize? input with
  | none => simp [tokens] at decoded
  | some stream =>
    simp only [tokens] at decoded
    have parsed : stream = formulaTokens formula := by
      simpa [formulaTokens, clauseTokens] using parseTokens_sound decoded
    exact (tokenize_sound tokens).trans
      ((congrArg encodeTokens parsed).trans (encodeTokens_formulaTokens formula))

private abbrev Mode := Bool × Bool × Bool

private abbrev rejected : Mode := (true, false, false)

private def nextMode (mode : Mode) (token : Token) : Mode :=
  if mode.1 then rejected else
    match token with
    | .data bit =>
      if mode.2.1 then (if bit then mode else rejected) else (false, true, mode.2.2)
    | .literalEnd => if mode.2.1 then (false, false, true) else rejected
    | .clauseEnd => if mode.2.1 then rejected else (false, false, false)

private def modeAccepts (mode : Mode) : Bool := !mode.1 && !mode.2.1 && !mode.2.2

private def rawValid (raw : List Bool) : Bool := raw.reverse.tail.all id

private def rawMode (raw : List Bool) (clause : Clause ℕ) : Mode :=
  if raw.isEmpty then (false, false, !clause.isEmpty)
  else if rawValid raw then (false, true, !clause.isEmpty) else rejected

private theorem rawValid_cons (bit : Bool) (raw : List Bool) (nonempty : raw ≠ []) :
    rawValid (bit :: raw) = (bit && rawValid raw) := by
  cases reversed : raw.reverse with
  | nil =>
    have empty : raw = [] := by
      simpa only [List.reverse_reverse, List.reverse_nil] using
        congrArg (List.reverse : List Bool → List Bool) reversed
    exact False.elim (nonempty empty)
  | cons sign body =>
    simp only [rawValid, List.reverse_cons, reversed, List.cons_append, List.tail_cons,
      List.all_append, List.all_cons, List.all_nil, id_eq, Bool.and_true]
    exact Bool.and_comm _ _

private theorem decodeLiteralBody_isSome_word (word : List Bool) :
    (decodeLiteralBody? word).isSome = (!word.isEmpty && word.tail.all id) := by
  cases word with
  | nil => rfl
  | cons sign body =>
    change (if ∀ bit ∈ body, bit = true then some (body.length, sign) else none).isSome =
      body.all id
    split_ifs with unary
    · change true = body.all id
      exact (List.all_eq_true.mpr unary).symm
    · change false = body.all id
      cases result : body.all id with
      | false => rfl
      | true => exact False.elim (unary (List.all_eq_true.mp result))

private theorem decodeLiteralBody_isSome (raw : List Bool) :
    (decodeLiteralBody? raw.reverse).isSome = (!raw.isEmpty && rawValid raw) := by
  simpa [rawValid] using decodeLiteralBody_isSome_word raw.reverse

private theorem rawMode_data (bit : Bool) (raw : List Bool) (clause : Clause ℕ) :
    rawMode (bit :: raw) clause = nextMode (rawMode raw clause) (.data bit) := by
  cases raw with
  | nil => simp [rawMode, rawValid, nextMode]
  | cons head tail =>
    have growth := rawValid_cons bit (head :: tail) (by simp)
    cases valid : rawValid (head :: tail) <;> cases bit <;>
      simp [rawMode, nextMode, rejected, valid, growth]

private theorem rawMode_literalEnd (raw : List Bool) (clause : Clause ℕ) :
    nextMode (rawMode raw clause) .literalEnd =
      if (decodeLiteralBody? raw.reverse).isSome then (false, false, true) else rejected := by
  rw [decodeLiteralBody_isSome]
  cases raw with
  | nil => rfl
  | cons head tail =>
    cases valid : rawValid (head :: tail) <;>
      simp [rawMode, nextMode, rejected, valid]

private theorem rawMode_clauseEnd (raw : List Bool) (clause : Clause ℕ) :
    nextMode (rawMode raw clause) .clauseEnd =
      if raw.isEmpty then (false, false, false) else rejected := by
  cases raw with
  | nil => rfl
  | cons head tail =>
    cases valid : rawValid (head :: tail) <;>
      simp [rawMode, nextMode, rejected, valid]

private theorem modeAccepts_rawMode (raw : List Bool) (clause : Clause ℕ) :
    modeAccepts (rawMode raw clause) = (raw.isEmpty && clause.isEmpty) := by
  cases raw with
  | nil => cases clause <;> rfl
  | cons head tail =>
    cases valid : rawValid (head :: tail) <;>
      simp [rawMode, modeAccepts, rejected, valid]

private theorem modeAccepts_fold_rejected (tokens : List Token) :
    modeAccepts (tokens.foldl nextMode rejected) = false := by
  induction tokens with
  | nil => rfl
  | cons token tokens ih =>
    change modeAccepts (tokens.foldl nextMode rejected) = false
    exact ih

private theorem parseTokens_isSome (tokens : List Token) (raw : List Bool)
    (clause : Clause ℕ) (formula : CNF ℕ) :
    (parseTokens tokens raw clause formula).isSome =
      modeAccepts (tokens.foldl nextMode (rawMode raw clause)) := by
  induction tokens generalizing raw clause formula with
  | nil =>
    rw [List.foldl_nil, modeAccepts_rawMode]
    cases raw <;> cases clause <;> rfl
  | cons token tokens ih =>
    cases token with
    | data bit =>
      simp only [parseTokens, List.foldl_cons, ← rawMode_data]
      exact ih (bit :: raw) clause formula
    | literalEnd =>
      rw [List.foldl_cons, rawMode_literalEnd]
      cases decoded : decodeLiteralBody? raw.reverse with
      | none => simpa [parseTokens, decoded] using (modeAccepts_fold_rejected tokens).symm
      | some literal =>
        simpa [parseTokens, decoded, rawMode] using ih [] (literal :: clause) formula
    | clauseEnd =>
      rw [List.foldl_cons, rawMode_clauseEnd]
      cases raw with
      | nil => simpa [parseTokens, rawMode] using ih [] [] (clause.reverse :: formula)
      | cons bit raw => simpa [parseTokens] using (modeAccepts_fold_rejected tokens).symm

private abbrev ScanState := Bool × Bool × (Bool × Bool × Bool)

private def scanStep (state : ScanState) (bit : Bool) : ScanState :=
  if state.1 then
    (false, false, nextMode state.2.2 (tokenOfPair state.2.1 bit))
  else (true, bit, state.2.2)

private abbrev inlineStep (state : ScanState) (bit : Bool) : ScanState :=
  if state.1 then
      (false, false,
        if state.2.2.1 then (true, false, false) else
          if state.2.1 == bit then
            if state.2.2.2.1 then
              (if bit then state.2.2 else (true, false, false))
            else (false, true, state.2.2.2.2)
          else if state.2.1 then
            if state.2.2.2.1 then (true, false, false) else (false, false, false)
          else
            if state.2.2.2.1 then (false, false, true) else (true, false, false))
    else (true, bit, state.2.2)

private theorem inlineStep_eq : inlineStep = scanStep := by
  funext state bit
  rcases state with ⟨waiting, pending, bad, literal, seen⟩
  cases waiting <;> cases pending <;> cases bad <;> cases literal <;> cases seen <;>
    cases bit <;> rfl

private def stateAccepts (state : ScanState) : Bool := !state.1 && modeAccepts state.2.2

/-- Validate the byte grammar with five Boolean registers. The state records an
unfinished bit pair, its first bit, rejection, an open literal and a nonempty
unfinished clause. No variable index or formula is constructed by this scan. -/
def syntaxValid (input : List Bool) : Bool :=
  let final := input.foldl
    (fun (state : Bool × Bool × (Bool × Bool × Bool)) bit =>
      if state.1 then
      (false, false,
        if state.2.2.1 then (true, false, false) else
          if state.2.1 == bit then
            if state.2.2.2.1 then
              (if bit then state.2.2 else (true, false, false))
            else (false, true, state.2.2.2.2)
          else if state.2.1 then
            if state.2.2.2.1 then (true, false, false) else (false, false, false)
          else
            if state.2.2.2.1 then (false, false, true) else (true, false, false))
    else (true, bit, state.2.2))
    (false, false, false, false, false)
  !final.1 && (!final.2.2.1 && !final.2.2.2.1 && !final.2.2.2.2)

private theorem syntaxValid_eq_scan (input : List Bool) :
    syntaxValid input =
      stateAccepts (input.foldl scanStep (false, false, false, false, false)) := by
  change stateAccepts (input.foldl inlineStep (false, false, false, false, false)) = _
  rw [inlineStep_eq]

private theorem scanStep_pair (mode : Mode) (first second : Bool) :
    scanStep (scanStep (false, false, mode) first) second =
      (false, false, nextMode mode (tokenOfPair first second)) := rfl

private theorem scan_tokens (input : List Bool) (mode : Mode) :
    stateAccepts (input.foldl scanStep (false, false, mode)) =
      match tokenize? input with
      | none => false
      | some tokens => modeAccepts (tokens.foldl nextMode mode) := by
  induction input using List.twoStepInduction generalizing mode with
  | nil => rfl
  | singleton bit => rfl
  | cons_cons first second tail ih _ =>
    rw [tokenize_pair]
    simp only [List.foldl_cons]
    rw [scanStep_pair]
    cases parsed : tokenize? tail with
    | none =>
      have smaller := ih (nextMode mode (tokenOfPair first second))
      rw [parsed] at smaller
      exact smaller
    | some tokens =>
      have smaller := ih (nextMode mode (tokenOfPair first second))
      rw [parsed] at smaller
      exact smaller

/-- The finite-state scan accepts precisely the inputs on which canonical native
CNF decoding succeeds, including every malformed and incomplete input. -/
theorem syntaxValid_eq_decodeFormula (input : List Bool) :
    syntaxValid input = (decodeFormula? input).isSome := by
  rw [syntaxValid_eq_scan, scan_tokens]
  unfold decodeFormula?
  cases parsed : tokenize? input with
  | none => rfl
  | some tokens => exact (parseTokens_isSome tokens [] [] []).symm

@[simp] theorem syntaxValid_encodeFormula (formula : CNF ℕ) :
    syntaxValid (encodeFormula formula) = true := by
  rw [syntaxValid_eq_decodeFormula, decodeFormula_encodeFormula]
  rfl

/-- The empty formula and an empty clause have distinct canonical encodings. -/
example : decodeFormula? [] = some [] ∧ decodeFormula? [true, false] = some [[]] := by
  constructor <;> rfl

/-- Odd input, a missing sign, a nonunary variable and an unfinished clause reject. -/
example : decodeFormula? [true] = none ∧
    decodeFormula? [false, true, true, false] = none ∧
    decodeFormula? [true, true, false, false, false, true, true, false] = none ∧
    decodeFormula? [true, true, false, true] = none := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Positive and negative literals use the native variable-first representation. -/
example : decodeFormula? [true, true, false, true, true, false] = some [[(0, true)]] ∧
    decodeFormula? [false, false, false, true, true, false] = some [[(0, false)]] := by
  exact ⟨rfl, rfl⟩


end GameTheory.Complexity.Backend.SATWords
