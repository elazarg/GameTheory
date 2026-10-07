import Complexitylib.SAT.Encoding

/-! A right-to-left scanner for clause incidence in the concrete unary SAT format.
Its counters enumerate clauses from the final encoded clause toward the first.
Missing padded clauses are tautological, so padding preserves satisfiability.
-/

namespace GameTheory.Complexity.Backend

/-- Registers of the reverse incidence scanner. -/
structure IncidenceState where
  /-- A token's second bit has been saved; its first bit is still pending. -/
  waiting : Bool := false
  /-- Saved second bit of the current two-bit token. -/
  saved : Bool := false
  /-- Current clause number, counted from the end of the formula. -/
  clauseIndex : ℕ := 0
  /-- Unary variable index accumulated within the current literal. -/
  variableCount : ℕ := 0
  /-- Most recently scanned data bit, which becomes the literal's sign. -/
  sign : Bool := false
  /-- Whether the current literal has supplied a data token. -/
  seenData : Bool := false
  /-- Whether the scan has crossed a clause delimiter. -/
  seenClause : Bool := false
  /-- Whether a completed literal matched the queried clause, variable and sign. -/
  hit : Bool := false
  deriving DecidableEq, Repr

/-- Complete the literal whose body and sign have just been scanned in reverse. -/
def IncidenceState.finish (varIndex : ℕ) (sign : Bool) (clause : ℕ)
    (s : IncidenceState) : IncidenceState :=
  { s with hit := s.hit ||
      (s.seenData && decide (s.variableCount = varIndex) &&
        decide (s.sign = sign) && decide (s.clauseIndex = clause)) }

/-- Consume a two-bit token in reverse order. -/
def IncidenceState.token (varIndex : ℕ) (sign : Bool) (clause : ℕ)
    (s : IncidenceState) (first second : Bool) : IncidenceState :=
  match first, second with
  | false, true =>
      { s.finish varIndex sign clause with variableCount := 0, seenData := false }
  | true, false =>
      { s.finish varIndex sign clause with
        clauseIndex := s.clauseIndex + (if s.seenClause then 1 else 0),
        variableCount := 0, seenData := false, seenClause := true }
  | bit, _ =>
      { s with
        variableCount := s.variableCount + (if s.seenData then 1 else 0),
        sign := bit, seenData := true }

/-- Consume one input bit during a reverse scan. -/
def IncidenceState.step (varIndex : ℕ) (sign : Bool) (clause : ℕ)
    (s : IncidenceState) (bit : Bool) : IncidenceState :=
  if s.waiting then
    { s.token varIndex sign clause bit s.saved with waiting := false }
  else
    { s with waiting := true, saved := bit }

/-- Literal occurrence in a reverse-numbered clause, with tautological padding.
Malformed strings are handled by the enclosing reduction's syntax check. -/
def scanIncidence (varIndex : ℕ) (sign : Bool) (clause : ℕ)
    (input : List Bool) : Bool :=
  let s := input.reverse.foldl (IncidenceState.step varIndex sign clause) {}
  let result := s.finish varIndex sign clause
  result.hit || !s.seenClause || decide (s.clauseIndex < clause)

end GameTheory.Complexity.Backend
