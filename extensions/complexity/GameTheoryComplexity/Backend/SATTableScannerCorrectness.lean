import GameTheoryComplexity.Backend.SATTableScanner
import GameTheoryComplexity.Backend.SATGame

/-! Correctness of the reverse incidence scanner on the concrete SAT encoding. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity.SAT

private def runBits (varIndex : ℕ) (sign : Bool) (clause : ℕ)
    (s : IncidenceState) (input : List Bool) : IncidenceState :=
  input.reverse.foldl (IncidenceState.step varIndex sign clause) s

private theorem runBits_append (v : ℕ) (b : Bool) (k : ℕ)
    (s : IncidenceState) (xs ys : List Bool) :
    runBits v b k s (xs ++ ys) = runBits v b k (runBits v b k s ys) xs := by
  simp [runBits, List.reverse_append, List.foldl_append]

private theorem runBits_pair (v : ℕ) (b : Bool) (k : ℕ)
    (s : IncidenceState) (first second : Bool) (hw : s.waiting = false) :
    runBits v b k s [first, second] =
      { s.token v b k first second with waiting := false, saved := second } := by
  cases first <;> cases second <;>
    simp [runBits, IncidenceState.step, IncidenceState.token, IncidenceState.finish, hw]

private theorem doubleBits_append (xs ys : List Bool) :
    doubleBits (xs ++ ys) = doubleBits xs ++ doubleBits ys := by
  simp [doubleBits]

private theorem runBits_raw (v : ℕ) (b : Bool) (k : ℕ)
    (literalSign : Bool) (literalVar : ℕ) (s : IncidenceState) (hw : s.waiting = false) :
    runBits v b k s (doubleBits (literalSign :: List.replicate literalVar true)) =
      { s with
        waiting := false
        saved := literalSign
        variableCount := s.variableCount + literalVar + (if s.seenData then 1 else 0)
        sign := literalSign
        seenData := true } := by
  induction literalVar generalizing s with
  | zero =>
      simp only [List.replicate_zero, doubleBits_cons, doubleBits_nil]
      rw [runBits_pair v b k s literalSign literalSign hw]
      cases literalSign <;> simp [IncidenceState.token]
  | succ n ih =>
      have heq : literalSign :: List.replicate (n + 1) true =
          (literalSign :: List.replicate n true) ++ [true] := by
        rw [List.replicate_add]
        simp
      rw [heq, doubleBits_append, runBits_append]
      rw [show doubleBits [true] = [true, true] from rfl]
      rw [runBits_pair v b k s true true hw]
      simp only [IncidenceState.token]
      rw [ih _ rfl]
      congr 1
      dsimp
      omega

private def occurs (v : ℕ) (b : Bool) (c : Clause) : Bool :=
  c.any fun lit => decide (lit.var = v) && decide (lit.sign = b)

private theorem runBits_clause (v : ℕ) (b : Bool) (k : ℕ)
    (c : Clause) (s : IncidenceState) (hw : s.waiting = false)
    (hd : s.seenData = false) :
    (runBits v b k s c.encode).waiting = false ∧
    (runBits v b k s c.encode).clauseIndex = s.clauseIndex ∧
    (runBits v b k s c.encode).seenClause = s.seenClause ∧
    ((runBits v b k s c.encode).finish v b k).hit =
      (s.hit || (decide (s.clauseIndex = k) && occurs v b c)) := by
  induction c generalizing s with
  | nil => simp [Clause.encode, runBits, IncidenceState.finish, occurs, hw, hd]
  | cons lit tail ih =>
      have ht := ih s hw hd
      simp only [Clause.encode_cons, runBits_append]
      rw [runBits_pair v b k _ false true ht.1]
      simp only [Lit.encodeRaw, Unary.encode]
      rw [runBits_raw v b k lit.sign lit.var _ rfl]
      simp only [IncidenceState.token]
      dsimp
      simp only [ht.2.1, ht.2.2.1, Nat.zero_add,
        IncidenceState.finish, Bool.true_and]
      have hh := ht.2.2.2
      simp only [IncidenceState.finish, ht.2.1] at hh
      simp only [occurs, List.any_cons] at *
      grind

private def hitFor (v : ℕ) (b : Bool) (k : ℕ) (φ : CNF) : Bool :=
  match φ.reverse[k]? with
  | some c => occurs v b c
  | none => false

private theorem hitFor_cons (v : ℕ) (b : Bool) (k : ℕ) (c : Clause) (tail : CNF) :
    hitFor v b k (c :: tail) =
      (hitFor v b k tail || (decide (tail.length = k) && occurs v b c)) := by
  by_cases h : k < tail.length
  · simp [hitFor, List.reverse_cons, List.getElem?_append, h, ne_of_gt h]
  · by_cases heq : k = tail.length
    · subst k
      simp [hitFor, List.reverse_cons]
    · have hsingle : [c][k - tail.length]? = none :=
        List.getElem?_eq_none (by simp; omega)
      simp [hitFor, List.reverse_cons, List.getElem?_append, h, Ne.symm heq, hsingle]

private theorem runBits_cnf (v : ℕ) (b : Bool) (k : ℕ) (φ : CNF) :
    (runBits v b k {} φ.encode).waiting = false ∧
    (runBits v b k {} φ.encode).clauseIndex = φ.length - 1 ∧
    (runBits v b k {} φ.encode).seenClause = decide (φ ≠ []) ∧
    ((runBits v b k {} φ.encode).finish v b k).hit = hitFor v b k φ := by
  induction φ with
  | nil => simp [CNF.encode, runBits, IncidenceState.finish, hitFor]
  | cons c tail ih =>
      let t := runBits v b k {} (CNF.encode tail)
      have ht : t.waiting = false := ih.1
      have hx : t.clauseIndex + (if t.seenClause then 1 else 0) = tail.length := by
        rw [show t.clauseIndex = tail.length - 1 from ih.2.1,
          show t.seenClause = decide (tail ≠ []) from ih.2.2.1]
        cases tail <;> simp
      let r : IncidenceState :=
        { t.token v b k true false with waiting := false, saved := false }
      have hrIndex : r.clauseIndex = tail.length := hx
      have hrHit : r.hit = (t.finish v b k).hit := rfl
      have hc := runBits_clause v b k c r rfl rfl
      simp only [CNF.encode_cons, runBits_append]
      rw [runBits_pair v b k t true false ht]
      change (runBits v b k r c.encode).waiting = false ∧
        (runBits v b k r c.encode).clauseIndex = (c :: tail).length - 1 ∧
        (runBits v b k r c.encode).seenClause = decide (c :: tail ≠ []) ∧
        ((runBits v b k r c.encode).finish v b k).hit = hitFor v b k (c :: tail)
      refine ⟨hc.1, ?_, ?_, ?_⟩
      · simpa only [List.length_cons, Nat.add_sub_cancel] using hc.2.1.trans hrIndex
      · exact hc.2.2.1
      · rw [hc.2.2.2, hrHit, hrIndex,
          show (t.finish v b k).hit = hitFor v b k tail from ih.2.2.2,
          hitFor_cons]

/-- The reverse scanner computes literal occurrence, with tautological absent clauses. -/
theorem scanIncidence_encode (v : ℕ) (b : Bool) (k : ℕ) (φ : CNF) :
    scanIncidence v b k φ.encode =
      match φ.reverse[k]? with
      | some c => c.any fun lit => lit.var == v && lit.sign == b
      | none => true := by
  have h := runBits_cnf v b k φ
  change (((runBits v b k {} φ.encode).finish v b k).hit ||
      !(runBits v b k {} φ.encode).seenClause ||
      decide ((runBits v b k {} φ.encode).clauseIndex < k)) = _
  rw [h.2.2.2, h.2.2.1, h.2.1]
  cases hg : φ.reverse[k]? with
  | none =>
      have hk : φ.length ≤ k := by
        simpa only [List.length_reverse] using List.getElem?_eq_none_iff.mp hg
      simp only [hitFor, hg]
      rw [Bool.eq_iff_iff]
      cases φ with
      | nil => simp
      | cons c cs =>
          simp only [List.length_cons] at hk
          simp
          omega
  | some c =>
      have hk : k < φ.length := by
        have hne : φ.reverse[k]? ≠ none := by simp [hg]
        have hlt := List.getElem?_eq_none_iff.not.mp hne
        simp only [List.length_reverse] at hlt
        omega
      have hnonempty : φ ≠ [] := by intro heq; simp [heq] at hk
      have hnlt : ¬φ.length - 1 < k := by omega
      simp only [hitFor, hg]
      rw [Bool.eq_iff_iff]
      simp [hnonempty, hnlt, occurs, List.any_eq_true]

/-- On valid encodings the executable scanner agrees with the semantic game incidence. -/
theorem scanIncidence_eq_satIncidence (input : List Bool) (φ : CNF)
    (hdecode : CNF.decode? input = some φ)
    (c v : Fin (input.length + 1)) (b : Bool) :
    scanIncidence v.val b c.val input = satIncidence input c v b := by
  have hinput := CNF.decode?_sound hdecode
  simp only [satIncidence, hdecode, paddedSATIncidence]
  exact (congrArg (scanIncidence v.val b c.val) hinput).trans
    (scanIncidence_encode v.val b c.val φ)

end GameTheory.Complexity.Backend
