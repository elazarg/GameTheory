import GameTheoryComplexity.Backend.BinaryCertificateArithmetic
import GameTheory.Math.FiniteMinimumScan

/-! Polynomial-time ordinal lookup in explicit Boolean membership words.
Every scan uses word lengths; no decoded numeric value controls recursion.
-/
namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham

private def tallyFalse (v : Fin 2 → List Bool) : List Bool := v 1
private def tallyTrue (v : Fin 2 → List Bool) : List Bool := true :: v 1

/-- Count selected positions as a unary word. -/
def binarySubsetTally (word : List Bool) : List Bool :=
  recNotation (fun _ : Fin 0 → List Bool => []) tallyFalse tallyTrue word Fin.elim0

theorem binarySubsetTally_value (word : List Bool) :
    binarySubsetTally word = List.replicate (word.count true) true := by
  induction word with
  | nil => rfl
  | cons b word ih =>
    simp only [binarySubsetTally] at ih ⊢
    cases b <;> simp [recNotation_cons, tallyFalse, tallyTrue, ih, List.replicate_succ]

theorem binarySubsetTally_length (word : List Bool) :
    (binarySubsetTally word).length = word.count true := by
  rw [binarySubsetTally_value, List.length_replicate]

theorem binarySubsetTally_cobham : Cobham fun v : Fin 1 → List Bool => binarySubsetTally (v 0) := by
  have ht : Cobham tallyTrue := Cobham.appendFn (Cobham.const [true]) (.proj 1)
  exact (Cobham.boundedRec (Cobham.const []) (.proj 1) ht (.proj 0)
    (fun r p => by
      have hp : p = Fin.elim0 := by ext i; exact i.elim0
      rw [hp]
      exact (binarySubsetTally_length r).le.trans List.count_le_length)).of_eq fun v => by congr 1; ext i; exact i.elim0

theorem binarySubsetTally_mem_FPn : FPn (fun v : Fin 1 → List Bool => binarySubsetTally (v 0)) :=
  cobham_iff_FPn.mp binarySubsetTally_cobham

private def nthStep (v : Fin 4 → List Bool) : List Bool :=
  caseBit₀ (andBit (notBit (bitAt [] (v 1)))
    (andBit (bitAt (v 0) (v 2))
      (lenEqFlag (binarySubsetTally ((v 2).take (v 0).length)) (v 3))))
    (true :: v 0) (v 1)

/-- Lookup the ordinal-th selected position. Inputs are a membership word and an
ordinal ruler. The output has a found header followed by a position ruler. -/
def binarySubsetNth (v : Fin 2 → List Bool) : List Bool :=
  recNotation (fun _ => [false]) nthStep nthStep (v 0) ![v 0, v 1]

private theorem nthStep_length (v : Fin 4 → List Bool) :
    (nthStep v).length ≤ max (v 1).length ((v 0).length + 1) := by
  unfold nthStep
  generalize andBit _ _ = c
  cases c with
  | nil => simp [caseBit₀]
  | cons b c => cases b <;> simp [caseBit₀]

theorem binarySubsetNth_length (v : Fin 2 → List Bool) :
    (binarySubsetNth v).length ≤ (v 0).length + 1 := by
  have aux (r : List Bool) (p : Fin 2 → List Bool) :
      (recNotation (fun _ => [false]) nthStep nthStep r p).length ≤ r.length + 1 := by
    induction r with
    | nil => simp [recNotation]
    | cons b r ih =>
      simp only [recNotation_cons, Bool.cond_self]
      exact (nthStep_length _).trans (by
        simp only [Fin.cons_zero, Fin.cons_one, List.length_cons]
        exact max_le (ih.trans (by omega)) (by omega))
  exact aux _ _

private theorem nthStep_cobham : Cobham nthStep :=
  Cobham.iteFn (Cobham.andFn
    (Cobham.notFn (Cobham.comp₂ Cobham.bitAtFn (Cobham.const []) (.proj 1)))
    (Cobham.andFn (Cobham.comp₂ Cobham.bitAtFn (.proj 0) (.proj 2))
      (lenEqFlag_mem (Cobham.comp binarySubsetTally_cobham (fun _ =>
        (Cobham.takeFn (.proj 0) (.proj 2)))) (.proj 3))))
    (Cobham.appendFn (Cobham.const [true]) (.proj 0)) (.proj 1)

theorem binarySubsetNth_cobham : Cobham binarySubsetNth := by
  have hscan : Cobham fun v : Fin 3 → List Bool =>
      recNotation (fun _ => [false]) nthStep nthStep (v 0) (Fin.tail v) :=
    Cobham.boundedRec (Cobham.const [false]) nthStep_cobham nthStep_cobham
      (Cobham.appendFn (Cobham.const [true]) (.proj 0)) (fun r p => by
        have aux : (recNotation (fun _ => [false]) nthStep nthStep r p).length ≤ r.length + 1 := by
          induction r with
          | nil => simp [recNotation]
          | cons b r ih =>
            simp only [recNotation_cons, Bool.cond_self]
            exact (nthStep_length _).trans (by
              simp only [Fin.cons_zero, Fin.cons_one, List.length_cons]
              exact max_le (ih.trans (by omega)) (by omega))
        exact aux)
  exact Cobham.comp₃ hscan (.proj 0) (.proj 0) (.proj 1)

theorem binarySubsetNth_mem_FPn : FPn binarySubsetNth := cobham_iff_FPn.mp binarySubsetNth_cobham

private def position (state : List Bool) : Option ℕ :=
  if state.headD false then some state.tail.length else none

/-- Decode the selected position, using the ruler's length. -/
def binarySubsetNthPosition (v : Fin 2 → List Bool) : Option ℕ := position (binarySubsetNth v)

private theorem bitAt_value (r word : List Bool) :
    bitAt r word = [(word[r.length]?).getD false] := by
  simp only [bitAt]
  induction r generalizing word with
  | nil => cases word with
    | nil => rfl
    | cons b word => cases b <;> rfl
  | cons b r ih =>
    cases word with
    | nil => simp [caseBit₀]
    | cons c word => simpa only [List.length_cons, List.drop_succ_cons,
        List.getElem?_cons_succ] using ih word

private theorem lenEqFlag_value (x y : List Bool) : lenEqFlag x y = [decide (x.length = y.length)] := by
  rcases lenEqFlag_flag x y with h | h
  · rw [h]
    simp [(lenEqFlag_eq_true_iff x y).mp h]
  · rw [h]
    have hn : x.length ≠ y.length := by
      intro he
      have := (lenEqFlag_eq_true_iff x y).mpr he
      simp [h] at this
    simp [hn]

private theorem nthStep_value (r state word ordinal : List Bool) :
    position (nthStep ![r, state, word, ordinal]) =
      if (word[r.length]?).getD false = true ∧ (word.take r.length).count true = ordinal.length then
        match position state with | none => some r.length | some j => some j
      else position state := by
  unfold nthStep
  change position (caseBit₀ (andBit (notBit (bitAt [] state))
    (andBit (bitAt r word)
      (lenEqFlag (binarySubsetTally (word.take r.length)) ordinal))) (true :: r) state) = _
  rw [bitAt_value r word, lenEqFlag_value, binarySubsetTally_length]
  cases state with
  | nil =>
    cases hb : (word[r.length]?).getD false <;>
      by_cases hc : (word.take r.length).count true = ordinal.length <;>
      simp [hc, position, bitAt, notBit, andBit, caseBit₀]
  | cons b state =>
    cases b
    · cases hb : (word[r.length]?).getD false <;>
        by_cases hc : (word.take r.length).count true = ordinal.length <;>
        simp [hc, position, bitAt, notBit, andBit, caseBit₀]
    · by_cases h : (word[r.length]?).getD false = true ∧
          (word.take r.length).count true = ordinal.length <;>
        simp [h, position, bitAt, notBit, andBit, caseBit₀]

/-- Ordinal lookup scans for a selected position with exactly the requested number
of selected predecessors. -/
theorem binarySubsetNth_prefix (v : Fin 2 → List Bool) :
    binarySubsetNthPosition v = GameTheory.Math.FiniteMinimumScan.minimumPrefix
      (fun i => decide ((v 0)[i]?.getD false = true ∧
        ((v 0).take i).count true = (v 1).length)) (fun _ _ => false) (v 0).length := by
  have aux (r word ordinal : List Bool) :
      position (recNotation (fun _ => [false]) nthStep nthStep r ![word, ordinal]) =
      GameTheory.Math.FiniteMinimumScan.minimumPrefix
        (fun i => decide (word[i]?.getD false = true ∧ (word.take i).count true = ordinal.length))
        (fun _ _ => false) r.length := by
    induction r with
    | nil => rfl
    | cons b r ih =>
      simp only [recNotation_cons, Bool.cond_self]
      change position (nthStep ![r,
        recNotation (fun _ => [false]) nthStep nthStep r ![word, ordinal], word, ordinal]) = _
      rw [nthStep_value, ih]
      simp only [List.length_cons, GameTheory.Math.FiniteMinimumScan.minimumPrefix,
        decide_eq_true_eq, Bool.false_eq_true, ↓reduceIte]
      rfl
  exact aux _ _ _

private theorem count_take_strict (word : List Bool) (i j : ℕ) (hij : i < j)
    (hb : word[i]?.getD false = true) :
    (word.take i).count true < (word.take j).count true := by
  have hbit : word[i]? = some true := by
    cases ho : word[i]? with
    | none => simp [ho] at hb
    | some b => cases b <;> simp_all
  have hstep : (word.take (i + 1)).count true = (word.take i).count true + 1 := by
    simp [List.take_add_one, List.count_append, hbit]
  have hsub : (word.take (i + 1)).Sublist (word.take j) := by
    have := List.take_sublist (i + 1) (word.take j)
    simpa only [List.take_take, Nat.min_eq_left (by omega : i + 1 ≤ j)] using this
  have hm := hsub.count_le true
  omega

private theorem selected_unique (word : List Bool) (ordinal i j : ℕ)
    (hi : word[i]?.getD false = true ∧ (word.take i).count true = ordinal)
    (hj : word[j]?.getD false = true ∧ (word.take j).count true = ordinal) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · have := count_take_strict word i j h hi.1
    omega
  · exact h
  · have := count_take_strict word j i h hj.1
    omega

/-- The returned position is precisely the ordinal-th true bit in increasing order. -/
theorem binarySubsetNth_value (v : Fin 2 → List Bool) (i : ℕ) :
    binarySubsetNthPosition v = some i ↔ i < (v 0).length ∧
      (v 0)[i]?.getD false = true ∧ ((v 0).take i).count true = (v 1).length := by
  rw [binarySubsetNth_prefix]
  constructor
  · intro hs
    have hm := GameTheory.Math.FiniteMinimumScan.minimumPrefix_mem _ _ _ _ hs
    exact ⟨hm.1, of_decide_eq_true hm.2⟩
  · rintro ⟨hi, hb⟩
    cases hs : GameTheory.Math.FiniteMinimumScan.minimumPrefix
      (fun j => decide ((v 0)[j]?.getD false = true ∧
        ((v 0).take j).count true = (v 1).length)) (fun _ _ => false) (v 0).length with
    | none =>
      have hn := (GameTheory.Math.FiniteMinimumScan.minimumPrefix_none _ _ _).mp hs i hi
      simp [hb] at hn
    | some j =>
      have hm := GameTheory.Math.FiniteMinimumScan.minimumPrefix_mem _ _ _ _ hs
      have hji := selected_unique (v 0) (v 1).length j i (of_decide_eq_true hm.2) hb
      exact congrArg some hji

private theorem exists_selected (word : List Bool) (k : ℕ) (hk : k < word.count true) :
    ∃ i < word.length, word[i]?.getD false = true ∧ (word.take i).count true = k := by
  induction word generalizing k with
  | nil => simp at hk
  | cons b word ih =>
    cases b
    · have hk' : k < word.count true := by simpa using hk
      obtain ⟨i, hi, hb, hc⟩ := ih k hk'
      exact ⟨i + 1, by simp; omega, by simpa, by simpa using hc⟩
    · cases k with
      | zero => exact ⟨0, by simp, by simp, by simp⟩
      | succ k =>
        have hk' : k < word.count true := by simpa using hk
        obtain ⟨i, hi, hb, hc⟩ := ih k hk'
        exact ⟨i + 1, by simp; omega, by simpa, by simpa using hc⟩

/-- Lookup fails exactly when the requested ordinal is outside the selected positions. -/
theorem binarySubsetNth_none (v : Fin 2 → List Bool) :
    binarySubsetNthPosition v = none ↔ (v 0).count true ≤ (v 1).length := by
  rw [binarySubsetNth_prefix, GameTheory.Math.FiniteMinimumScan.minimumPrefix_none]
  constructor
  · intro hn
    by_contra h
    obtain ⟨i, hi, hb⟩ := exists_selected (v 0) (v 1).length (by omega)
    have := hn i hi
    simp [hb] at this
  · intro h i hi
    apply decide_eq_false
    rintro ⟨hb, hc⟩
    have hs := count_take_strict (v 0) i (v 0).length hi hb
    simp only [List.take_length] at hs
    omega

private def parityTrue (v : Fin 2 → List Bool) : List Bool := notBit (v 1)

/-- The parity flag of the number of selected positions. -/
def binarySubsetParity (word : List Bool) : List Bool :=
  recNotation (fun _ : Fin 0 → List Bool => [false]) tallyFalse parityTrue word Fin.elim0

theorem binarySubsetParity_value (word : List Bool) :
    binarySubsetParity word = [decide (word.count true % 2 = 1)] := by
  induction word with
  | nil => rfl
  | cons b word ih =>
    simp only [binarySubsetParity] at ih ⊢
    cases b
    · simpa [recNotation_cons, tallyFalse] using ih
    · simp only [recNotation_cons, parityTrue, Fin.cons_one, Bool.cond_true, ih]
      have hcount : (true :: word).count true = word.count true + 1 := by simp
      rw [hcount]
      have hm : word.count true % 2 < 2 := Nat.mod_lt _ (by omega)
      by_cases ho : word.count true % 2 = 1
      · have he : (word.count true + 1) % 2 ≠ 1 := by omega
        simp [ho, he, notBit, caseBit₀]
      · have he : (word.count true + 1) % 2 = 1 := by omega
        simp [ho, he, notBit, caseBit₀]

theorem binarySubsetParity_length (word : List Bool) : (binarySubsetParity word).length = 1 := by
  rw [binarySubsetParity_value]
  rfl

theorem binarySubsetParity_cobham : Cobham fun v : Fin 1 → List Bool => binarySubsetParity (v 0) := by
  have ht : Cobham parityTrue := Cobham.notFn (.proj 1)
  exact (Cobham.boundedRec (Cobham.const [false]) (.proj 1) ht (Cobham.const [false])
    (fun r p => by
      have hp : p = Fin.elim0 := by ext i; exact i.elim0
      rw [hp]
      exact (binarySubsetParity_length r).le)).of_eq fun v => by
        congr 1
        ext i
        exact i.elim0

theorem binarySubsetParity_mem_FPn : FPn (fun v : Fin 1 → List Bool => binarySubsetParity (v 0)) :=
  cobham_iff_FPn.mp binarySubsetParity_cobham

end GameTheory.Complexity.Backend
