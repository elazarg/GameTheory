module

public import GameTheoryComplexity.Backend.BinaryCertificateArithmetic
public import GameTheoryComplexity.Backend.WordOperations
public import GameTheoryComplexity.Backend.WordFold
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import GameTheory.Math.FiniteMinimumScan

@[expose] public section

/-! Polynomial-time ordinal lookup in explicit Boolean membership words.
Every scan uses word lengths; no decoded numeric value controls recursion.
-/
namespace GameTheory.Complexity.Backend
open Cslib.BitString Turing.MultiTapeTM
open GameTheory.Complexity.Backend.WordOperations

/-- Count selected positions as a unary word. -/
def binarySubsetTally (word : List Bool) : List Bool :=
  List.replicate (word.count true) true

theorem binarySubsetTally_value (word : List Bool) :
    binarySubsetTally word = List.replicate (word.count true) true := rfl

theorem binarySubsetTally_length (word : List Bool) :
    (binarySubsetTally word).length = word.count true := by
  rw [binarySubsetTally_value, List.length_replicate]

@[fun_prop] theorem binarySubsetTally_polyTime {Input : Type} {input : Input ↪ List Bool}
    {word : Input → List Bool} (hword : ComputableInPolyTime word input encBits) :
    ComputableInPolyTime (fun x => binarySubsetTally (word x)) input encBits := by
  have hcount := ComputableInPolyTime.of_tidy
    (ComputableTidilyInPolyTime.bitsCountWithInput hword.tidy (ComputableTidilyInPolyTime.const true))
  exact ComputableInPolyTime.bitsReplicate true |>.comp hcount

private def nthStep (v : Fin 4 → List Bool) : List Bool :=
  select (andFlag (notFlag (indexedFlag 0 (v 1)))
    (andFlag (indexedFlag (v 0).length (v 2))
      [decide (List.count true ((v 2).take (v 0).length) = (v 3).length)]))
    (true :: v 0) (v 1)

private def nthFoldStep (context : Fin 2 → List Bool)
    (suffix state : List Bool) (_bit : Bool) : List Bool :=
  nthStep ![suffix, state, context 0, context 1]

/-- Lookup the ordinal-th selected position. Inputs are a membership word and an
ordinal ruler. The output has a found header followed by a position ruler. -/
def binarySubsetNth (v : Fin 2 → List Bool) : List Bool :=
  let step : (Fin 2 → List Bool) → List Bool → List Bool → Bool → List Bool :=
    fun (context : Fin 2 → List Bool) (suffix state : List Bool) (_bit : Bool) =>
      select (andFlag (notFlag (indexedFlag 0 state))
        (andFlag (indexedFlag suffix.length (context 0))
          [decide (List.count true ((context 0).take suffix.length) = (context 1).length)]))
        (true :: suffix) state
  WordFold.suffixFold step v [false] (v 0)

private theorem nthStep_length (v : Fin 4 → List Bool) :
    (nthStep v).length ≤ max (v 1).length ((v 0).length + 1) := by
  unfold nthStep
  generalize andFlag _ _ = condition
  cases condition with
  | nil => simp [select]
  | cons b rest =>
    cases b
    · simp [select]
    · simp only [select, List.headD_cons, ↓reduceIte, List.length_cons]
      exact Nat.le_max_right _ _

private theorem nthFold_length (params : Fin 2 → List Bool) (word : List Bool) :
    (WordFold.suffixFold nthFoldStep params [false] word).length ≤ word.length + 1 := by
  induction word with
  | nil => simp [WordFold.suffixFold]
  | cons b word ih =>
    rw [WordFold.suffixFold_cons]
    have hstep := nthStep_length
      ![word, WordFold.suffixFold nthFoldStep params [false] word, params 0, params 1]
    exact hstep.trans (by simp [List.length_cons]; omega)

theorem binarySubsetNth_length (v : Fin 2 → List Bool) :
    (binarySubsetNth v).length ≤ (v 0).length + 1 := by
  change (WordFold.suffixFold nthFoldStep v [false] (v 0)).length ≤ (v 0).length + 1
  exact nthFold_length v (v 0)

private theorem nthStep_polyTime :
    ComputableInPolyTime nthStep (encPi encBits) encBits := by
  have h0 : ComputableInPolyTime (fun v : Fin 4 → List Bool => v 0)
      (encPi encBits) encBits := .pi_apply encBits 0
  have h1 : ComputableInPolyTime (fun v : Fin 4 → List Bool => v 1)
      (encPi encBits) encBits := .pi_apply encBits 1
  have h2 : ComputableInPolyTime (fun v : Fin 4 → List Bool => v 2)
      (encPi encBits) encBits := .pi_apply encBits 2
  have h3 : ComputableInPolyTime (fun v : Fin 4 → List Bool => v 3)
      (encPi encBits) encBits := .pi_apply encBits 3
  have hindex := ComputableInPolyTime.length_bits_comp h0
  have hbit := indexedFlag_polyTime.comp (hindex.prod h2)
  have hfound := indexedFlag_polyTime.comp ((ComputableInPolyTime.const (0 : ℕ)).prod h1)
  have hnotFound := notFlag_polyTime.comp hfound
  have hprefix := take_polyTime.comp (hindex.prod h2)
  have hcount : ComputableInPolyTime
      (fun v : Fin 4 → List Bool => List.count true ((v 2).take (v 0).length))
      (encPi encBits) encUnary :=
    ComputableInPolyTime.bitsCountWithInput hprefix (ComputableInPolyTime.const true)
  have hordinal := ComputableInPolyTime.length_bits_comp h3
  have heqBool : ComputableInPolyTime
      (fun v : Fin 4 → List Bool =>
        decide (List.count true ((v 2).take (v 0).length) = (v 3).length))
      (encPi encBits) encBool := by
    exact ComputableInPolyTime.of_tidy
      ((ComputableTidilyInPolyTime.decide_eq encUnary).comp (hcount.tidy.prod hordinal.tidy))
  have heq := ComputableInPolyTime.bitsCons heqBool (.const [])
  have hinner := andFlag_polyTime.comp (hbit.prod heq)
  have hcondition := andFlag_polyTime.comp (hnotFound.prod hinner)
  have hyes : ComputableInPolyTime (fun v : Fin 4 → List Bool => true :: v 0)
      (encPi encBits) encBits :=
    ComputableInPolyTime.bitsCons (ComputableInPolyTime.const true) h0
  exact select_polyTime.comp (hcondition.prod (hyes.prod h1))

private theorem nthFoldStep_polyTime :
    ComputableInPolyTime
      (fun q : ((Fin 2 → List Bool) × (List Bool × List Bool)) × Bool =>
        nthFoldStep q.1.1 q.1.2.1 q.1.2.2 q.2)
      (encPair (encPair (encPi encBits) (encPair encBits encBits)) encBool) encBits := by
  let encContext : (Fin 2 → List Bool) ↪ List Bool := encPi encBits
  let encMiddle : (Fin 2 → List Bool) × (List Bool × List Bool) ↪ List Bool :=
    encPair encContext (encPair encBits encBits)
  have hmiddle : ComputableInPolyTime
      (fun q : ((Fin 2 → List Bool) × (List Bool × List Bool)) × Bool => q.1)
      (encPair encMiddle encBool) encMiddle := ComputableInPolyTime.fst encMiddle encBool
  have hcontext : ComputableInPolyTime
      (fun q : ((Fin 2 → List Bool) × (List Bool × List Bool)) × Bool => q.1.1)
      (encPair encMiddle encBool) encContext :=
    (ComputableInPolyTime.fst encContext (encPair encBits encBits)).comp hmiddle
  have hcontext' : ComputableInPolyTime
      (fun q : ((Fin 2 → List Bool) × (List Bool × List Bool)) × Bool => q.1.1)
      (encPair encMiddle encBool) (encPi encBits) := by
    simpa [encContext] using hcontext
  have hsuffix : ComputableInPolyTime
      (fun q : ((Fin 2 → List Bool) × (List Bool × List Bool)) × Bool => q.1.2.1)
      (encPair encMiddle encBool) encBits :=
    (ComputableInPolyTime.fst encBits encBits).comp
      ((ComputableInPolyTime.snd encContext (encPair encBits encBits)).comp hmiddle)
  have hstate : ComputableInPolyTime
      (fun q : ((Fin 2 → List Bool) × (List Bool × List Bool)) × Bool => q.1.2.2)
      (encPair encMiddle encBool) encBits :=
    (ComputableInPolyTime.snd encBits encBits).comp
      ((ComputableInPolyTime.snd encContext (encPair encBits encBits)).comp hmiddle)
  have hargs : ComputableInPolyTime
      (fun q : ((Fin 2 → List Bool) × (List Bool × List Bool)) × Bool =>
        ![q.1.2.1, q.1.2.2, q.1.1 0, q.1.1 1])
      (encPair encMiddle encBool) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact hsuffix
    · exact hstate
    · exact (ComputableInPolyTime.pi_apply encBits 0).comp hcontext'
    · exact (ComputableInPolyTime.pi_apply encBits 1).comp hcontext'
  exact nthStep_polyTime.comp hargs

@[fun_prop] theorem binarySubsetNth_polyTime :
    ComputableInPolyTime binarySubsetNth (encPi encBits) encBits := by
  change ComputableInPolyTime
    (fun v : Fin 2 → List Bool => WordFold.suffixFold nthFoldStep v [false] (v 0))
    (encPi encBits) encBits
  have hclock : ComputableInPolyTime (fun v : Fin 2 → List Bool => v 0)
      (encPi encBits) encBits := .pi_apply encBits 0
  have hbound : PolyBounded (fun v : Fin 2 → List Bool => (encPi encBits v).length)
      (fun v => (v 0).length + 1) := hclock.polyBounded_length.add (.const 1)
  exact WordFold.suffixFold_polyTime .id' hclock (.const [false]
    ) nthFoldStep_polyTime hbound (fun v suffix hsub =>
      (nthFold_length v suffix).trans (Nat.add_le_add_right hsub.length_le 1))

private def position (state : List Bool) : Option ℕ :=
  if state.headD false then some state.tail.length else none

/-- Decode the selected position, using the ruler's length. -/
def binarySubsetNthPosition (v : Fin 2 → List Bool) : Option ℕ :=
  if (binarySubsetNth v).headD false then some (binarySubsetNth v).tail.length else none



private theorem nthStep_value (r state word ordinal : List Bool) :
    position (nthStep ![r, state, word, ordinal]) =
      if (word[r.length]?).getD false = true ∧ (word.take r.length).count true = ordinal.length then
        match position state with | none => some r.length | some j => some j
      else position state := by
  unfold nthStep
  cases state with
  | nil =>
    by_cases hb : (word[r.length]?).getD false = true
    · by_cases hc : List.count true (word.take r.length) = ordinal.length
      · simp [select, andFlag, notFlag, indexedFlag, position, hb, hc,
          List.getD_eq_getElem?_getD]
      · simp [select, andFlag, notFlag, indexedFlag, position, hb, hc,
          List.getD_eq_getElem?_getD]
    · by_cases hc : List.count true (word.take r.length) = ordinal.length
      · simp [select, andFlag, notFlag, indexedFlag, position, hb, hc,
          List.getD_eq_getElem?_getD]
      · simp [select, andFlag, notFlag, indexedFlag, position, hb, hc,
          List.getD_eq_getElem?_getD]
  | cons b state =>
    cases b
    · by_cases hb : (word[r.length]?).getD false = true
      · by_cases hc : List.count true (word.take r.length) = ordinal.length
        · simp [select, andFlag, notFlag, indexedFlag, position, hb, hc,
            List.getD_eq_getElem?_getD]
        · simp [select, andFlag, notFlag, indexedFlag, position, hb, hc,
            List.getD_eq_getElem?_getD]
      · by_cases hc : List.count true (word.take r.length) = ordinal.length
        · simp [select, andFlag, notFlag, indexedFlag, position, hb, hc,
            List.getD_eq_getElem?_getD]
        · simp [select, andFlag, notFlag, indexedFlag, position, hb, hc,
            List.getD_eq_getElem?_getD]
    · simp [select, andFlag, notFlag, indexedFlag, position,
        List.getD_eq_getElem?_getD]

/-- Ordinal lookup scans for a selected position with exactly the requested number
of selected predecessors. -/
theorem binarySubsetNth_prefix (v : Fin 2 → List Bool) :
    binarySubsetNthPosition v = GameTheory.Math.FiniteMinimumScan.minimumPrefix
      (fun i => decide ((v 0)[i]?.getD false = true ∧
        ((v 0).take i).count true = (v 1).length)) (fun _ _ => false) (v 0).length := by
  change position (binarySubsetNth v) = _
  change position (WordFold.suffixFold nthFoldStep v [false] (v 0)) = _
  have aux (r word ordinal : List Bool) :
      position (WordFold.suffixFold nthFoldStep ![word, ordinal] [false] r) =
      GameTheory.Math.FiniteMinimumScan.minimumPrefix
        (fun i => decide (word[i]?.getD false = true ∧ (word.take i).count true = ordinal.length))
        (fun _ _ => false) r.length := by
    induction r with
    | nil => rfl
    | cons b r ih =>
      rw [WordFold.suffixFold_cons]
      change position (nthStep ![r,
        WordFold.suffixFold nthFoldStep ![word, ordinal] [false] r, word, ordinal]) = _
      rw [nthStep_value, ih]
      simp only [List.length_cons, GameTheory.Math.FiniteMinimumScan.minimumPrefix,
        decide_eq_true_eq, Bool.false_eq_true, ↓reduceIte]
      rfl
  have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
  rw [hv]
  have h := aux (v 0) (v 0) (v 1)
  simpa [nthFoldStep] using h

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

/-- The parity flag of the number of selected positions. -/
def binarySubsetParity (word : List Bool) : List Bool :=
  [decide (word.count true % 2 = 1)]

theorem binarySubsetParity_value (word : List Bool) :
    binarySubsetParity word = [decide (word.count true % 2 = 1)] := rfl

theorem binarySubsetParity_length (word : List Bool) : (binarySubsetParity word).length = 1 := by
  rw [binarySubsetParity_value]
  rfl

@[fun_prop] theorem binarySubsetParity_polyTime {Input : Type} {input : Input ↪ List Bool}
    {word : Input → List Bool} (hword : ComputableInPolyTime word input encBits) :
    ComputableInPolyTime (fun x => binarySubsetParity (word x)) input encBits := by
  have hcount := ComputableInPolyTime.of_tidy
    (ComputableTidilyInPolyTime.bitsCountWithInput hword.tidy (ComputableTidilyInPolyTime.const true))
  have hmod := ComputableInPolyTime.unary_mod.comp (hcount.prod (.const 2))
  have hflag : ComputableInPolyTime
      (fun x => decide ((word x).count true % 2 = 1)) input encBool :=
    ComputableInPolyTime.of_tidy
      ((ComputableTidilyInPolyTime.decide_eq encUnary).comp (hmod.tidy.prod (.const 1)))
  exact ComputableInPolyTime.bitsCons hflag (.const [])

end GameTheory.Complexity.Backend
