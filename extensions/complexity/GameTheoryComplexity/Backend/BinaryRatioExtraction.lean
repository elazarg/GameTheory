module

public import GameTheoryComplexity.Backend.BinaryWordSubtraction
public import GameTheoryComplexity.Backend.CircuitWords
public import GameTheoryComplexity.Backend.WordFold
public import GameTheoryComplexity.Backend.WordOperations
public import GameTheory.Math.BinaryExtraction

@[expose] public section

/-! Exact binary ratio extraction by bounded word arithmetic.
The precision ruler controls every iteration. A numerator exceeding its denominator
is clipped to the right endpoint, which selects the final binary cell.
A zero denominator retains the total scan: every extracted bit is one.
The exact ratio theorem requires a positive decoded denominator. -/
namespace GameTheory.Complexity.Backend.BinaryRatioExtraction
open Turing.MultiTapeTM WordOperations

private def clipped (num den : List Bool) : List Bool :=
  select (binaryCertificateLE ![num, den]) num den

/-- The paired prefix and residual after a length-controlled scan. -/
def state (num den precision : List Bool) : List Bool :=
  WordFold.suffixFold
    (fun params _ value _ =>
      let doubled := false :: CircuitWords.rest value
      let next := binaryCertificateLE ![params.2, doubled]
      CircuitWords.encodePair (next ++ CircuitWords.first value)
        (select next (binaryWordSub doubled params.2) doubled))
    (num, den) (CircuitWords.encodePair [] (select (binaryCertificateLE ![num, den]) num den)) precision

/-- Little-endian integer identifying the selected binary cell. -/
def prefixWord (num den precision : List Bool) : List Bool := CircuitWords.first (state num den precision)
/-- Unsigned residual numerator with the original denominator. -/
def remainderWord (num den precision : List Bool) : List Bool := CircuitWords.rest (state num den precision)

private theorem state_nil (num den : List Bool) :
    state num den [] = CircuitWords.encodePair [] (clipped num den) := rfl

private theorem clipped_value (num den : List Bool) :
    ofBits (clipped num den) = min (ofBits num) (ofBits den) := by
  rw [clipped, binaryCertificateLE_value]
  by_cases h : ofBits num ≤ ofBits den
  · simp [h, select]
  · simp [h, select, min_eq_right (by omega : ofBits den ≤ ofBits num)]

private theorem select_length (flag x y : List Bool) :
    (select flag x y).length ≤ max x.length y.length := by
  cases flag with
  | nil => exact le_max_right _ _
  | cons b flag => cases b <;> simp [select]

private theorem fields_length (num den precision : List Bool) :
    ∃ p r, state num den precision = CircuitWords.encodePair p r ∧ p.length = precision.length ∧
      r.length ≤ precision.length + num.length + den.length := by
  induction precision with
  | nil =>
    refine ⟨[], clipped num den, rfl, rfl, ?_⟩
    exact (select_length _ _ _).trans (by omega)
  | cons b clock ih =>
    obtain ⟨p, r, hs, hp, hr⟩ := ih
    let doubled := false :: r
    let next := binaryCertificateLE ![den, doubled]
    refine ⟨next ++ p, select next (binaryWordSub doubled den) doubled, ?_, ?_, ?_⟩
    · rw [state, WordFold.suffixFold_cons]
      change CircuitWords.encodePair
        (binaryCertificateLE ![den, false :: CircuitWords.rest (state num den clock)] ++
          CircuitWords.first (state num den clock))
        (select (binaryCertificateLE ![den, false :: CircuitWords.rest (state num den clock)])
          (binaryWordSub (false :: CircuitWords.rest (state num den clock)) den)
          (false :: CircuitWords.rest (state num den clock))) = _
      rw [hs, CircuitWords.first_encodePair, CircuitWords.rest_encodePair]
    · change (binaryCertificateLE ![den, doubled] ++ p).length = _
      rw [List.length_append, binaryCertificateLE_length, hp, List.length_cons]
      omega
    · have hsub := binaryWordSub_length doubled den
      have hsel := select_length next (binaryWordSub doubled den) doubled
      have hd : doubled.length = r.length + 1 := rfl
      simp only [List.length_cons]
      omega

/-- The complete state has a linear bound even for malformed zero denominators. -/
theorem state_length (num den precision : List Bool) :
    (state num den precision).length ≤ 3 * precision.length + num.length + den.length + 2 := by
  obtain ⟨p, r, hs, hp, hr⟩ := fields_length num den precision
  rw [hs, CircuitWords.encodePair_length, hp]
  omega

/-- The output contains exactly one bit per precision-ruler position. -/
theorem prefixWord_length (num den precision : List Bool) :
    (prefixWord num den precision).length = precision.length := by
  obtain ⟨p, r, hs, hp, _⟩ := fields_length num den precision
  simp only [prefixWord, hs, CircuitWords.first_encodePair, hp]

private theorem leFlag_polyTime {α : Type} {enc : α ↪ List Bool}
    {left right : α → List Bool}
    (hl : ComputableInPolyTime left enc encBits)
    (hr : ComputableInPolyTime right enc encBits) :
    ComputableInPolyTime (fun a => binaryCertificateLE ![left a, right a]) enc encBits := by
  have hargs : ComputableInPolyTime (fun a => ![left a, right a]) enc (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact hl
    · exact hr
  exact binaryCertificateLE_polyTime.comp hargs

/-- The complete scan charges its context, every precision bit and all intermediate states. -/
@[fun_prop] theorem state_polyTime {α : Type} {enc : α ↪ List Bool}
    {num den precision : α → List Bool}
    (hn : ComputableInPolyTime num enc encBits)
    (hd : ComputableInPolyTime den enc encBits)
    (hp : ComputableInPolyTime precision enc encBits) :
    ComputableInPolyTime (fun a => state (num a) (den a) (precision a)) enc encBits := by
  have hclipped := select_polyTime.comp ((leFlag_polyTime hn hd).prod (hn.prod hd))
  have hinitial := CircuitWords.encodePair_polyTime.comp
    ((ComputableInPolyTime.const []).prod hclipped)
  let contextEncoding := encPair encBits encBits
  have hstep : ComputableInPolyTime
      (fun p : ((List Bool × List Bool) × (List Bool × List Bool)) × Bool =>
        let doubled := false :: CircuitWords.rest p.1.2.2
        let next := binaryCertificateLE ![p.1.1.2, doubled]
        CircuitWords.encodePair (next ++ CircuitWords.first p.1.2.2)
          (select next (binaryWordSub doubled p.1.1.2) doubled))
      (encPair (encPair contextEncoding (encPair encBits encBits)) encBool) encBits := by
    have houter := ComputableInPolyTime.fst
      (encPair contextEncoding (encPair encBits encBits)) encBool
    have hcontext := (ComputableInPolyTime.fst contextEncoding (encPair encBits encBits)).comp houter
    have hvalue := (ComputableInPolyTime.snd encBits encBits).comp
      ((ComputableInPolyTime.snd contextEncoding (encPair encBits encBits)).comp houter)
    have hden := (ComputableInPolyTime.snd encBits encBits).comp hcontext
    have hdoubled := ComputableInPolyTime.bitsCons (.const false)
      (CircuitWords.rest_polyTime.comp hvalue)
    have hnext := leFlag_polyTime hden hdoubled
    have hprefix := ComputableInPolyTime.bitsAppend hnext
      (CircuitWords.first_polyTime.comp hvalue)
    have hremainder := select_polyTime.comp
      (hnext.prod ((binaryWordSub_polyTime hdoubled hden).prod hdoubled))
    exact CircuitWords.encodePair_polyTime.comp (hprefix.prod hremainder)
  have hbound : PolyBounded (fun a => (enc a).length)
      (fun a => 3 * (precision a).length + (num a).length + (den a).length + 2) :=
    ((((PolyBounded.const 3).mul hp.polyBounded_length).add hn.polyBounded_length).add
      hd.polyBounded_length).add (.const 2)
  apply WordFold.suffixFold_polyTime (hn.prod hd) hp hinitial hstep hbound
  intro a suffix hsuffix
  have h := state_length (num a) (den a) suffix
  have hlength := hsuffix.length_le
  exact h.trans (by omega)

/-- Selecting the extracted cell retains the full native scan certificate. -/
@[fun_prop] theorem prefixWord_polyTime {α : Type} {enc : α ↪ List Bool}
    {num den precision : α → List Bool}
    (hn : ComputableInPolyTime num enc encBits)
    (hd : ComputableInPolyTime den enc encBits)
    (hp : ComputableInPolyTime precision enc encBits) :
    ComputableInPolyTime (fun a => prefixWord (num a) (den a) (precision a)) enc encBits :=
  CircuitWords.first_polyTime.comp (state_polyTime hn hd hp)

/-- Selecting the exact residual retains the full native scan certificate. -/
@[fun_prop] theorem remainderWord_polyTime {α : Type} {enc : α ↪ List Bool}
    {num den precision : α → List Bool}
    (hn : ComputableInPolyTime num enc encBits)
    (hd : ComputableInPolyTime den enc encBits)
    (hp : ComputableInPolyTime precision enc encBits) :
    ComputableInPolyTime (fun a => remainderWord (num a) (den a) (precision a)) enc encBits :=
  CircuitWords.rest_polyTime.comp (state_polyTime hn hd hp)

private theorem state_cons (num den clock : List Bool) (b : Bool) :
    state num den (b :: clock) =
      CircuitWords.encodePair (binaryCertificateLE ![den, false :: remainderWord num den clock] ++
        prefixWord num den clock)
      (select (binaryCertificateLE ![den, false :: remainderWord num den clock])
        (binaryWordSub (false :: remainderWord num den clock) den)
        (false :: remainderWord num den clock)) := by
  rw [state, WordFold.suffixFold_cons]
  rfl

private theorem wordValue_cons (bit : Bool) (word : List Bool) :
    ofBits (bit :: word) = (if bit then 1 else 0) + 2 * ofBits word := by
  cases bit <;> simp [ofBits, Nat.bit_val, Nat.add_comm]

private theorem threshold_ratio (R D : ℕ) (hD : 0 < D) :
    decide (D ≤ 2 * R) = GameTheory.Math.binaryThreshold ((R : ℚ) / D) := by
  unfold GameTheory.Math.binaryThreshold
  congr 1
  apply propext
  have hDq : (0 : ℚ) < D := by exact_mod_cast hD
  rw [le_div_iff₀ hDq]
  constructor
  · intro h
    have hq : (D : ℚ) ≤ 2 * (R : ℚ) := by exact_mod_cast h
    linarith
  · intro h
    have hq : (D : ℚ) ≤ 2 * (R : ℚ) := by linarith
    exact_mod_cast hq

/-- Exact prefix and residual for a clipped ratio with a positive denominator. -/
theorem value (num den precision : List Bool) (hden : 0 < ofBits den) :
    let q : ℚ := (min (ofBits num) (ofBits den) : ℕ) / (ofBits den : ℚ)
    ofBits (prefixWord num den precision) =
      GameTheory.Math.binaryPrefix precision.length q ∧
    (ofBits (remainderWord num den precision) : ℚ) / (ofBits den : ℚ) =
      GameTheory.Math.binaryRemainder precision.length q ∧
    ofBits (remainderWord num den precision) ≤ ofBits den := by
  dsimp only
  induction precision with
  | nil =>
    simp only [prefixWord, remainderWord, state_nil, CircuitWords.first_encodePair, CircuitWords.rest_encodePair,
      clipped_value, List.length_nil, GameTheory.Math.binaryPrefix, GameTheory.Math.binaryRemainder]
    exact ⟨by trivial, by trivial, Nat.min_le_right _ _⟩
  | cons b clock ih =>
    obtain ⟨hp, hr, hbound⟩ := ih
    let R := ofBits (remainderWord num den clock)
    let D := ofBits den
    have hD : (0 : ℚ) < D := by exact_mod_cast hden
    have hbit : decide (D ≤ 2 * R) = GameTheory.Math.binaryThreshold
        (GameTheory.Math.binaryRemainder clock.length
          ((min (ofBits num) D : ℕ) / (D : ℚ))) := by
      rw [threshold_ratio R D hden, hr]
    simp only [prefixWord, remainderWord, state_cons, CircuitWords.first_encodePair, CircuitWords.rest_encodePair]
    rw [binaryCertificateLE_value]
    simp only [wordValue_cons, Bool.false_eq_true, ite_false, zero_add]
    change ofBits ([decide (D ≤ 2 * R)] ++ prefixWord num den clock) = _ ∧
      (ofBits (select [decide (D ≤ 2 * R)]
        (binaryWordSub (false :: remainderWord num den clock) den)
        (false :: remainderWord num den clock)) : ℚ) / D = _ ∧
      ofBits (select [decide (D ≤ 2 * R)]
        (binaryWordSub (false :: remainderWord num den clock) den)
        (false :: remainderWord num den clock)) ≤ D
    by_cases hc : D ≤ 2 * R
    · have htrue : GameTheory.Math.binaryThreshold
          (GameTheory.Math.binaryRemainder clock.length
            ((min (ofBits num) D : ℕ) / (D : ℚ))) = true := by simpa [hc] using hbit.symm
      simp only [hc, decide_true, select, List.headD_cons, ite_true,
        List.singleton_append, wordValue_cons, binaryWordSub_value,
        Bool.false_eq_true, ite_false, zero_add]
      constructor
      · rw [List.length_cons, GameTheory.Math.binaryPrefix, htrue, hp]
        simp [Nat.add_comm]
      · constructor
        · rw [Nat.cast_sub hc, Nat.cast_mul, Nat.cast_ofNat, List.length_cons,
            GameTheory.Math.binaryRemainder, htrue]
          change (2 * (R : ℚ) - D) / D = 2 * _ - 1
          rw [← hr]
          simp [sub_div, mul_div_assoc, hD.ne', R, D]
        · change 2 * R - D ≤ D
          omega
    · have hfalse : GameTheory.Math.binaryThreshold
          (GameTheory.Math.binaryRemainder clock.length
            ((min (ofBits num) D : ℕ) / (D : ℚ))) = false := by simpa [hc] using hbit.symm
      simp only [hc, decide_false, select, List.headD_cons, Bool.false_eq_true, ite_false,
        List.singleton_append, wordValue_cons, zero_add]
      constructor
      · rw [List.length_cons, GameTheory.Math.binaryPrefix, hfalse, hp]
        simp
      · constructor
        · rw [Nat.cast_mul, Nat.cast_ofNat, List.length_cons,
            GameTheory.Math.binaryRemainder, hfalse]
          change (2 * (R : ℚ)) / D = 2 * _ - 0
          rw [← hr]
          ring
        · change 2 * R ≤ D
          omega

/-- The right endpoint and every clipped larger numerator select the final binary cell. -/
theorem prefixWord_endpoint (num den precision : List Bool)
    (hden : 0 < ofBits den) (hclip : ofBits den ≤ ofBits num) :
    ofBits (prefixWord num den precision) = 2 ^ precision.length - 1 := by
  have hn : (ofBits den : ℚ) ≠ 0 := by exact_mod_cast hden.ne'
  simpa only [Nat.min_eq_right hclip, div_self hn, GameTheory.Math.binaryPrefix_one]
    using (value num den precision hden).1

end GameTheory.Complexity.Backend.BinaryRatioExtraction
