module

public import GameTheoryComplexity.Backend.BrouwerNashHeaders
public import GameTheoryComplexity.Backend.BinaryUnaryArithmetic
public import GameTheoryComplexity.Backend.WordOperations

@[expose] public section

/-! Comparator-kind flags identify alternating extraction digits and every ripple
increment in each sample. Actual source and output words are retained; only their
ruler lengths determine these singleton flags. -/
namespace GameTheory.Complexity.Backend.BrouwerNashSampleKind
open Turing.MultiTapeTM
open WordOperations

/-- One sample uses comparators for even extraction slots and all increment slots. -/
def sampleFlag (source code₀ code₁ ordinal out : List Bool) : List Bool :=
  let depth := (BrouwerNashHeaders.sourceDepthRuler source).length
  let base := (BrouwerNashHeaders.globalRuler source).length +
    ordinal.length * (BrouwerNashHeaders.sampleRuler source code₀ code₁).length
  [decide ((base + 2 ≤ out.length ∧ out.length < base + 2 + 4 * depth ∧
    (out.length - base) % 2 ≠ 1) ∨
    (base + 2 + 4 * depth ≤ out.length ∧ out.length < base + 2 + 12 * depth))]

private def collect (n : ℕ) (source code₀ code₁ out : List Bool) : List Bool :=
  (List.range n).foldl (fun flag i =>
    orFlag flag (sampleFlag source code₀ code₁ (List.replicate i false) out)) [false]

private theorem collect_succ (n : ℕ) (source code₀ code₁ out : List Bool) :
    collect (n + 1) source code₀ code₁ out =
      orFlag (collect n source code₀ code₁ out)
        (sampleFlag source code₀ code₁ (List.replicate n false) out) := by
  simp only [collect, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- Combine the forty-one original false ordinal rulers in ascending OR order. -/
def kindWord (source code₀ code₁ out : List Bool) : List Bool :=
  (List.range 41).foldl (fun flag i =>
    orFlag flag (sampleFlag source code₀ code₁ (List.replicate i false) out)) [false]

private theorem kindWord_eq (source code₀ code₁ out : List Bool) :
    kindWord source code₀ code₁ out = collect 41 source code₀ code₁ out := rfl

@[fun_prop] theorem sampleFlag_polyTime {Input : Type} {input : Input ↪ List Bool}
    {source code₀ code₁ ordinal out : Input → List Bool}
    (hs : ComputableInPolyTime source input encBits)
    (hc₀ : ComputableInPolyTime code₀ input encBits)
    (hc₁ : ComputableInPolyTime code₁ input encBits)
    (ht : ComputableInPolyTime ordinal input encBits)
    (ho : ComputableInPolyTime out input encBits) :
    ComputableInPolyTime (fun a => sampleFlag (source a) (code₀ a) (code₁ a)
      (ordinal a) (out a)) input encBits := by
  have hdepth := ComputableInPolyTime.length_bits_comp (BrouwerNashHeaders.sourceDepthRuler_polyTime hs)
  have hbase := ComputableInPolyTime.unary_add'
    (ComputableInPolyTime.length_bits_comp (BrouwerNashHeaders.globalRuler_polyTime hs))
    (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.length_bits_comp ht)
      (ComputableInPolyTime.length_bits_comp (BrouwerNashHeaders.sampleRuler_polyTime hs hc₀ hc₁)))
  have hout := ComputableInPolyTime.length_bits_comp ho
  have hfirst := ComputableInPolyTime.unary_add' hbase (ComputableInPolyTime.const 2)
  have hmiddle := ComputableInPolyTime.unary_add' hfirst
    (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 4) hdepth)
  have hlast := ComputableInPolyTime.unary_add' hfirst
    (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 12) hdepth)
  have hmod := ComputableInPolyTime.unary_mod.comp
    ((ComputableInPolyTime.unary_sub' hout hbase).prod (ComputableInPolyTime.const 2))
  have heven := ComputableInPolyTime.bool_not.comp (hmod.decide_eq' (ComputableInPolyTime.const 1))
  have heven' : ComputableInPolyTime (fun a : Input => decide
      (((out a).length - ((BrouwerNashHeaders.globalRuler (source a)).length +
        (ordinal a).length * (BrouwerNashHeaders.sampleRuler (source a) (code₀ a) (code₁ a)).length)) % 2 ≠ 1))
      input encBool :=
    heven.of_enc_eq (fun a => by simp only [Function.comp_apply, decide_not])
  have hgeFirst := ComputableInPolyTime.of_tidy
    (ComputableTidilyInPolyTime.unary_le' hfirst.tidy hout.tidy)
  have hltMiddle := ComputableInPolyTime.of_tidy
    (ComputableTidilyInPolyTime.unary_lt' hout.tidy hmiddle.tidy)
  have hgeMiddle := ComputableInPolyTime.of_tidy
    (ComputableTidilyInPolyTime.unary_le' hmiddle.tidy hout.tidy)
  have hltLast := ComputableInPolyTime.of_tidy
    (ComputableTidilyInPolyTime.unary_lt' hout.tidy hlast.tidy)
  have hdigit := ComputableInPolyTime.decide_and hgeFirst
    (ComputableInPolyTime.decide_and hltMiddle heven')
  have hincrement := ComputableInPolyTime.decide_and hgeMiddle hltLast
  exact ComputableInPolyTime.bitsCons (ComputableInPolyTime.decide_or hdigit hincrement)
    (ComputableInPolyTime.const [])

private theorem collect_polyTime (n : ℕ) {Input : Type} {input : Input ↪ List Bool}
    {source code₀ code₁ out : Input → List Bool}
    (hs : ComputableInPolyTime source input encBits)
    (hc₀ : ComputableInPolyTime code₀ input encBits)
    (hc₁ : ComputableInPolyTime code₁ input encBits)
    (ho : ComputableInPolyTime out input encBits) :
    ComputableInPolyTime (fun a => collect n (source a) (code₀ a) (code₁ a) (out a)) input encBits := by
  induction n with
  | zero => exact ComputableInPolyTime.const [false]
  | succ n ih =>
    have hflag := sampleFlag_polyTime hs hc₀ hc₁ (ComputableInPolyTime.const (List.replicate n false)) ho
    exact (orFlag_polyTime.comp (ih.prod hflag)).of_enc_eq (fun a => by
      simp only [collect_succ, Function.comp_apply])

/-- The comparator-kind producer charges source, code words and the original output ruler. -/
@[fun_prop] theorem kindWord_polyTime {Input : Type} {input : Input ↪ List Bool}
    {source code₀ code₁ out : Input → List Bool}
    (hs : ComputableInPolyTime source input encBits)
    (hc₀ : ComputableInPolyTime code₀ input encBits)
    (hc₁ : ComputableInPolyTime code₁ input encBits)
    (ho : ComputableInPolyTime out input encBits) :
    ComputableInPolyTime (fun a => kindWord (source a) (code₀ a) (code₁ a) (out a)) input encBits :=
  collect_polyTime 41 hs hc₀ hc₁ ho

/-- Each sample flag has the original total interval-and-parity interpretation. -/
theorem sampleFlag_value (t out source code₀ code₁ : List Bool) :
    sampleFlag source code₀ code₁ t out =
      [decide (
        (BrouwerNashLayout.globalCount (CircuitWords.first source).length + t.length *
          BrouwerNashLayout.sampleWidth (CircuitWords.first source).length
            (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length + 2 ≤ out.length ∧
        out.length < BrouwerNashLayout.globalCount (CircuitWords.first source).length + t.length *
          BrouwerNashLayout.sampleWidth (CircuitWords.first source).length
            (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length +
          2 + 4 * (CircuitWords.first source).length ∧
        (out.length - (BrouwerNashLayout.globalCount (CircuitWords.first source).length + t.length *
          BrouwerNashLayout.sampleWidth (CircuitWords.first source).length
            (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length)) % 2 ≠ 1) ∨
        (BrouwerNashLayout.globalCount (CircuitWords.first source).length + t.length *
          BrouwerNashLayout.sampleWidth (CircuitWords.first source).length
            (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length +
          2 + 4 * (CircuitWords.first source).length ≤ out.length ∧
        out.length < BrouwerNashLayout.globalCount (CircuitWords.first source).length + t.length *
          BrouwerNashLayout.sampleWidth (CircuitWords.first source).length
            (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length +
          2 + 12 * (CircuitWords.first source).length))] := by
  simp only [sampleFlag, BrouwerNashHeaders.sourceDepthRuler_length,
    BrouwerNashHeaders.globalRuler_length, BrouwerNashHeaders.sampleRuler_length]

private theorem sampleFlag_flag (source code₀ code₁ ordinal out : List Bool) :
    ∃ b : Bool, sampleFlag source code₀ code₁ ordinal out = [b] := by
  dsimp only [sampleFlag]
  exact ⟨_, rfl⟩

private theorem collect_value (n : ℕ) (source code₀ code₁ out : List Bool) :
    collect n source code₀ code₁ out =
      [decide (∃ i < n, sampleFlag source code₀ code₁ (List.replicate i false) out = [true])] := by
  induction n with
  | zero => simp [collect]
  | succ n ih =>
    rw [collect_succ, ih]
    rcases sampleFlag_flag source code₀ code₁ (List.replicate n false) out with ⟨b, hb⟩
    rw [hb]
    have hs : (∃ i < n + 1, sampleFlag source code₀ code₁ (List.replicate i false) out = [true]) ↔
        (∃ i < n, sampleFlag source code₀ code₁ (List.replicate i false) out = [true]) ∨
          sampleFlag source code₀ code₁ (List.replicate n false) out = [true] := by
      constructor
      · rintro ⟨i, hi, ht⟩
        by_cases hin : i < n
        · exact Or.inl ⟨i, hin, ht⟩
        · have he : i = n := by omega
          subst i
          exact Or.inr ht
      · rintro (⟨i, hi, ht⟩ | ht)
        · exact ⟨i, by omega, ht⟩
        · exact ⟨n, by omega, ht⟩
    simp only [hs, hb]
    by_cases he : ∃ i < n, sampleFlag source code₀ code₁ (List.replicate i false) out = [true]
    · cases b <;> simp [he, orFlag]
    · cases b <;> simp [he, orFlag]

/-- Exactly the finite sample flags are combined, including for malformed input words. -/
theorem kindWord_value (source code₀ code₁ out : List Bool) :
    kindWord source code₀ code₁ out = [decide (∃ t : Fin 41,
      sampleFlag source code₀ code₁ (List.replicate t.val false) out = [true])] := by
  rw [kindWord_eq, collect_value]
  congr 2
  apply propext
  constructor
  · rintro ⟨i, hi, ht⟩
    exact ⟨⟨i, hi⟩, ht⟩
  · rintro ⟨i, ht⟩
    exact ⟨i.val, i.isLt, ht⟩

/-- The alternating extraction blocks use comparator digits and affine remainders. -/
theorem sampleFlag_extraction (ordinal out source code₀ code₁ : List Bool)
    (t : Fin 41) (axis : Fin 2) (stage : Fin 2) (j : ℕ) (hj : j < (CircuitWords.first source).length)
    (ht : ordinal.length = t.val)
    (ho : out.length = BrouwerNashLayout.sampleBase (CircuitWords.first source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t +
      BrouwerNashLayout.digit (CircuitWords.first source).length axis j + stage.val) :
    sampleFlag (source) (code₀) (code₁) (ordinal) (out) = [decide (stage = 0)] := by
  rw [sampleFlag_value, ht, ho]
  simp only [BrouwerNashLayout.sampleBase, BrouwerNashLayout.digit]
  congr 2
  apply propext
  rw [Fin.ext_iff]
  fin_cases axis <;> fin_cases stage <;> dsimp only <;> omega

/-- Every stage of the valid ripple increment is a comparator block. -/
theorem sampleFlag_increment (ordinal out source code₀ code₁ : List Bool)
    (t : Fin 41) (axis : Fin 2) (stage : Fin 4) (j : ℕ) (hj : j < (CircuitWords.first source).length)
    (ht : ordinal.length = t.val)
    (ho : out.length = BrouwerNashLayout.sampleBase (CircuitWords.first source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t +
      BrouwerNashLayout.increment (CircuitWords.first source).length axis j stage) :
    sampleFlag (source) (code₀) (code₁) (ordinal) (out) = [true] := by
  rw [sampleFlag_value, ht, ho]
  simp only [BrouwerNashLayout.sampleBase, BrouwerNashLayout.increment,
    BrouwerNashLayout.incrementBase]
  have hs := stage.isLt
  fin_cases axis <;> dsimp only <;> congr 1 <;> apply decide_eq_true <;> omega

private theorem sampleFlag_true_bounds (ordinal out source code₀ code₁ : List Bool)
    (ht : sampleFlag (source) (code₀) (code₁) (ordinal) (out) = [true]) :
    BrouwerNashLayout.globalCount (CircuitWords.first source).length + ordinal.length *
      BrouwerNashLayout.sampleWidth (CircuitWords.first source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length ≤ out.length ∧
    out.length < BrouwerNashLayout.globalCount (CircuitWords.first source).length +
      (ordinal.length + 1) * BrouwerNashLayout.sampleWidth (CircuitWords.first source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length := by
  rw [sampleFlag_value] at ht
  have hp := of_decide_eq_true (List.cons.inj ht).1
  have hw : 2 + 12 * (CircuitWords.first source).length ≤
      BrouwerNashLayout.sampleWidth (CircuitWords.first source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length := by
    simp only [BrouwerNashLayout.sampleWidth]
    omega
  rw [Nat.add_mul, one_mul]
  omega

/-- A sample-local output cannot select another sample's comparator flag. -/
theorem kindWord_at_sample (out source code₀ code₁ : List Bool) (t : Fin 41) (i : ℕ)
    (hi : i < BrouwerNashLayout.sampleWidth (CircuitWords.first source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length)
    (ho : out.length = BrouwerNashLayout.sampleBase (CircuitWords.first source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t + i) :
    kindWord (source) (code₀) (code₁) (out) =
      sampleFlag (source) (code₀) (code₁) (List.replicate t.val false) (out) := by
  rw [kindWord_value]
  have he : (∃ s : Fin 41, sampleFlag source code₀ code₁ (List.replicate s.val false) out = [true]) ↔
      sampleFlag (source) (code₀) (code₁) (List.replicate t.val false) (out) = [true] := by
    constructor
    · rintro ⟨s, hs⟩
      have hbounds := sampleFlag_true_bounds (List.replicate s.val false)
        out source code₀ code₁ hs
      simp only [List.length_replicate] at hbounds
      simp only [BrouwerNashLayout.sampleBase] at ho
      have hst : s.val = t.val := by
        by_cases hlt : s.val < t.val
        · have hm := Nat.mul_le_mul_right
            (BrouwerNashLayout.sampleWidth (CircuitWords.first source).length
              (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length)
            (show s.val + 1 ≤ t.val by omega)
          omega
        · by_cases hgt : t.val < s.val
          · have hm := Nat.mul_le_mul_right
              (BrouwerNashLayout.sampleWidth (CircuitWords.first source).length
                (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length)
              (show t.val + 1 ≤ s.val by omega)
            simp only [Nat.add_mul, one_mul] at hm
            omega
          · omega
      have hs_eq : s = t := Fin.ext hst
      subst s
      exact hs
    · intro ht
      exact ⟨t, ht⟩
  simp only [he]
  rcases sampleFlag_flag (source) (code₀) (code₁) (List.replicate t.val false) (out)
    with ⟨b, hb⟩
  rw [hb]
  cases b <;> rfl

end GameTheory.Complexity.Backend.BrouwerNashSampleKind
