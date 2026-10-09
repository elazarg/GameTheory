import GameTheoryComplexity.Backend.BrouwerNashHeaders
import GameTheoryComplexity.Backend.BinaryUnaryArithmetic

/-! Comparator-kind flags for digit extraction and ripple increments in each jitter sample. -/
namespace GameTheory.Complexity.Backend.BrouwerNashSampleKind
open _root_.Complexity _root_.Complexity.Cobham

/-- Comparator flag for one sample ordinal and the source-dependent layout. -/
def sampleFlag (v : Fin 6 → List Bool) : List Bool :=
  let source := ![v 3, v 4, v 5]
  let depth := BrouwerNashHeaders.sourceDepthRuler source
  let base := BrouwerNashHeaders.globalRuler source ++
    smash (v 0) (BrouwerNashHeaders.sampleRuler source)
  let first := base ++ [false, false]
  let middle := first ++ smash depth [false, false, false, false]
  let last := first ++ smash depth (List.replicate 12 false)
  orBit
    (andBit (andBit (lenLeFlag (v 1) first) (notBit (lenLeFlag (v 1) middle)))
      (notBit (binaryLengthParity ((v 1).drop base.length))))
    (andBit (lenLeFlag (v 1) middle) (notBit (lenLeFlag (v 1) last)))

private theorem sampleFlag_cobham : Cobham sampleFlag := by
  have hd : Cobham fun v : Fin 6 → List Bool =>
      BrouwerNashHeaders.sourceDepthRuler ![v 3, v 4, v 5] :=
    Cobham.comp₃ BrouwerNashHeaders.sourceDepthRuler_cobham (.proj 3) (.proj 4) (.proj 5)
  have hg : Cobham fun v : Fin 6 → List Bool =>
      BrouwerNashHeaders.globalRuler ![v 3, v 4, v 5] :=
    Cobham.comp₃ BrouwerNashHeaders.globalRuler_cobham (.proj 3) (.proj 4) (.proj 5)
  have hs : Cobham fun v : Fin 6 → List Bool =>
      BrouwerNashHeaders.sampleRuler ![v 3, v 4, v 5] :=
    Cobham.comp₃ BrouwerNashHeaders.sampleRuler_cobham (.proj 3) (.proj 4) (.proj 5)
  have hb := appendFn hg (Cobham.comp₂ Cobham.smash (.proj 0) hs)
  have hf := appendFn hb (Cobham.const [false, false])
  have hm := appendFn hf
    (Cobham.comp₂ Cobham.smash hd (Cobham.const [false, false, false, false]))
  have hl := appendFn hf
    (Cobham.comp₂ Cobham.smash hd (Cobham.const (List.replicate 12 false)))
  have ht := Cobham.orFn
    (Cobham.andFn
      (Cobham.andFn (lenLeFlag_mem (.proj 1) hf) (Cobham.notFn (lenLeFlag_mem (.proj 1) hm)))
      (Cobham.notFn (Cobham.comp binaryLengthParity_cobham fun _ : Fin 1 =>
        dropFn hb (.proj 1))))
    (Cobham.andFn (lenLeFlag_mem (.proj 1) hm) (Cobham.notFn (lenLeFlag_mem (.proj 1) hl)))
  exact ht.of_eq fun v => rfl

private def collect : ℕ → (Fin 5 → List Bool) → List Bool
  | 0, _ => [false]
  | n + 1, v => orBit (collect n v) (sampleFlag (Fin.cons (List.replicate n false) v))

private theorem collect_cobham (n : ℕ) : Cobham (collect n) := by
  induction n with
  | zero => exact Cobham.const [false]
  | succ n ih =>
    have hv : ∀ i : Fin 6, Cobham fun v : Fin 5 → List Bool =>
        (Fin.cons (List.replicate n false) v : Fin 6 → List Bool) i := by
      intro i
      exact Fin.cases (Cobham.const (List.replicate n false)) (fun j => .proj j) i
    exact Cobham.orFn ih (Cobham.comp sampleFlag_cobham hv)

/-- The input layout is output ruler, action ruler, source and the two scalar color codes. -/
def kindWord : (Fin 5 → List Bool) → List Bool := collect 41

set_option maxRecDepth 4096 in
theorem kindWord_cobham : Cobham kindWord := collect_cobham 41

theorem kindWord_mem_FPn : FPn kindWord := cobham_iff_FPn.mp kindWord_cobham

private theorem lenLe_value (a b : List Bool) : lenLeFlag a b = [decide (b.length ≤ a.length)] := by
  rcases lenLeFlag_flag a b with h | h
  · rw [h]; simp [(lenLeFlag_eq_true_iff a b).mp h]
  · rw [h]
    have hn : ¬ b.length ≤ a.length := by
      intro he
      have ht := (lenLeFlag_eq_true_iff a b).mpr he
      rw [h] at ht
      contradiction
    simp [hn]

private theorem and_decide (P Q : Prop) [Decidable P] [Decidable Q] :
    andBit [decide P] [decide Q] = [decide (P ∧ Q)] := by
  by_cases hp : P <;> by_cases hq : Q <;> simp [hp, hq, andBit, caseBit₀]

private theorem or_decide (P Q : Prop) [Decidable P] [Decidable Q] :
    orBit [decide P] [decide Q] = [decide (P ∨ Q)] := by
  by_cases hp : P <;> by_cases hq : Q <;> simp [hp, hq, orBit, caseBit₀]

private theorem not_decide (P : Prop) [Decidable P] :
    notBit [decide P] = [decide (¬ P)] := by
  by_cases hp : P <;> simp [hp, notBit, caseBit₀]

theorem sampleFlag_value (t out action source code₀ code₁ : List Bool) :
    sampleFlag ![t, out, action, source, code₀, code₁] =
      [decide (
        (BrouwerNashLayout.globalCount (pairFst source).length + t.length *
          BrouwerNashLayout.sampleWidth (pairFst source).length
            (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length + 2 ≤ out.length ∧
        out.length < BrouwerNashLayout.globalCount (pairFst source).length + t.length *
          BrouwerNashLayout.sampleWidth (pairFst source).length
            (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length +
          2 + 4 * (pairFst source).length ∧
        (out.length - (BrouwerNashLayout.globalCount (pairFst source).length + t.length *
          BrouwerNashLayout.sampleWidth (pairFst source).length
            (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length)) % 2 ≠ 1) ∨
        (BrouwerNashLayout.globalCount (pairFst source).length + t.length *
          BrouwerNashLayout.sampleWidth (pairFst source).length
            (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length +
          2 + 4 * (pairFst source).length ≤ out.length ∧
        out.length < BrouwerNashLayout.globalCount (pairFst source).length + t.length *
          BrouwerNashLayout.sampleWidth (pairFst source).length
            (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length +
          2 + 12 * (pairFst source).length))] := by
  dsimp only [sampleFlag]
  rw [lenLe_value, lenLe_value, lenLe_value, binaryLengthParity_value,
    not_decide, not_decide, not_decide, and_decide, and_decide, and_decide, or_decide]
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_drop,
    List.length_replicate, smash_length, BrouwerNashHeaders.sourceDepthRuler_length,
    BrouwerNashHeaders.globalRuler_length, BrouwerNashHeaders.sampleRuler_length]
  congr 2
  apply propext
  dsimp
  omega

private theorem sampleFlag_flag (v : Fin 6 → List Bool) :
    ∃ b : Bool, sampleFlag v = [b] := by
  have hv : v = ![v 0, v 1, v 2, v 3, v 4, v 5] := by
    ext i
    fin_cases i <;> rfl
  rw [hv, sampleFlag_value]
  exact ⟨_, rfl⟩

private theorem collect_value (n : ℕ) (v : Fin 5 → List Bool) :
    collect n v =
      [decide (∃ i < n, sampleFlag (Fin.cons (List.replicate i false) v) = [true])] := by
  induction n with
  | zero => simp [collect]
  | succ n ih =>
    rw [collect, ih]
    rcases sampleFlag_flag (Fin.cons (List.replicate n false) v) with ⟨b, hb⟩
    rw [hb]
    have hs : (∃ i < n + 1, sampleFlag (Fin.cons (List.replicate i false) v) = [true]) ↔
        (∃ i < n, sampleFlag (Fin.cons (List.replicate i false) v) = [true]) ∨
          sampleFlag (Fin.cons (List.replicate n false) v) = [true] := by
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
    by_cases he : ∃ i < n, sampleFlag (Fin.cons (List.replicate i false) v) = [true]
    · cases b <;> simp [he, orBit, caseBit₀]
    · cases b <;> simp [he, orBit, caseBit₀]

/-- Exactly the finite sample flags are combined, including for malformed input words. -/
theorem kindWord_value (v : Fin 5 → List Bool) :
    kindWord v = [decide (∃ t : Fin 41,
      sampleFlag (Fin.cons (List.replicate t.val false) v) = [true])] := by
  rw [kindWord, collect_value]
  congr 2
  apply propext
  constructor
  · rintro ⟨i, hi, ht⟩
    exact ⟨⟨i, hi⟩, ht⟩
  · rintro ⟨i, ht⟩
    exact ⟨i.val, i.isLt, ht⟩

/-- The alternating extraction blocks use comparator digits and affine remainders. -/
theorem sampleFlag_extraction (ordinal out action source code₀ code₁ : List Bool)
    (t : Fin 41) (axis : Fin 2) (stage : Fin 2) (j : ℕ) (hj : j < (pairFst source).length)
    (ht : ordinal.length = t.val)
    (ho : out.length = BrouwerNashLayout.sampleBase (pairFst source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t +
      BrouwerNashLayout.digit (pairFst source).length axis j + stage.val) :
    sampleFlag ![ordinal, out, action, source, code₀, code₁] = [decide (stage = 0)] := by
  rw [sampleFlag_value, ht, ho]
  simp only [BrouwerNashLayout.sampleBase, BrouwerNashLayout.digit]
  congr 2
  apply propext
  rw [Fin.ext_iff]
  fin_cases axis <;> fin_cases stage <;> dsimp only <;> omega

/-- Every stage of the valid ripple increment is a comparator block. -/
theorem sampleFlag_increment (ordinal out action source code₀ code₁ : List Bool)
    (t : Fin 41) (axis : Fin 2) (stage : Fin 4) (j : ℕ) (hj : j < (pairFst source).length)
    (ht : ordinal.length = t.val)
    (ho : out.length = BrouwerNashLayout.sampleBase (pairFst source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t +
      BrouwerNashLayout.increment (pairFst source).length axis j stage) :
    sampleFlag ![ordinal, out, action, source, code₀, code₁] = [true] := by
  rw [sampleFlag_value, ht, ho]
  simp only [BrouwerNashLayout.sampleBase, BrouwerNashLayout.increment,
    BrouwerNashLayout.incrementBase]
  have hs := stage.isLt
  fin_cases axis <;> dsimp only <;> congr 1 <;> apply decide_eq_true <;> omega
private theorem sampleFlag_true_bounds (ordinal out action source code₀ code₁ : List Bool)
    (ht : sampleFlag ![ordinal, out, action, source, code₀, code₁] = [true]) :
    BrouwerNashLayout.globalCount (pairFst source).length + ordinal.length *
      BrouwerNashLayout.sampleWidth (pairFst source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length ≤ out.length ∧
    out.length < BrouwerNashLayout.globalCount (pairFst source).length +
      (ordinal.length + 1) * BrouwerNashLayout.sampleWidth (pairFst source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length := by
  rw [sampleFlag_value] at ht
  have hp := of_decide_eq_true (List.cons.inj ht).1
  have hw : 2 + 12 * (pairFst source).length ≤
      BrouwerNashLayout.sampleWidth (pairFst source).length
        (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length := by
    simp only [BrouwerNashLayout.sampleWidth]
    omega
  rw [Nat.add_mul, one_mul]
  omega

/-- A sample-local output cannot select another sample's comparator flag. -/
theorem kindWord_at_sample (out action source code₀ code₁ : List Bool) (t : Fin 41) (i : ℕ)
    (hi : i < BrouwerNashLayout.sampleWidth (pairFst source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length)
    (ho : out.length = BrouwerNashLayout.sampleBase (pairFst source).length
      (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length t + i) :
    kindWord ![out, action, source, code₀, code₁] =
      sampleFlag ![List.replicate t.val false, out, action, source, code₀, code₁] := by
  rw [kindWord_value]
  have he : (∃ s : Fin 41, sampleFlag
      (Fin.cons (List.replicate s.val false) ![out, action, source, code₀, code₁]) = [true]) ↔
      sampleFlag ![List.replicate t.val false, out, action, source, code₀, code₁] = [true] := by
    constructor
    · rintro ⟨s, hs⟩
      have hbounds := sampleFlag_true_bounds (List.replicate s.val false)
        out action source code₀ code₁ hs
      simp only [List.length_replicate] at hbounds
      simp only [BrouwerNashLayout.sampleBase] at ho
      have hst : s.val = t.val := by
        by_cases hlt : s.val < t.val
        · have hm := Nat.mul_le_mul_right
            (BrouwerNashLayout.sampleWidth (pairFst source).length
              (circuitUnaryPrefix code₀).length (circuitUnaryPrefix code₁).length)
            (show s.val + 1 ≤ t.val by omega)
          omega
        · by_cases hgt : t.val < s.val
          · have hm := Nat.mul_le_mul_right
              (BrouwerNashLayout.sampleWidth (pairFst source).length
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
  rcases sampleFlag_flag ![List.replicate t.val false, out, action, source, code₀, code₁]
    with ⟨b, hb⟩
  rw [hb]
  cases b <;> rfl
end GameTheory.Complexity.Backend.BrouwerNashSampleKind