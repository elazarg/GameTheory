import GameTheoryComplexity.Backend.BinarySignedMatrixMachine
import GameTheoryComplexity.Backend.BinaryUnaryArithmetic
import GameTheoryComplexity.Backend.BinarySubsetMachine
import GameTheoryComplexity.Backend.BinaryIndexedAll
import GameTheory.Finite.BimatrixPathBinaryCodec

/-! Certified unmasking and combinatorial validation of complementary path words.
The dimension is an explicit length ruler and the dropped label is zero.
-/
namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham

private def basicBit (v : Fin 2 → List Bool) : List Bool :=
  xorSuffix (bitAt (v 0) (v 1)) (notBit (binaryLengthParity (v 0)))

private def enteringBit (v : Fin 2 → List Bool) : List Bool :=
  xorSuffix (bitAt (v 0) (v 1)) (lenEqFlag (v 0) [false])

/-- Unmask the basis bits, indexed in canonical label/kind order. -/
def bimatrixNodeBasicWord (v : Fin 2 → List Bool) : List Bool :=
  binarySignedTable basicBit ((v 0) ++ (v 0)) [false] ![v 1]

/-- Unmask the entering bits; the source entering variable has position one. -/
def bimatrixNodeEnteringWord (v : Fin 2 → List Bool) : List Bool :=
  binarySignedTable enteringBit ((v 0) ++ (v 0)) [false]
    ![(v 1).drop (((v 0) ++ (v 0)).length)]

private theorem basicBit_cobham : Cobham basicBit :=
  xorSuffix_mem (Cobham.comp₂ Cobham.bitAtFn (.proj 0) (.proj 1))
    (Cobham.notFn (Cobham.comp binaryLengthParity_cobham fun _ => .proj 0))

private theorem enteringBit_cobham : Cobham enteringBit :=
  xorSuffix_mem (Cobham.comp₂ Cobham.bitAtFn (.proj 0) (.proj 1))
    (lenEqFlag_mem (.proj 0) (Cobham.const [false]))

theorem bimatrixNodeBasicWord_cobham : Cobham bimatrixNodeBasicWord :=
  Cobham.comp₃ (binarySignedTable_cobham basicBit_cobham)
    (Cobham.appendFn (.proj 0) (.proj 0)) (Cobham.const [false]) (.proj 1)

theorem bimatrixNodeEnteringWord_cobham : Cobham bimatrixNodeEnteringWord :=
  Cobham.comp₃ (binarySignedTable_cobham enteringBit_cobham)
    (Cobham.appendFn (.proj 0) (.proj 0)) (Cobham.const [false])
    (Cobham.dropFn (Cobham.appendFn (.proj 0) (.proj 0)) (.proj 1))

theorem bimatrixNodeBasicWord_mem_FPn : FPn bimatrixNodeBasicWord :=
  cobham_iff_FPn.mp bimatrixNodeBasicWord_cobham

theorem bimatrixNodeEnteringWord_mem_FPn : FPn bimatrixNodeEnteringWord :=
  cobham_iff_FPn.mp bimatrixNodeEnteringWord_cobham

@[simp] theorem bimatrixNodeBasicWord_length (v : Fin 2 → List Bool) :
    (bimatrixNodeBasicWord v).length = 2 * (v 0).length := by
  simp [bimatrixNodeBasicWord, two_mul]

@[simp] theorem bimatrixNodeEnteringWord_length (v : Fin 2 → List Bool) :
    (bimatrixNodeEnteringWord v).length = 2 * (v 0).length := by
  simp [bimatrixNodeEnteringWord, two_mul]



private theorem lenEq_value (x y : List Bool) : lenEqFlag x y = [decide (x.length = y.length)] := by
  rcases lenEqFlag_flag x y with h | h
  · rw [h]; simp [(lenEqFlag_eq_true_iff x y).mp h]
  · rw [h]
    have hn : x.length ≠ y.length := by
      intro he
      have := (lenEqFlag_eq_true_iff x y).mpr he
      simp [h] at this
    simp [hn]

private theorem xor_value (x y : Bool) : xorSuffix [x] [y] = [xor x y] := by
  rw [xorSuffix_eq_zipWith_of_length [x] [y] rfl]
  rfl

private theorem xor_decide (x y : Bool) : some (xor x y) = some (decide (xor x y = true)) := by
  cases x <;> cases y <;> rfl

private theorem basicBit_value (r node : List Bool) :
    basicBit ![r, node] = [xor (node[r.length]?.getD false) (!(decide (r.length % 2 = 1)))] := by
  change xorSuffix (bitAt r node) (notBit (binaryLengthParity r)) = _
  rw [bitAt_getElem?, binaryLengthParity_value]
  generalize decide (r.length % 2 = 1) = b
  cases b <;> exact xor_value _ _

private theorem enteringBit_value (r node : List Bool) :
    enteringBit ![r, node] = [xor (node[r.length]?.getD false) (decide (r.length = 1))] := by
  change xorSuffix (bitAt r node) (lenEqFlag r [false]) = _
  rw [bitAt_getElem?, lenEq_value]
  exact xor_value _ _

/-- Exact unmasked basis bytes, including zero padding for truncated nodes. -/
theorem bimatrixNodeBasicWord_value (v : Fin 2 → List Bool) :
    bimatrixNodeBasicWord v = (List.range (2 * (v 0).length)).map
      (fun i => xor ((v 1)[i]?.getD false) (!(decide (i % 2 = 1)))) := by
  have h := binarySignedTable_flags basicBit ![v 1]
    (fun i => xor ((v 1)[i]?.getD false) (!(decide (i % 2 = 1))))
    (fun r => basicBit_value r (v 1)) ((v 0) ++ (v 0))
  simpa only [bimatrixNodeBasicWord, List.length_append, ← two_mul] using h

/-- Exact entering bytes with the source's one-hot bit removed. -/
theorem bimatrixNodeEnteringWord_value (v : Fin 2 → List Bool) :
    bimatrixNodeEnteringWord v = (List.range (2 * (v 0).length)).map
      (fun i => xor ((v 1)[2 * (v 0).length + i]?.getD false) (decide (i = 1))) := by
  have h := binarySignedTable_flags enteringBit ![(v 1).drop (2 * (v 0).length)]
    (fun i => xor (((v 1).drop (2 * (v 0).length))[i]?.getD false) (decide (i = 1)))
    (fun r => enteringBit_value r _) ((v 0) ++ (v 0))
  simpa only [bimatrixNodeEnteringWord, List.length_append, ← two_mul, List.getElem?_drop] using h

private def coverageBit (v : Fin 2 → List Bool) : List Bool :=
  orBit (lenEqFlag (v 0) []) (notBit (andBit
    (bitAt ((v 0) ++ (v 0)) (v 1))
    (bitAt (true :: ((v 0) ++ (v 0))) (v 1))))

private def portBit (v : Fin 3 → List Bool) : List Bool :=
  let label := binaryHalfRuler (v 0)
  orBit (notBit (bitAt (v 0) (v 2)))
    (andBit (notBit (bitAt (v 0) (v 1)))
      (orBit (lenEqFlag label []) (notBit (orBit
        (bitAt (label ++ label) (v 1)) (bitAt (true :: (label ++ label)) (v 1))))))

private theorem coverageBit_cobham : Cobham coverageBit :=
  Cobham.orFn (lenEqFlag_mem (.proj 0) (Cobham.const []))
    (Cobham.notFn (Cobham.andFn
      (Cobham.comp₂ Cobham.bitAtFn (Cobham.appendFn (.proj 0) (.proj 0)) (.proj 1))
      (Cobham.comp₂ Cobham.bitAtFn
        (Cobham.appendFn (Cobham.const [true]) (Cobham.appendFn (.proj 0) (.proj 0))) (.proj 1))))

private theorem portBit_cobham : Cobham portBit := by
  have hl : Cobham fun v : Fin 3 → List Bool => binaryHalfRuler (v 0) :=
    Cobham.comp binaryHalfRuler_cobham fun _ => .proj 0
  exact Cobham.orFn (Cobham.notFn (Cobham.comp₂ Cobham.bitAtFn (.proj 0) (.proj 2)))
    (Cobham.andFn (Cobham.notFn (Cobham.comp₂ Cobham.bitAtFn (.proj 0) (.proj 1)))
      (Cobham.orFn (lenEqFlag_mem hl (Cobham.const [])) (Cobham.notFn (Cobham.orFn
        (Cobham.comp₂ Cobham.bitAtFn (Cobham.appendFn hl hl) (.proj 1))
        (Cobham.comp₂ Cobham.bitAtFn
          (Cobham.appendFn (Cobham.const [true]) (Cobham.appendFn hl hl)) (.proj 1))))))

private abbrev CoveredAt (basic : List Bool) (i : ℕ) : Prop :=
  i = 0 ∨ basic[2 * i]?.getD false = false ∨ basic[2 * i + 1]?.getD false = false

private abbrev PermittedAt (basic entering : List Bool) (i : ℕ) : Prop :=
  entering[i]?.getD false = true → basic[i]?.getD false = false ∧
    (i / 2 = 0 ∨ (basic[2 * (i / 2)]?.getD false = false ∧
      basic[2 * (i / 2) + 1]?.getD false = false))

private theorem coverageBit_value (r basic : List Bool) :
    coverageBit ![r, basic] = [decide (CoveredAt basic r.length)] := by
  change orBit (lenEqFlag r []) (notBit (andBit (bitAt (r ++ r) basic)
    (bitAt (true :: (r ++ r)) basic))) = _
  rw [lenEq_value, bitAt_getElem?, bitAt_getElem?]
  simp only [List.length_nil, List.length_append, List.length_cons, ← two_mul]
  unfold CoveredAt
  by_cases hz : r.length = 0 <;>
    cases ha : basic[2 * r.length]?.getD false <;>
    cases hb : basic[2 * r.length + 1]?.getD false <;>
    simp [hz, orBit, andBit, notBit, caseBit₀]

private theorem portBit_value (r basic entering : List Bool) :
    portBit ![r, basic, entering] = [decide (PermittedAt basic entering r.length)] := by
  change orBit (notBit (bitAt r entering))
    (andBit (notBit (bitAt r basic))
      (orBit (lenEqFlag (binaryHalfRuler r) []) (notBit (orBit
        (bitAt (binaryHalfRuler r ++ binaryHalfRuler r) basic)
        (bitAt (true :: (binaryHalfRuler r ++ binaryHalfRuler r)) basic))))) = _
  rw [bitAt_getElem?, bitAt_getElem?, lenEq_value, bitAt_getElem?, bitAt_getElem?]
  simp only [List.length_nil, List.length_append, List.length_cons,
    binaryHalfRuler_length, ← two_mul]
  unfold PermittedAt
  by_cases hz : r.length / 2 = 0 <;>
    cases he : entering[r.length]?.getD false <;>
    cases ha : basic[r.length]?.getD false <;>
    cases hb : basic[2 * (r.length / 2)]?.getD false <;>
    cases hc : basic[2 * (r.length / 2) + 1]?.getD false <;>
    simp [hz, orBit, andBit, notBit, caseBit₀]

/-- Combinatorial validation: exact size, basis cardinality, one entering variable,
coverage away from label zero, and the complementary-port condition. -/
def bimatrixNodeSyntaxFlag (v : Fin 2 → List Bool) : List Bool :=
  let basic := bimatrixNodeBasicWord v
  let entering := bimatrixNodeEnteringWord v
  andBit (lenEqFlag (v 1) (((v 0) ++ (v 0)) ++ ((v 0) ++ (v 0))))
    (andBit (lenEqFlag (binarySubsetTally basic) (v 0))
      (andBit (lenEqFlag (binarySubsetTally entering) [false])
        (andBit (binaryIndexedAll coverageBit (v 0) ![basic])
          (binaryIndexedAll portBit ((v 0) ++ (v 0)) ![basic, entering]))))

theorem bimatrixNodeSyntaxFlag_cobham : Cobham bimatrixNodeSyntaxFlag := by
  have ht {term : (Fin 2 → List Bool) → List Bool} (h : Cobham term) :
      Cobham fun v => binarySubsetTally (term v) := Cobham.comp binarySubsetTally_cobham fun _ => h
  exact Cobham.andFn
    (lenEqFlag_mem (.proj 1) (Cobham.appendFn (Cobham.appendFn (.proj 0) (.proj 0))
      (Cobham.appendFn (.proj 0) (.proj 0))))
    (Cobham.andFn (lenEqFlag_mem (ht bimatrixNodeBasicWord_cobham) (.proj 0))
      (Cobham.andFn (lenEqFlag_mem (ht bimatrixNodeEnteringWord_cobham) (Cobham.const [false]))
        (Cobham.andFn (Cobham.comp₂ (binaryIndexedAll_cobham coverageBit_cobham)
          (.proj 0) bimatrixNodeBasicWord_cobham)
          (Cobham.comp₃ (binaryIndexedAll_cobham portBit_cobham)
            (Cobham.appendFn (.proj 0) (.proj 0))
            bimatrixNodeBasicWord_cobham bimatrixNodeEnteringWord_cobham))))

theorem bimatrixNodeSyntaxFlag_mem_FPn : FPn bimatrixNodeSyntaxFlag :=
  cobham_iff_FPn.mp bimatrixNodeSyntaxFlag_cobham

private theorem and_decide (P Q : Prop) [Decidable P] [Decidable Q] :
    andBit [decide P] [decide Q] = [decide (P ∧ Q)] := by
  by_cases hp : P <;> by_cases hq : Q <;> simp [hp, hq, andBit, caseBit₀]

/-- All syntactic conditions checked by the bounded Boolean machine. -/
theorem bimatrixNodeSyntaxFlag_value (v : Fin 2 → List Bool) :
    bimatrixNodeSyntaxFlag v = [decide ((v 1).length = 4 * (v 0).length ∧
      (bimatrixNodeBasicWord v).count true = (v 0).length ∧
      (bimatrixNodeEnteringWord v).count true = 1 ∧
      (∀ i < (v 0).length, CoveredAt (bimatrixNodeBasicWord v) i) ∧
      (∀ i < 2 * (v 0).length, PermittedAt (bimatrixNodeBasicWord v)
        (bimatrixNodeEnteringWord v) i))] := by
  rw [bimatrixNodeSyntaxFlag, lenEq_value, lenEq_value, lenEq_value,
    binarySubsetTally_length, binarySubsetTally_length]
  rw [binaryIndexedAll_value coverageBit _ _ (fun r => coverageBit_value r _),
    binaryIndexedAll_value portBit _ _ (fun r => portBit_value r _ _)]
  simp only [List.length_append, List.length_singleton, ← two_mul,
    show 2 * (2 * (v 0).length) = 4 * (v 0).length by omega]
  rw [and_decide, and_decide, and_decide, and_decide]

/-- Unmasking recovers the base codec's canonical basis membership word. -/
theorem bimatrixNodeBasicWord_membership {m n : ℕ} (dimension node : List Bool)
    (hk : dimension.length = m + n) :
    bimatrixNodeBasicWord ![dimension, node] =
      GameTheory.Finite.BimatrixPathBinaryCodec.membershipWord
        (GameTheory.Finite.BimatrixPathBinaryCodec.basic (m := m) (n := n) node) := by
  rw [bimatrixNodeBasicWord_value]
  apply List.ext_getElem?
  intro i
  by_cases hi : i < 2 * (m + n)
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hk,
      List.getElem?_map, List.getElem?_range, Option.map_some,
      GameTheory.Finite.BimatrixPathBinaryCodec.membershipWord, List.getElem?_ofFn, hi,
      ↓reduceDIte]
    simp only [GameTheory.Finite.BimatrixPathBinaryCodec.basic,
      Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [GameTheory.Finite.BimatrixPathBinaryCodec.index_variableAt]
    change some (xor (node[i]?.getD false) (!(decide (i % 2 = 1)))) =
      some (decide (xor (node[i]?.getD false) (!(decide (i % 2 = 1))) = true))
    exact xor_decide _ _
  · simp [hk, hi, GameTheory.Finite.BimatrixPathBinaryCodec.membershipWord]

theorem bimatrixNodeBasicWord_bit {m n : ℕ} (dimension node : List Bool)
    (hk : dimension.length = m + n) (v : GameTheory.Finite.BimatrixVariable m n) :
    (bimatrixNodeBasicWord ![dimension, node])[(GameTheory.Finite.BimatrixPathBinaryCodec.index v).val]?.getD false =
      decide (v ∈ GameTheory.Finite.BimatrixPathBinaryCodec.basic node) := by
  rw [bimatrixNodeBasicWord_membership dimension node hk]
  simp only [GameTheory.Finite.BimatrixPathBinaryCodec.membershipWord,
    List.getElem?_ofFn, (GameTheory.Finite.BimatrixPathBinaryCodec.index v).isLt,
    ↓reduceDIte, Option.getD_some]
  exact congrArg (fun u => decide (u ∈ GameTheory.Finite.BimatrixPathBinaryCodec.basic node))
    (GameTheory.Finite.BimatrixPathBinaryCodec.variableAt_index v)

/-- Unmasking recovers the base codec's entering set at dropped label zero. -/
theorem bimatrixNodeEnteringWord_membership {m n : ℕ} (dimension node : List Bool)
    (hk : dimension.length = m + n) (d : Fin (m + n)) (hd : d.val = 0) :
    bimatrixNodeEnteringWord ![dimension, node] =
      GameTheory.Finite.BimatrixPathBinaryCodec.membershipWord
        (GameTheory.Finite.BimatrixPathBinaryCodec.enteringSet d node) := by
  rw [bimatrixNodeEnteringWord_value]
  apply List.ext_getElem?
  intro i
  by_cases hi : i < 2 * (m + n)
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hk,
      List.getElem?_map, List.getElem?_range, Option.map_some,
      GameTheory.Finite.BimatrixPathBinaryCodec.membershipWord, List.getElem?_ofFn, hi,
      ↓reduceDIte]
    let u := GameTheory.Finite.BimatrixPathBinaryCodec.variableAt (m := m) (n := n) ⟨i, hi⟩
    have hsource : u = toLex (d, true) ↔ i = 1 := by
      have hindex : (GameTheory.Finite.BimatrixPathBinaryCodec.index (toLex (d, true))).val = 1 := by
        simp [GameTheory.Finite.BimatrixPathBinaryCodec.index, hd]
      constructor
      · intro he
        have hh := congrArg (fun v => (GameTheory.Finite.BimatrixPathBinaryCodec.index v).val) he
        simpa only [u, GameTheory.Finite.BimatrixPathBinaryCodec.index_variableAt, hindex] using hh
      · intro he
        apply GameTheory.Finite.BimatrixPathBinaryCodec.index_strictMono.injective
        apply Fin.ext
        simpa only [u, GameTheory.Finite.BimatrixPathBinaryCodec.index_variableAt, hindex] using he
    change some (xor (node[2 * (m + n) + i]?.getD false) (decide (i = 1))) =
      some (decide (u ∈ GameTheory.Finite.BimatrixPathBinaryCodec.enteringSet d node))
    simp only [GameTheory.Finite.BimatrixPathBinaryCodec.enteringSet,
      Finset.mem_filter, Finset.mem_univ, true_and]
    change some (xor (node[2 * (m + n) + i]?.getD false) (decide (i = 1))) =
      some (decide (xor
        (node[2 * (m + n) + (GameTheory.Finite.BimatrixPathBinaryCodec.index u).val]?.getD false)
        (decide (u = toLex (d, true))) = true))
    simp only [u, GameTheory.Finite.BimatrixPathBinaryCodec.index_variableAt]
    simp only [← hsource]
    change some (xor (node[2 * (m + n) + i]?.getD false) (decide (u = toLex (d, true)))) =
      some (decide (xor (node[2 * (m + n) + i]?.getD false)
        (decide (u = toLex (d, true))) = true))
    exact xor_decide _ _
  · simp [hk, hi, GameTheory.Finite.BimatrixPathBinaryCodec.membershipWord]

theorem bimatrixNodeEnteringWord_bit {m n : ℕ} (dimension node : List Bool)
    (hk : dimension.length = m + n) (d : Fin (m + n)) (hd : d.val = 0)
    (v : GameTheory.Finite.BimatrixVariable m n) :
    (bimatrixNodeEnteringWord ![dimension, node])[(GameTheory.Finite.BimatrixPathBinaryCodec.index v).val]?.getD false =
      decide (v ∈ GameTheory.Finite.BimatrixPathBinaryCodec.enteringSet d node) := by
  rw [bimatrixNodeEnteringWord_membership dimension node hk d hd]
  simp only [GameTheory.Finite.BimatrixPathBinaryCodec.membershipWord,
    List.getElem?_ofFn, (GameTheory.Finite.BimatrixPathBinaryCodec.index v).isLt,
    ↓reduceDIte, Option.getD_some]
  exact congrArg (fun u => decide (u ∈ GameTheory.Finite.BimatrixPathBinaryCodec.enteringSet d node))
    (GameTheory.Finite.BimatrixPathBinaryCodec.variableAt_index v)

private theorem basic_label_bit {m n : ℕ} (dimension node : List Bool)
    (hk : dimension.length = m + n) (i : Fin (m + n)) (b : Bool) :
    (bimatrixNodeBasicWord ![dimension, node])[2 * i.val + (if b then 1 else 0)]?.getD false =
      decide (toLex (i, b) ∈ GameTheory.Finite.BimatrixPathBinaryCodec.basic node) :=
  bimatrixNodeBasicWord_bit dimension node hk (toLex (i, b))

private theorem basic_false_bit {m n : ℕ} (dimension node : List Bool)
    (hk : dimension.length = m + n) (i : Fin (m + n)) :
    (bimatrixNodeBasicWord ![dimension, node])[2 * i.val]?.getD false =
      decide (toLex (i, false) ∈ GameTheory.Finite.BimatrixPathBinaryCodec.basic node) :=
  basic_label_bit dimension node hk i false

private theorem basic_true_bit {m n : ℕ} (dimension node : List Bool)
    (hk : dimension.length = m + n) (i : Fin (m + n)) :
    (bimatrixNodeBasicWord ![dimension, node])[2 * i.val + 1]?.getD false =
      decide (toLex (i, true) ∈ GameTheory.Finite.BimatrixPathBinaryCodec.basic node) :=
  basic_label_bit dimension node hk i true

private theorem coverage_iff {m n : ℕ} (dimension node : List Bool)
    (hk : dimension.length = m + n) (d : Fin (m + n)) (hd : d.val = 0) :
    (∀ i < dimension.length, CoveredAt (bimatrixNodeBasicWord ![dimension, node]) i) ↔
      GameTheory.Math.ComplementaryLabels.CoversExcept
        ((GameTheory.Finite.BimatrixPathBinaryCodec.basic (m := m) (n := n) node)ᶜ.map ofLex.toEmbedding) d := by
  constructor
  · intro h i hi
    have hh := h i.val (by simpa only [hk] using i.isLt)
    have hn : i.val ≠ 0 := by intro hz; apply hi; exact Fin.ext (hz.trans hd.symm)
    rcases hh with hz | hf | ht
    · exact (hn hz).elim
    · left
      have hf' : toLex (i, false) ∉ GameTheory.Finite.BimatrixPathBinaryCodec.basic node := by
        rw [basic_false_bit dimension node hk i] at hf
        exact of_decide_eq_false hf
      simpa using hf'
    · right
      have ht' : toLex (i, true) ∉ GameTheory.Finite.BimatrixPathBinaryCodec.basic node := by
        rw [basic_true_bit dimension node hk i] at ht
        exact of_decide_eq_false ht
      simpa using ht'
  · intro h i hi
    by_cases hz : i = 0
    · exact Or.inl hz
    · let label : Fin (m + n) := ⟨i, by simpa only [hk] using hi⟩
      have hne : label ≠ d := by intro he; exact hz ((congrArg Fin.val he).trans hd)
      rcases h label hne with hf | ht
      · right; left
        have hf' : toLex (label, false) ∉ GameTheory.Finite.BimatrixPathBinaryCodec.basic node := by
          simpa using hf
        change (bimatrixNodeBasicWord ![dimension, node])[2 * label.val]?.getD false = false
        rw [basic_false_bit dimension node hk label]
        exact decide_eq_false hf'
      · right; right
        have ht' : toLex (label, true) ∉ GameTheory.Finite.BimatrixPathBinaryCodec.basic node := by
          simpa using ht
        change (bimatrixNodeBasicWord ![dimension, node])[2 * label.val + 1]?.getD false = false
        rw [basic_true_bit dimension node hk label]
        exact decide_eq_false ht'

private theorem index_half {m n : ℕ} (v : GameTheory.Finite.BimatrixVariable m n) :
    (GameTheory.Finite.BimatrixPathBinaryCodec.index v).val / 2 = (ofLex v).1.val := by
  rcases v with ⟨i, b⟩
  change (GameTheory.Finite.BimatrixPathBinaryCodec.index (toLex (i, b))).val / 2 = i.val
  cases b <;> simp [GameTheory.Finite.BimatrixPathBinaryCodec.index, Nat.add_div]

private theorem ports_iff {m n : ℕ} (dimension node : List Bool)
    (hk : dimension.length = m + n) (d : Fin (m + n)) (hd : d.val = 0) :
    (∀ i < 2 * dimension.length, PermittedAt (bimatrixNodeBasicWord ![dimension, node])
      (bimatrixNodeEnteringWord ![dimension, node]) i) ↔
    ∀ v ∈ GameTheory.Finite.BimatrixPathBinaryCodec.enteringSet d node,
      GameTheory.Math.ComplementaryPorts.IsPort
        ((GameTheory.Finite.BimatrixPathBinaryCodec.basic (m := m) (n := n) node)ᶜ.map ofLex.toEmbedding)
        d (ofLex v) := by
  constructor
  · intro h v hv
    have he : (bimatrixNodeEnteringWord ![dimension, node])[
        (GameTheory.Finite.BimatrixPathBinaryCodec.index v).val]?.getD false = true := by
      rw [bimatrixNodeEnteringWord_bit dimension node hk d hd v]
      exact decide_eq_true hv
    have hp := h (GameTheory.Finite.BimatrixPathBinaryCodec.index v).val
      (by simpa only [hk] using (GameTheory.Finite.BimatrixPathBinaryCodec.index v).isLt) he
    have hn : v ∉ GameTheory.Finite.BimatrixPathBinaryCodec.basic node := by
      have hh := hp.1
      rw [bimatrixNodeBasicWord_bit dimension node hk v] at hh
      exact of_decide_eq_false hh
    refine ⟨by simpa using hn, ?_⟩
    rw [index_half v] at hp
    rcases hp.2 with hz | ⟨hf, ht⟩
    · left
      exact Fin.ext (hz.trans hd.symm)
    · right
      constructor
      · have hn' : toLex ((ofLex v).1, false) ∉ GameTheory.Finite.BimatrixPathBinaryCodec.basic node := by
          rw [basic_false_bit dimension node hk (ofLex v).1] at hf
          exact of_decide_eq_false hf
        simpa using hn'
      · have hn' : toLex ((ofLex v).1, true) ∉ GameTheory.Finite.BimatrixPathBinaryCodec.basic node := by
          rw [basic_true_bit dimension node hk (ofLex v).1] at ht
          exact of_decide_eq_false ht
        simpa using hn'
  · intro h i hi he
    let u := GameTheory.Finite.BimatrixPathBinaryCodec.variableAt (m := m) (n := n)
      ⟨i, by simpa only [hk] using hi⟩
    have hui : (GameTheory.Finite.BimatrixPathBinaryCodec.index u).val = i :=
      congrArg Fin.val (GameTheory.Finite.BimatrixPathBinaryCodec.index_variableAt _)
    have he' := bimatrixNodeEnteringWord_bit dimension node hk d hd u
    rw [hui] at he'
    rw [he'] at he
    have hp := h u (of_decide_eq_true he)
    have hn : u ∉ GameTheory.Finite.BimatrixPathBinaryCodec.basic node := by simpa using hp.1
    constructor
    · have hb := bimatrixNodeBasicWord_bit dimension node hk u
      rw [hui] at hb
      rw [hb]
      exact decide_eq_false hn
    · rcases hp.2 with hz | ⟨hf, ht⟩
      · left
        have hh := (congrArg Fin.val hz).trans hd
        exact hh
      · right
        have hf' : toLex ((ofLex u).1, false) ∉ GameTheory.Finite.BimatrixPathBinaryCodec.basic node := by
          simpa using hf
        have ht' : toLex ((ofLex u).1, true) ∉ GameTheory.Finite.BimatrixPathBinaryCodec.basic node := by
          simpa using ht
        constructor
        · change (bimatrixNodeBasicWord ![dimension, node])[2 * (ofLex u).1.val]?.getD false = false
          rw [basic_false_bit dimension node hk (ofLex u).1]
          exact decide_eq_false hf'
        · change (bimatrixNodeBasicWord ![dimension, node])[2 * (ofLex u).1.val + 1]?.getD false = false
          rw [basic_true_bit dimension node hk (ofLex u).1]
          exact decide_eq_false ht'

/-- The syntactic machine agrees with the codec's basis, entering set, and port predicates. -/
theorem bimatrixNodeSyntaxFlag_codec {m n : ℕ} (dimension node : List Bool)
    (hk : dimension.length = m + n) (d : Fin (m + n)) (hd : d.val = 0) :
    bimatrixNodeSyntaxFlag ![dimension, node] = [true] ↔
      node.length = GameTheory.Finite.BimatrixPathBinaryCodec.width m n ∧
      (GameTheory.Finite.BimatrixPathBinaryCodec.basic (m := m) (n := n) node).card = m + n ∧
      (GameTheory.Finite.BimatrixPathBinaryCodec.enteringSet d node).card = 1 ∧
      GameTheory.Math.ComplementaryLabels.CoversExcept
        ((GameTheory.Finite.BimatrixPathBinaryCodec.basic (m := m) (n := n) node)ᶜ.map ofLex.toEmbedding) d ∧
      ∀ v ∈ GameTheory.Finite.BimatrixPathBinaryCodec.enteringSet d node,
        GameTheory.Math.ComplementaryPorts.IsPort
          ((GameTheory.Finite.BimatrixPathBinaryCodec.basic (m := m) (n := n) node)ᶜ.map ofLex.toEmbedding)
          d (ofLex v) := by
  rw [bimatrixNodeSyntaxFlag_value]
  simp only [List.cons.injEq, and_true,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · intro h
    have hp := of_decide_eq_true h
    rw [coverage_iff dimension node hk d hd, ports_iff dimension node hk d hd,
      bimatrixNodeBasicWord_membership dimension node hk,
      bimatrixNodeEnteringWord_membership dimension node hk d hd,
      GameTheory.Finite.BimatrixPathBinaryCodec.membershipWord_count,
      GameTheory.Finite.BimatrixPathBinaryCodec.membershipWord_count] at hp
    simpa only [hk, GameTheory.Finite.BimatrixPathBinaryCodec.width] using hp
  · intro h
    apply decide_eq_true
    rw [coverage_iff dimension node hk d hd, ports_iff dimension node hk d hd,
      bimatrixNodeBasicWord_membership dimension node hk,
      bimatrixNodeEnteringWord_membership dimension node hk d hd,
      GameTheory.Finite.BimatrixPathBinaryCodec.membershipWord_count,
      GameTheory.Finite.BimatrixPathBinaryCodec.membershipWord_count]
    simpa only [hk, GameTheory.Finite.BimatrixPathBinaryCodec.width] using h

end GameTheory.Complexity.Backend
