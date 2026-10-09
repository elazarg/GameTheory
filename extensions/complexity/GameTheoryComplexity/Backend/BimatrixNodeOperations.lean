import GameTheoryComplexity.Backend.BimatrixNodeWord

/-! Certified binary operations on complementary-path node fields.

Unary rulers identify variables in canonical label/kind order. Exchange replaces
one basis membership bit and enters the leaving variable; switching changes the
entering kind at a duplicated nonzero label. Both operations preserve malformed
word lengths by fixing words whose width differs from the supplied dimension.
The semantic theorems identify their outputs with the existing canonical port
operations, without computing rational inverses or choosing an order instance.
-/

namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham

/-- Assemble unmasked membership fields using the canonical source masks. -/
def bimatrixNodeAssemble (v : Fin 3 → List Bool) : List Bool :=
  bimatrixNodeBasicWord ![v 0, v 1] ++
    bimatrixNodeEnteringWord ![v 0, ((v 0) ++ (v 0)) ++ v 2]

theorem bimatrixNodeAssemble_cobham : Cobham bimatrixNodeAssemble :=
  Cobham.appendFn (Cobham.comp₂ bimatrixNodeBasicWord_cobham (.proj 0) (.proj 1))
    (Cobham.comp₂ bimatrixNodeEnteringWord_cobham (.proj 0)
      (Cobham.appendFn (Cobham.appendFn (.proj 0) (.proj 0)) (.proj 2)))

@[simp] theorem bimatrixNodeAssemble_length (v : Fin 3 → List Bool) :
    (bimatrixNodeAssemble v).length = 4 * (v 0).length := by
  simp [bimatrixNodeAssemble]
  omega

theorem bimatrixNodeAssemble_value (v : Fin 3 → List Bool) :
    bimatrixNodeAssemble v =
      (List.range (2 * (v 0).length)).map
        (fun i => xor ((v 1)[i]?.getD false) (!(decide (i % 2 = 1)))) ++
      (List.range (2 * (v 0).length)).map
        (fun i => xor ((v 2)[i]?.getD false) (decide (i = 1))) := by
  simp only [bimatrixNodeAssemble, bimatrixNodeBasicWord_value, bimatrixNodeEnteringWord_value,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  congr 2
  funext i
  rw [List.getElem?_append_right (by simp only [List.length_append]; omega)]
  simp only [List.length_append, ← two_mul, Nat.add_sub_cancel_left]

private theorem assemble_bit (v : Fin 3 → List Bool) (i : ℕ) (hi : i < 4 * (v 0).length) :
    (bimatrixNodeAssemble v)[i]?.getD false =
      if i < 2 * (v 0).length then xor ((v 1)[i]?.getD false) (!(decide (i % 2 = 1)))
      else xor ((v 2)[i - 2 * (v 0).length]?.getD false) (decide (i - 2 * (v 0).length = 1)) := by
  rw [bimatrixNodeAssemble_value]
  simp only [List.getElem?_append, List.length_map, List.length_range,
    List.getElem?_map]
  by_cases hb : i < 2 * (v 0).length
  · simp [hb]
  · have he : i - 2 * (v 0).length < 2 * (v 0).length := by omega
    simp [hb, he]

private theorem basic_bit (v : Fin 2 → List Bool) (i : ℕ) (hi : i < 2 * (v 0).length) :
    (bimatrixNodeBasicWord v)[i]?.getD false = xor ((v 1)[i]?.getD false) (!(decide (i % 2 = 1))) := by
  rw [bimatrixNodeBasicWord_value]
  simp [hi]

private theorem entering_bit (v : Fin 2 → List Bool) (i : ℕ) (hi : i < 2 * (v 0).length) :
    (bimatrixNodeEnteringWord v)[i]?.getD false =
      xor ((v 1)[2 * (v 0).length + i]?.getD false) (decide (i = 1)) := by
  rw [bimatrixNodeEnteringWord_value]
  simp [hi]

/-- Applying the source masks twice restores every correctly sized word. -/
theorem bimatrixNodeAssemble_roundtrip (v : Fin 2 → List Bool) (hv : (v 1).length = 4 * (v 0).length) :
    bimatrixNodeAssemble ![v 0, bimatrixNodeBasicWord v, bimatrixNodeEnteringWord v] = v 1 := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < 4 * (v 0).length
  · have hiA : i < (bimatrixNodeAssemble ![v 0, bimatrixNodeBasicWord v, bimatrixNodeEnteringWord v]).length := by
      simpa only [bimatrixNodeAssemble_length, Matrix.cons_val_zero] using hi
    have hiN : i < (v 1).length := by omega
    have hbit : (bimatrixNodeAssemble ![v 0, bimatrixNodeBasicWord v, bimatrixNodeEnteringWord v])[i]?.getD false =
        (v 1)[i]?.getD false := by
      rw [assemble_bit _ i (by exact hi)]
      change (if i < 2 * (v 0).length then
        xor ((bimatrixNodeBasicWord v)[i]?.getD false) (!(decide (i % 2 = 1)))
        else xor ((bimatrixNodeEnteringWord v)[i - 2 * (v 0).length]?.getD false)
          (decide (i - 2 * (v 0).length = 1))) = (v 1)[i]?.getD false
      by_cases hb : i < 2 * (v 0).length
      · rw [ite_eq_left hb, basic_bit v i hb]
        simp
      · have he : i - 2 * (v 0).length < 2 * (v 0).length := by omega
        rw [ite_eq_right hb, entering_bit v _ he]
        have hadd : 2 * (v 0).length + (i - 2 * (v 0).length) = i := by omega
        rw [hadd]
        simp
    rw [List.getElem?_eq_getElem hiA, List.getElem?_eq_getElem hiN] at hbit ⊢
    exact congrArg some hbit
  · simp [hv, hi]

private theorem assemble_basic_bit (v : Fin 3 → List Bool) (i : ℕ) (hi : i < 2 * (v 0).length) :
    (bimatrixNodeBasicWord ![v 0, bimatrixNodeAssemble v])[i]?.getD false = (v 1)[i]?.getD false := by
  rw [basic_bit _ i (by exact hi)]
  change xor ((bimatrixNodeAssemble v)[i]?.getD false) (!(decide (i % 2 = 1))) = _
  rw [assemble_bit v i (by omega)]
  rw [ite_eq_left hi]
  simp

private theorem assemble_entering_bit (v : Fin 3 → List Bool) (i : ℕ) (hi : i < 2 * (v 0).length) :
    (bimatrixNodeEnteringWord ![v 0, bimatrixNodeAssemble v])[i]?.getD false = (v 2)[i]?.getD false := by
  rw [entering_bit _ i (by exact hi)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [assemble_bit v (2 * (v 0).length + i) (by omega), ite_eq_right (by omega)]
  simp

private theorem flagTable_bit {p : ℕ} (term : (Fin (p + 1) → List Bool) → List Bool)
    (params : Fin p → List Bool) (f : ℕ → Bool)
    (ht : ∀ r, term (Fin.cons r params) = [f r.length])
    (clock : List Bool) (i : ℕ) (hi : i < clock.length) :
    (binarySignedTable term clock [false] params)[i]?.getD false = f i := by
  rw [binarySignedTable_flags term params f ht clock]
  simp [hi]

private def exchangeBit (v : Fin 4 → List Bool) : List Bool :=
  caseBit₀ (lenEqFlag (v 0) (v 2)) [false]
    (orBit (lenEqFlag (v 0) (v 3)) (bitAt (v 0) (v 1)))

private def oneHotBit (v : Fin 2 → List Bool) : List Bool := lenEqFlag (v 0) (v 1)

private theorem exchangeBit_cobham : Cobham exchangeBit :=
  Cobham.iteFn (lenEqFlag_mem (.proj 0) (.proj 2)) (Cobham.const [false])
    (Cobham.orFn (lenEqFlag_mem (.proj 0) (.proj 3))
      (Cobham.comp₂ Cobham.bitAtFn (.proj 0) (.proj 1)))

private theorem oneHotBit_cobham : Cobham oneHotBit := lenEqFlag_mem (.proj 0) (.proj 1)

private def exchangeBasic (v : Fin 4 → List Bool) : List Bool :=
  binarySignedTable exchangeBit ((v 0) ++ (v 0)) [false]
    ![bimatrixNodeBasicWord ![v 0, v 1], v 2, v 3]

private def exchangeEntering (v : Fin 4 → List Bool) : List Bool :=
  binarySignedTable oneHotBit ((v 0) ++ (v 0)) [false] ![v 2]

private theorem exchangeBasic_cobham : Cobham exchangeBasic := by
  have h := Cobham.comp (binarySignedTable_cobham exchangeBit_cobham)
    (gs := fun i => fun v : Fin 4 → List Bool =>
      ![(v 0) ++ (v 0), [false], bimatrixNodeBasicWord ![v 0, v 1], v 2, v 3] i)
    (fun i => by
      fin_cases i
      · exact Cobham.appendFn (.proj 0) (.proj 0)
      · exact Cobham.const [false]
      · exact Cobham.comp₂ bimatrixNodeBasicWord_cobham (.proj 0) (.proj 1)
      · exact .proj 2
      · exact .proj 3)
  exact h.of_eq fun _ => rfl

private theorem exchangeEntering_cobham : Cobham exchangeEntering :=
  Cobham.comp₃ (binarySignedTable_cobham oneHotBit_cobham)
    (Cobham.appendFn (.proj 0) (.proj 0)) (Cobham.const [false]) (.proj 2)

/-- Replace the leaving basis position by the entering position and reverse the port.
Inputs are dimension, node, leaving-position ruler, and entering-position ruler.
Malformed lengths are preserved. -/
def bimatrixNodeExchangeWord (v : Fin 4 → List Bool) : List Bool :=
  caseBit₀ (lenEqFlag (v 1) (((v 0) ++ (v 0)) ++ ((v 0) ++ (v 0))))
    (bimatrixNodeAssemble ![v 0, exchangeBasic v, exchangeEntering v]) (v 1)

theorem bimatrixNodeExchangeWord_cobham : Cobham bimatrixNodeExchangeWord :=
  Cobham.iteFn
    (lenEqFlag_mem (.proj 1) (Cobham.appendFn (Cobham.appendFn (.proj 0) (.proj 0))
      (Cobham.appendFn (.proj 0) (.proj 0))))
    (Cobham.comp₃ bimatrixNodeAssemble_cobham (.proj 0) exchangeBasic_cobham exchangeEntering_cobham)
    (.proj 1)

theorem bimatrixNodeExchangeWord_mem_FPn : FPn bimatrixNodeExchangeWord :=
  cobham_iff_FPn.mp bimatrixNodeExchangeWord_cobham

private theorem case_head (x a b : List Bool) : caseBit₀ x a b = if x.headD false then a else b := by
  cases x with
  | nil => rfl
  | cons c x => cases c <;> rfl

private theorem lenEq_word (a b : List Bool) : lenEqFlag a b = [decide (a.length = b.length)] := by
  rcases lenEqFlag_flag a b with h | h
  · rw [h]; simp [(lenEqFlag_eq_true_iff a b).mp h]
  · rw [h]
    have hn : a.length ≠ b.length := by
      intro he
      have := (lenEqFlag_eq_true_iff a b).mpr he
      simp [h] at this
    simp [hn]



private theorem exchangeBit_value (r basic leaving entering : List Bool) :
    exchangeBit ![r, basic, leaving, entering] =
      [if r.length = leaving.length then false else
        decide (r.length = entering.length) || basic[r.length]?.getD false] := by
  change caseBit₀ (lenEqFlag r leaving) [false]
    (orBit (lenEqFlag r entering) (bitAt r basic)) = _
  rw [lenEq_word, lenEq_word, bitAt_getElem?]
  by_cases hl : r.length = leaving.length
  · rw [decide_eq_true hl, ite_eq_left hl]
    rfl
  · rw [decide_eq_false hl, ite_eq_right hl]
    cases decide (r.length = entering.length) <;> cases basic[r.length]?.getD false <;> rfl

private theorem exchangeBasic_bit (v : Fin 4 → List Bool) (i : ℕ) (hi : i < 2 * (v 0).length) :
    (exchangeBasic v)[i]?.getD false = if i = (v 2).length then false else
      decide (i = (v 3).length) || (bimatrixNodeBasicWord ![v 0, v 1])[i]?.getD false := by
  exact flagTable_bit exchangeBit ![bimatrixNodeBasicWord ![v 0, v 1], v 2, v 3]
    (fun i => if i = (v 2).length then false else
      decide (i = (v 3).length) || (bimatrixNodeBasicWord ![v 0, v 1])[i]?.getD false)
    (fun r => exchangeBit_value r _ _ _) ((v 0) ++ (v 0)) i (by simpa only [List.length_append, ← two_mul] using hi)

private theorem oneHotBit_value (r target : List Bool) :
    oneHotBit ![r, target] = [decide (r.length = target.length)] := lenEq_word r target

private theorem exchangeEntering_bit (v : Fin 4 → List Bool) (i : ℕ) (hi : i < 2 * (v 0).length) :
    (exchangeEntering v)[i]?.getD false = decide (i = (v 2).length) := by
  exact flagTable_bit oneHotBit ![v 2] (fun i => decide (i = (v 2).length))
    (fun r => oneHotBit_value r _) ((v 0) ++ (v 0)) i
    (by simpa only [List.length_append, ← two_mul] using hi)

theorem bimatrixNodeExchangeWord_length (v : Fin 4 → List Bool) :
    (bimatrixNodeExchangeWord v).length = (v 1).length := by
  rw [bimatrixNodeExchangeWord, lenEq_word, case_head]
  simp only [List.headD_cons, decide_eq_true_eq]
  split
  · rw [bimatrixNodeAssemble_length]
    simp only [Matrix.cons_val_zero, List.length_append] at *
    omega
  · rfl

private theorem exchangeWord_valid (v : Fin 4 → List Bool) (hv : (v 1).length = 4 * (v 0).length) :
    bimatrixNodeExchangeWord v = bimatrixNodeAssemble ![v 0, exchangeBasic v, exchangeEntering v] := by
  rw [bimatrixNodeExchangeWord, lenEq_word, case_head]
  simp only [List.headD_cons, decide_eq_true_eq]
  have h : (v 1).length = (((v 0) ++ (v 0)) ++ ((v 0) ++ (v 0))).length := by
    simp only [List.length_append]
    omega
  exact ite_eq_left h

private theorem index_val_eq {m n : ℕ} (u v : GameTheory.Finite.BimatrixVariable m n) :
    (GameTheory.Finite.BimatrixPathBinaryCodec.index u).val =
      (GameTheory.Finite.BimatrixPathBinaryCodec.index v).val ↔ u = v := by
  constructor
  · intro h
    exact GameTheory.Finite.BimatrixPathBinaryCodec.index_strictMono.injective (Fin.ext h)
  · rintro rfl
    rfl

/-- Bit replacement implements the existing finite basis-set exchange. -/
theorem bimatrixNodeExchangeWord_basic {m n : ℕ} (dimension node leaving entering : List Bool)
    (hk : dimension.length = m + n) (hw : node.length = 4 * dimension.length)
    (l e : GameTheory.Finite.BimatrixVariable m n)
    (hl : leaving.length = (GameTheory.Finite.BimatrixPathBinaryCodec.index l).val)
    (he : entering.length = (GameTheory.Finite.BimatrixPathBinaryCodec.index e).val)
    (hne : l ≠ e) :
    GameTheory.Finite.BimatrixPathBinaryCodec.basic
      (bimatrixNodeExchangeWord ![dimension, node, leaving, entering]) =
      GameTheory.Math.FiniteBasisExchange.exchange
        (GameTheory.Finite.BimatrixPathBinaryCodec.basic node) l e := by
  ext u
  apply decide_eq_decide.mp
  all_goals try infer_instance
  rw [← bimatrixNodeBasicWord_bit dimension _ hk u]
  rw [exchangeWord_valid _ hw]
  have hi : (GameTheory.Finite.BimatrixPathBinaryCodec.index u).val < 2 * dimension.length := by
    simpa only [hk] using (GameTheory.Finite.BimatrixPathBinaryCodec.index u).isLt
  refine (assemble_basic_bit
    ![dimension, exchangeBasic ![dimension, node, leaving, entering],
      exchangeEntering ![dimension, node, leaving, entering]] _ hi).trans ?_
  change (exchangeBasic ![dimension, node, leaving, entering])[
    (GameTheory.Finite.BimatrixPathBinaryCodec.index u).val]?.getD false = _
  rw [exchangeBasic_bit _ _ hi]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three]
  change (if (GameTheory.Finite.BimatrixPathBinaryCodec.index u).val = leaving.length then false else
        decide ((GameTheory.Finite.BimatrixPathBinaryCodec.index u).val = entering.length) ||
          (bimatrixNodeBasicWord ![dimension, node])[(GameTheory.Finite.BimatrixPathBinaryCodec.index u).val]?.getD false) = _
  rw [bimatrixNodeBasicWord_bit dimension node hk u]
  simp only [hl, he, index_val_eq, GameTheory.Math.FiniteBasisExchange.mem_exchange]
  by_cases hul : u = l
  · subst u
    simp [hne]
  · by_cases hue : u = e <;> simp [hul, hue, hne.symm]

/-- The opposite port enters precisely the variable that left the basis. -/
theorem bimatrixNodeExchangeWord_entering {m n : ℕ} (dimension node leaving entering : List Bool)
    (hk : dimension.length = m + n) (hw : node.length = 4 * dimension.length)
    (d : Fin (m + n)) (hd : d.val = 0) (l : GameTheory.Finite.BimatrixVariable m n)
    (hl : leaving.length = (GameTheory.Finite.BimatrixPathBinaryCodec.index l).val) :
    GameTheory.Finite.BimatrixPathBinaryCodec.enteringSet d
      (bimatrixNodeExchangeWord ![dimension, node, leaving, entering]) = {l} := by
  ext u
  apply decide_eq_decide.mp
  all_goals try infer_instance
  rw [← bimatrixNodeEnteringWord_bit dimension _ hk d hd u]
  rw [exchangeWord_valid _ hw]
  have hi : (GameTheory.Finite.BimatrixPathBinaryCodec.index u).val < 2 * dimension.length := by
    simpa only [hk] using (GameTheory.Finite.BimatrixPathBinaryCodec.index u).isLt
  refine (assemble_entering_bit
    ![dimension, exchangeBasic ![dimension, node, leaving, entering],
      exchangeEntering ![dimension, node, leaving, entering]] _ hi).trans ?_
  change (exchangeEntering ![dimension, node, leaving, entering])[
    (GameTheory.Finite.BimatrixPathBinaryCodec.index u).val]?.getD false = _
  rw [exchangeEntering_bit _ _ hi]
  change decide ((GameTheory.Finite.BimatrixPathBinaryCodec.index u).val = leaving.length) = decide (u ∈ ({l} : Finset _))
  simp only [hl, index_val_eq, Finset.mem_singleton]

private def switchPosition (v : Fin 3 → List Bool) : List Bool :=
  let label := binaryHalfRuler (v 2)
  let basic := bimatrixNodeBasicWord ![v 0, v 1]
  caseBit₀ (andBit (notBit (lenEqFlag label []))
    (notBit (orBit (bitAt (label ++ label) basic) (bitAt (true :: (label ++ label)) basic))))
    (caseBit₀ (binaryLengthParity (v 2)) (v 2).tail (true :: v 2)) (v 2)

private theorem switchPosition_cobham : Cobham switchPosition := by
  have hl : Cobham fun v : Fin 3 → List Bool => binaryHalfRuler (v 2) :=
    Cobham.comp binaryHalfRuler_cobham fun _ => .proj 2
  have hb : Cobham fun v : Fin 3 → List Bool => bimatrixNodeBasicWord ![v 0, v 1] :=
    Cobham.comp₂ bimatrixNodeBasicWord_cobham (.proj 0) (.proj 1)
  exact Cobham.iteFn
    (Cobham.andFn (Cobham.notFn (lenEqFlag_mem hl (Cobham.const [])))
      (Cobham.notFn (Cobham.orFn
        (Cobham.comp₂ Cobham.bitAtFn (Cobham.appendFn hl hl) hb)
        (Cobham.comp₂ Cobham.bitAtFn
          (Cobham.appendFn (Cobham.const [true]) (Cobham.appendFn hl hl)) hb))))
    (Cobham.iteFn (Cobham.comp binaryLengthParity_cobham fun _ => .proj 2)
      (Cobham.tailFn (.proj 2)) (Cobham.appendFn (Cobham.const [true]) (.proj 2))) (.proj 2)

private def switchEntering (v : Fin 3 → List Bool) : List Bool :=
  binarySignedTable oneHotBit ((v 0) ++ (v 0)) [false] ![switchPosition v]

private theorem switchEntering_cobham : Cobham switchEntering :=
  Cobham.comp₃ (binarySignedTable_cobham oneHotBit_cobham)
    (Cobham.appendFn (.proj 0) (.proj 0)) (Cobham.const [false]) switchPosition_cobham

/-- Switch a duplicated-label port's kind, retaining dropped-label endpoints.
Inputs are dimension, node, and entering-position ruler. Malformed lengths are preserved. -/
def bimatrixNodeSwitchWord (v : Fin 3 → List Bool) : List Bool :=
  caseBit₀ (lenEqFlag (v 1) (((v 0) ++ (v 0)) ++ ((v 0) ++ (v 0))))
    (bimatrixNodeAssemble ![v 0, bimatrixNodeBasicWord ![v 0, v 1], switchEntering v]) (v 1)

theorem bimatrixNodeSwitchWord_cobham : Cobham bimatrixNodeSwitchWord :=
  Cobham.iteFn
    (lenEqFlag_mem (.proj 1) (Cobham.appendFn (Cobham.appendFn (.proj 0) (.proj 0))
      (Cobham.appendFn (.proj 0) (.proj 0))))
    (Cobham.comp₃ bimatrixNodeAssemble_cobham (.proj 0)
      (Cobham.comp₂ bimatrixNodeBasicWord_cobham (.proj 0) (.proj 1)) switchEntering_cobham)
    (.proj 1)

theorem bimatrixNodeSwitchWord_mem_FPn : FPn bimatrixNodeSwitchWord :=
  cobham_iff_FPn.mp bimatrixNodeSwitchWord_cobham

theorem bimatrixNodeSwitchWord_length (v : Fin 3 → List Bool) :
    (bimatrixNodeSwitchWord v).length = (v 1).length := by
  rw [bimatrixNodeSwitchWord, lenEq_word, case_head]
  simp only [List.headD_cons, decide_eq_true_eq]
  split
  · rw [bimatrixNodeAssemble_length]
    simp only [Matrix.cons_val_zero, List.length_append] at *
    omega
  · rfl

private theorem switchPosition_length (v : Fin 3 → List Bool) :
    (switchPosition v).length =
      if (v 2).length / 2 ≠ 0 ∧
          (bimatrixNodeBasicWord ![v 0, v 1])[2 * ((v 2).length / 2)]?.getD false = false ∧
          (bimatrixNodeBasicWord ![v 0, v 1])[2 * ((v 2).length / 2) + 1]?.getD false = false then
        if (v 2).length % 2 = 1 then (v 2).length - 1 else (v 2).length + 1
      else (v 2).length := by
  rw [switchPosition, lenEq_word, bitAt_getElem?, bitAt_getElem?, binaryLengthParity_value]
  simp only [binaryHalfRuler_length, List.length_append, List.length_cons, List.length_nil]
  rw [case_head, case_head]
  simp only [andBit, notBit, orBit, List.headD_cons,
    ]
  cases h₀ : (bimatrixNodeBasicWord ![v 0, v 1])[(v 2).length / 2 + (v 2).length / 2]?.getD false <;>
    cases h₁ : (bimatrixNodeBasicWord ![v 0, v 1])[(v 2).length / 2 + (v 2).length / 2 + 1]?.getD false <;>
    by_cases hz : (v 2).length / 2 = 0 <;>
    by_cases hp : (v 2).length % 2 = 1 <;>
    simp [hz, hp, show 2 * ((v 2).length / 2) = (v 2).length / 2 + (v 2).length / 2 by omega, h₀, h₁]
private theorem switchPosition_port {m n : ℕ} {A B : Fin m → Fin n → ℤ}
    {d : Fin (m + n)} (dimension node pointer : List Bool)
    (hk : dimension.length = m + n) (hd : d.val = 0)
    (port : GameTheory.Finite.BimatrixPathPort A B d)
    (hb : GameTheory.Finite.BimatrixPathBinaryCodec.basic node = port.node.basis.basic)
    (hp : pointer.length = (GameTheory.Finite.BimatrixPathBinaryCodec.index port.entering).val) :
    (switchPosition ![dimension, node, pointer]).length =
      (GameTheory.Finite.BimatrixPathBinaryCodec.index port.switch.entering).val := by
  rw [switchPosition_length]
  have hl : pointer.length / 2 = (ofLex port.entering).1.val := by
    rw [hp]
    simp only [GameTheory.Finite.BimatrixPathBinaryCodec.index]
    cases hkind : (ofLex port.entering).2 <;> simp [Nat.add_div]
  have hpar : pointer.length % 2 = if (ofLex port.entering).2 then 1 else 0 := by
    rw [hp]
    simp only [GameTheory.Finite.BimatrixPathBinaryCodec.index]
    cases hkind : (ofLex port.entering).2 <;> simp [Nat.add_mod]
  change (if pointer.length / 2 ≠ 0 ∧
      (bimatrixNodeBasicWord ![dimension, node])[2 * (pointer.length / 2)]?.getD false = false ∧
      (bimatrixNodeBasicWord ![dimension, node])[2 * (pointer.length / 2) + 1]?.getD false = false then
    if pointer.length % 2 = 1 then pointer.length - 1 else pointer.length + 1
    else pointer.length) = _
  by_cases hz : (ofLex port.entering).1 = d
  · have hzero : pointer.length / 2 = 0 := by rw [hl, hz, hd]
    simp only [hzero, ne_eq, not_true_eq_false, false_and, ↓reduceIte]
    change pointer.length = (GameTheory.Finite.BimatrixPathBinaryCodec.index
      (toLex (GameTheory.Math.ComplementaryPorts.switch port.node.basis.nonbasic d (ofLex port.entering)))).val
    simpa only [GameTheory.Math.ComplementaryPorts.switch, hz, ↓reduceIte, toLex_ofLex] using hp
  · have hzero : pointer.length / 2 ≠ 0 := by
      rw [hl]
      intro h
      exact hz (Fin.ext (h.trans hd.symm))
    have hpairs := port.permitted.2.resolve_left hz
    have hf : toLex ((ofLex port.entering).1, false) ∉ port.node.basis.basic :=
      (port.node.basis.mem_nonbasic _).mp hpairs.1
    have ht : toLex ((ofLex port.entering).1, true) ∉ port.node.basis.basic :=
      (port.node.basis.mem_nonbasic _).mp hpairs.2
    have hbf := bimatrixNodeBasicWord_bit dimension node hk (toLex ((ofLex port.entering).1, false))
    have hbt := bimatrixNodeBasicWord_bit dimension node hk (toLex ((ofLex port.entering).1, true))
    simp only [GameTheory.Finite.BimatrixPathBinaryCodec.index, ofLex_toLex, Bool.false_eq_true,
      ↓reduceIte, add_zero, hb, hf, decide_false] at hbf
    simp only [GameTheory.Finite.BimatrixPathBinaryCodec.index, ofLex_toLex, ↓reduceIte,
      hb, ht, decide_false] at hbt
    rw [hl, hbf, hbt]
    simp only [← hl, and_true]
    rw [ite_eq_left hzero]
    change (if pointer.length % 2 = 1 then pointer.length - 1 else pointer.length + 1) =
      (GameTheory.Finite.BimatrixPathBinaryCodec.index
        (toLex (GameTheory.Math.ComplementaryPorts.switch port.node.basis.nonbasic d (ofLex port.entering)))).val
    rw [GameTheory.Math.ComplementaryPorts.switch, ite_eq_right hz]
    simp only [GameTheory.Finite.BimatrixPathBinaryCodec.index, ofLex_toLex]
    rw [hpar, hp]
    simp only [GameTheory.Finite.BimatrixPathBinaryCodec.index]
    cases (ofLex port.entering).2 <;> simp
private theorem switchWord_valid (v : Fin 3 → List Bool)
    (hw : (v 1).length = 4 * (v 0).length) :
    bimatrixNodeSwitchWord v = bimatrixNodeAssemble
      ![v 0, bimatrixNodeBasicWord ![v 0, v 1], switchEntering v] := by
  rw [bimatrixNodeSwitchWord, lenEq_word, case_head]
  simp only [List.length_append, List.headD_cons, hw]
  have heq : 4 * (v 0).length = (v 0).length + (v 0).length + ((v 0).length + (v 0).length) := by omega
  simp only [heq, decide_true, ↓reduceIte]

/-- Switching retains the entire unmasked basis field. -/
theorem bimatrixNodeSwitchWord_basic {m n : ℕ} (dimension node pointer : List Bool)
    (hk : dimension.length = m + n) (hw : node.length = 4 * dimension.length) :
    GameTheory.Finite.BimatrixPathBinaryCodec.basic (m := m) (n := n)
      (bimatrixNodeSwitchWord ![dimension, node, pointer]) =
      GameTheory.Finite.BimatrixPathBinaryCodec.basic node := by
  ext u
  apply decide_eq_decide.mp
  all_goals try infer_instance
  rw [← bimatrixNodeBasicWord_bit dimension _ hk u, switchWord_valid _ hw]
  have hi : (GameTheory.Finite.BimatrixPathBinaryCodec.index u).val < 2 * dimension.length := by
    simpa only [hk] using (GameTheory.Finite.BimatrixPathBinaryCodec.index u).isLt
  exact (assemble_basic_bit
    ![dimension, bimatrixNodeBasicWord ![dimension, node], switchEntering ![dimension, node, pointer]]
    _ hi).trans (bimatrixNodeBasicWord_bit dimension node hk u)

/-- A permitted port switches to the canonical twin variable, fixing dropped-label endpoints. -/
theorem bimatrixNodeSwitchWord_entering {m n : ℕ} {A B : Fin m → Fin n → ℤ}
    {d : Fin (m + n)} (dimension node pointer : List Bool)
    (hk : dimension.length = m + n) (hw : node.length = 4 * dimension.length)
    (hd : d.val = 0) (port : GameTheory.Finite.BimatrixPathPort A B d)
    (hb : GameTheory.Finite.BimatrixPathBinaryCodec.basic node = port.node.basis.basic)
    (hp : pointer.length = (GameTheory.Finite.BimatrixPathBinaryCodec.index port.entering).val) :
    GameTheory.Finite.BimatrixPathBinaryCodec.enteringSet d
      (bimatrixNodeSwitchWord ![dimension, node, pointer]) = {port.switch.entering} := by
  ext u
  apply decide_eq_decide.mp
  all_goals try infer_instance
  rw [← bimatrixNodeEnteringWord_bit dimension _ hk d hd u, switchWord_valid _ hw]
  have hi : (GameTheory.Finite.BimatrixPathBinaryCodec.index u).val < 2 * dimension.length := by
    simpa only [hk] using (GameTheory.Finite.BimatrixPathBinaryCodec.index u).isLt
  refine (assemble_entering_bit
    ![dimension, bimatrixNodeBasicWord ![dimension, node], switchEntering ![dimension, node, pointer]]
    _ hi).trans ?_
  change (switchEntering ![dimension, node, pointer])[
    (GameTheory.Finite.BimatrixPathBinaryCodec.index u).val]?.getD false = _
  rw [switchEntering]
  refine (flagTable_bit oneHotBit _ (fun i => decide (i = (switchPosition ![dimension, node, pointer]).length))
    (fun r => oneHotBit_value r _) _ _ (by simpa only [Matrix.cons_val_zero, List.length_append, two_mul] using hi)).trans ?_
  rw [switchPosition_port dimension node pointer hk hd port hb hp]
  simp only [index_val_eq, Finset.mem_singleton]

/-- The executable switch agrees with switching a valid canonical path port. -/
theorem bimatrixNodeSwitchWord_encode {m n : ℕ} {A B : Fin m → Fin n → ℤ}
    {d : Fin (m + n)} (dimension pointer : List Bool) (hk : dimension.length = m + n)
    (hd : d.val = 0) (port : GameTheory.Finite.BimatrixPathPort A B d)
    (hp : pointer.length = (GameTheory.Finite.BimatrixPathBinaryCodec.index port.entering).val) :
    bimatrixNodeSwitchWord ![dimension, GameTheory.Finite.BimatrixPathBinaryCodec.encode port, pointer] =
      GameTheory.Finite.BimatrixPathBinaryCodec.encode port.switch := by
  apply Eq.symm
  apply GameTheory.Finite.BimatrixPathBinaryCodec.encode_eq_of_fields
  · rw [bimatrixNodeSwitchWord_length]
    exact GameTheory.Finite.BimatrixPathBinaryCodec.encode_length port
  · rw [bimatrixNodeSwitchWord_basic dimension _ pointer hk
      (by simp only [GameTheory.Finite.BimatrixPathBinaryCodec.encode_length,
        GameTheory.Finite.BimatrixPathBinaryCodec.width, hk])]
    exact GameTheory.Finite.BimatrixPathBinaryCodec.basic_encode port
  · exact bimatrixNodeSwitchWord_entering dimension _ pointer hk
      (by simp only [GameTheory.Finite.BimatrixPathBinaryCodec.encode_length,
        GameTheory.Finite.BimatrixPathBinaryCodec.width, hk]) hd port
      (GameTheory.Finite.BimatrixPathBinaryCodec.basic_encode port) hp
/-- The executable basis exchange agrees with the canonical feasible pivot port. -/
theorem bimatrixNodeExchangeWord_encode {m n : ℕ} {A B : Fin m → Fin n → ℤ}
    {d : Fin (m + n)} (dimension leaving entering : List Bool)
    (hk : dimension.length = m + n) (hd : d.val = 0)
    (port : GameTheory.Finite.BimatrixPathPort A B d)
    (hm : 0 < m) (hn : 0 < n) (hA : ∀ i j, 0 < A i j) (hB : ∀ i j, 0 < B i j)
    (hl : leaving.length = (GameTheory.Finite.BimatrixPathBinaryCodec.index
      (port.toPivotPort.leavingVariable (port.toPivotPort.leavingRow hm hn hA hB))).val)
    (he : entering.length = (GameTheory.Finite.BimatrixPathBinaryCodec.index port.entering).val) :
    bimatrixNodeExchangeWord
      ![dimension, GameTheory.Finite.BimatrixPathBinaryCodec.encode port, leaving, entering] =
      GameTheory.Finite.BimatrixPathBinaryCodec.encode (port.pivot hm hn hA hB) := by
  let l := port.toPivotPort.leavingVariable (port.toPivotPort.leavingRow hm hn hA hB)
  have hne : l ≠ port.entering := by
    intro h
    apply port.toPivotPort.nonbasic
    change port.entering ∈ port.node.basis.basic
    rw [← h]
    exact Finset.orderEmbOfFin_mem _ _ _
  have hw : (GameTheory.Finite.BimatrixPathBinaryCodec.encode port).length = 4 * dimension.length := by
    simp only [GameTheory.Finite.BimatrixPathBinaryCodec.encode_length,
      GameTheory.Finite.BimatrixPathBinaryCodec.width, hk]
  apply Eq.symm
  apply GameTheory.Finite.BimatrixPathBinaryCodec.encode_eq_of_fields
  · rw [bimatrixNodeExchangeWord_length]
    exact GameTheory.Finite.BimatrixPathBinaryCodec.encode_length port
  · rw [bimatrixNodeExchangeWord_basic dimension _ leaving entering hk hw l port.entering hl he hne,
      GameTheory.Finite.BimatrixPathBinaryCodec.basic_encode]
    rfl
  · exact bimatrixNodeExchangeWord_entering dimension _ leaving entering hk hw d hd l hl
end GameTheory.Complexity.Backend
