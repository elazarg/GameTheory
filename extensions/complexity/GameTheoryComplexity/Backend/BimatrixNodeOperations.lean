module

public import GameTheoryComplexity.Backend.BimatrixNodeWord

@[expose] public section

/-! Certified binary operations on complementary-path node fields.

Unary rulers identify variables in canonical label/kind order. Exchange replaces
one basis membership bit and enters the leaving variable; switching changes the
entering kind at a duplicated nonzero label. Both operations preserve malformed
word lengths by fixing words whose width differs from the supplied dimension.
The semantic theorems identify their outputs with the existing canonical port
operations, without computing rational inverses or choosing an order instance.
-/

namespace GameTheory.Complexity.Backend
open Cslib.BitString Turing.MultiTapeTM
open GameTheory.Complexity.Backend.WordOperations

/-- Assemble unmasked membership fields using the canonical source masks. -/
def bimatrixNodeAssemble (v : Fin 3 → List Bool) : List Bool :=
  bimatrixNodeBasicWord ![v 0, v 1] ++
    bimatrixNodeEnteringWord ![v 0, ((v 0) ++ (v 0)) ++ v 2]

@[fun_prop] theorem bimatrixNodeAssemble_polyTime :
    ComputableInPolyTime bimatrixNodeAssemble (encPi encBits) encBits := by
  have hbasic : ComputableInPolyTime
      (fun v : Fin 3 → List Bool => bimatrixNodeBasicWord ![v 0, v 1])
      (encPi encBits) encBits := by
    have hargs : ComputableInPolyTime
        (fun v : Fin 3 → List Bool => ![v 0, v 1])
        (encPi encBits) (encPi encBits) := by
      apply ComputableInPolyTime.pi
      intro i
      fin_cases i
      · exact .pi_apply encBits 0
      · exact .pi_apply encBits 1
    exact bimatrixNodeBasicWord_polyTime.comp hargs
  have henter : ComputableInPolyTime
      (fun v : Fin 3 → List Bool =>
        bimatrixNodeEnteringWord ![v 0, (v 0 ++ v 0) ++ v 2])
      (encPi encBits) encBits := by
    have hclock : ComputableInPolyTime (fun v : Fin 3 → List Bool => v 0 ++ v 0)
        (encPi encBits) encBits :=
      ComputableInPolyTime.bitsAppend (.pi_apply encBits 0) (.pi_apply encBits 0)
    have hclock2 : ComputableInPolyTime (fun v : Fin 3 → List Bool =>
        (v 0 ++ v 0) ++ v 2) (encPi encBits) encBits :=
      ComputableInPolyTime.bitsAppend hclock (.pi_apply encBits 2)
    have hargs : ComputableInPolyTime
        (fun v : Fin 3 → List Bool => ![v 0, (v 0 ++ v 0) ++ v 2])
        (encPi encBits) (encPi encBits) := by
      apply ComputableInPolyTime.pi
      intro i
      fin_cases i
      · exact .pi_apply encBits 0
      · exact hclock2
    exact bimatrixNodeEnteringWord_polyTime.comp hargs
  exact ComputableInPolyTime.bitsAppend hbasic henter

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

/-- Clear the leaving bit and set the entering bit in one unmasked basis position. -/
def bimatrixNodeExchangeBit (v : Fin 4 → List Bool) : List Bool :=
  [if (v 0).length = (v 2).length then false
    else decide ((v 0).length = (v 3).length) || (v 1)[(v 0).length]?.getD false]

/-- One-hot membership at the ordinal named by the target ruler. -/
def bimatrixNodeOneHotBit (v : Fin 2 → List Bool) : List Bool :=
  [decide ((v 0).length = (v 1).length)]

private theorem exchangeBit_polyTime :
    ComputableInPolyTime bimatrixNodeExchangeBit (encPi encBits) encBits := by
  have hposition := ComputableInPolyTime.pi_apply encBits (0 : Fin 4)
  have hbasic := ComputableInPolyTime.pi_apply encBits (1 : Fin 4)
  have hleaving := ComputableInPolyTime.pi_apply encBits (2 : Fin 4)
  have hentering := ComputableInPolyTime.pi_apply encBits (3 : Fin 4)
  have hpositionLen := ComputableInPolyTime.length_bits_comp hposition
  have hleave := ComputableInPolyTime.decide_eq' hpositionLen
    (ComputableInPolyTime.length_bits_comp hleaving)
  have henter := ComputableInPolyTime.decide_eq' hpositionLen
    (ComputableInPolyTime.length_bits_comp hentering)
  have hbit := ComputableInPolyTime.bitsGetDWithInput hbasic hpositionLen false
  have hresult := hleave.ite_decide (ComputableInPolyTime.const false)
    (ComputableInPolyTime.bool_or.comp (henter.prod hbit))
  exact ComputableInPolyTime.bitsCons hresult (.const [])

private theorem oneHotBit_polyTime :
    ComputableInPolyTime bimatrixNodeOneHotBit (encPi encBits) encBits := by
  have h0 := ComputableInPolyTime.pi_apply encBits (0 : Fin 2)
  have h1 := ComputableInPolyTime.pi_apply encBits (1 : Fin 2)
  have h0len := ComputableInPolyTime.length_bits_comp h0
  have h1len := ComputableInPolyTime.length_bits_comp h1
  exact ComputableInPolyTime.bitsCons
    (ComputableInPolyTime.of_tidy ((ComputableTidilyInPolyTime.decide_eq encUnary).comp
      (h0len.tidy.prod h1len.tidy))) (.const [])

/-- Rebuild every unmasked basis bit after the requested exchange. -/
def bimatrixNodeExchangeBasicWord (v : Fin 4 → List Bool) : List Bool :=
  binarySignedTable bimatrixNodeExchangeBit ((v 0) ++ (v 0)) [false]
    ![bimatrixNodeBasicWord ![v 0, v 1], v 2, v 3]

/-- The opposite port enters exactly the leaving ordinal. -/
def bimatrixNodeExchangeEnteringWord (v : Fin 4 → List Bool) : List Bool :=
  binarySignedTable bimatrixNodeOneHotBit ((v 0) ++ (v 0)) [false] ![v 2]

private theorem exchangeBasic_polyTime :
    ComputableInPolyTime bimatrixNodeExchangeBasicWord (encPi encBits) encBits := by
  have hargs : ComputableInPolyTime
      (fun v : Fin 4 → List Bool =>
        ![(v 0) ++ (v 0), [false], bimatrixNodeBasicWord ![v 0, v 1], v 2, v 3])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact ComputableInPolyTime.bitsAppend (.pi_apply encBits (0 : Fin 4))
        (.pi_apply encBits (0 : Fin 4))
    · exact .const [false]
    · apply bimatrixNodeBasicWord_polyTime.comp
      apply ComputableInPolyTime.pi
      intro j
      fin_cases j
      · exact .pi_apply encBits (0 : Fin 4)
      · exact .pi_apply encBits (1 : Fin 4)
    · exact .pi_apply encBits (2 : Fin 4)
    · exact .pi_apply encBits (3 : Fin 4)
  have htable : ComputableInPolyTime
      (fun v : Fin 5 → List Bool => binarySignedTable bimatrixNodeExchangeBit
        (v 0) (v 1) (Fin.tail (Fin.tail v))) (encPi encBits) encBits :=
    binarySignedTable_polyTime (p := 3) exchangeBit_polyTime
  have hcert := htable.comp hargs
  apply ComputableInPolyTime.of_tidy
  apply hcert.tidy.of_enc_eq (g := bimatrixNodeExchangeBasicWord)
  intro v
  change binarySignedTable bimatrixNodeExchangeBit (v 0 ++ v 0) [false]
      ![bimatrixNodeBasicWord ![v 0, v 1], v 2, v 3] =
    binarySignedTable bimatrixNodeExchangeBit (v 0 ++ v 0) [false]
      (Fin.tail (Fin.tail (![v 0 ++ v 0, [false], bimatrixNodeBasicWord ![v 0, v 1], v 2, v 3] :
        Fin 5 → List Bool)))
  apply congrArg (binarySignedTable bimatrixNodeExchangeBit (v 0 ++ v 0) [false])
  funext i
  fin_cases i <;> rfl

private theorem exchangeEntering_polyTime :
    ComputableInPolyTime bimatrixNodeExchangeEnteringWord (encPi encBits) encBits := by
  have hclock := ComputableInPolyTime.bitsAppend
    (.pi_apply encBits (0 : Fin 4)) (.pi_apply encBits (0 : Fin 4))
  have hargs : ComputableInPolyTime
      (fun v : Fin 4 → List Bool => ![(v 0) ++ (v 0), [false], v 2])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact hclock
    · exact .const [false]
    · exact .pi_apply encBits (2 : Fin 4)
  have htable : ComputableInPolyTime
      (fun v : Fin 3 → List Bool => binarySignedTable bimatrixNodeOneHotBit
        (v 0) (v 1) (Fin.tail (Fin.tail v))) (encPi encBits) encBits :=
    binarySignedTable_polyTime (p := 1) oneHotBit_polyTime
  have hcert := htable.comp hargs
  apply ComputableInPolyTime.of_tidy
  apply hcert.tidy.of_enc_eq (g := bimatrixNodeExchangeEnteringWord)
  intro v
  change binarySignedTable bimatrixNodeOneHotBit (v 0 ++ v 0) [false] ![v 2] =
    binarySignedTable bimatrixNodeOneHotBit (v 0 ++ v 0) [false]
      (Fin.tail (Fin.tail (![v 0 ++ v 0, [false], v 2] : Fin 3 → List Bool)))
  apply congrArg (binarySignedTable bimatrixNodeOneHotBit (v 0 ++ v 0) [false])
  funext i
  fin_cases i; rfl

/-- Replace the leaving basis position by the entering position and reverse the port.
Inputs are dimension, node, leaving-position ruler, and entering-position ruler.
Malformed lengths are preserved. -/
def bimatrixNodeExchangeWord (v : Fin 4 → List Bool) : List Bool :=
  if (v 1).length = 4 * (v 0).length then
    bimatrixNodeAssemble ![v 0, bimatrixNodeExchangeBasicWord v, bimatrixNodeExchangeEnteringWord v]
  else v 1

/-- Exchange charges every field, both fixed-width tables and the source-mask assembly. -/
@[fun_prop] theorem bimatrixNodeExchangeWord_polyTime :
    ComputableInPolyTime bimatrixNodeExchangeWord (encPi encBits) encBits := by
  have hdimension : ComputableInPolyTime (fun v : Fin 4 → List Bool => v 0)
      (encPi encBits) encBits := .pi_apply encBits 0
  have hnode : ComputableInPolyTime (fun v : Fin 4 → List Bool => v 1)
      (encPi encBits) encBits := .pi_apply encBits 1
  have hguard := ComputableInPolyTime.decide_eq'
    (ComputableInPolyTime.length_bits_comp hnode)
    (ComputableInPolyTime.unary_mul' (.const 4)
      (ComputableInPolyTime.length_bits_comp hdimension))
  have hargs : ComputableInPolyTime (fun v : Fin 4 → List Bool =>
      ![v 0, bimatrixNodeExchangeBasicWord v, bimatrixNodeExchangeEnteringWord v])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact hdimension
    · exact exchangeBasic_polyTime
    · exact exchangeEntering_polyTime
  exact hguard.ite_decide (bimatrixNodeAssemble_polyTime.comp hargs) hnode

private theorem exchangeBit_value (r basic leaving entering : List Bool) :
    bimatrixNodeExchangeBit ![r, basic, leaving, entering] =
      [if r.length = leaving.length then false else
        decide (r.length = entering.length) || basic[r.length]?.getD false] := rfl

private theorem exchangeBasic_bit (v : Fin 4 → List Bool) (i : ℕ) (hi : i < 2 * (v 0).length) :
    (bimatrixNodeExchangeBasicWord v)[i]?.getD false = if i = (v 2).length then false else
      decide (i = (v 3).length) || (bimatrixNodeBasicWord ![v 0, v 1])[i]?.getD false := by
  exact flagTable_bit bimatrixNodeExchangeBit ![bimatrixNodeBasicWord ![v 0, v 1], v 2, v 3]
    (fun i => if i = (v 2).length then false else
      decide (i = (v 3).length) || (bimatrixNodeBasicWord ![v 0, v 1])[i]?.getD false)
    (fun r => exchangeBit_value r _ _ _) ((v 0) ++ (v 0)) i (by simpa only [List.length_append, ← two_mul] using hi)

private theorem oneHotBit_value (r target : List Bool) :
    bimatrixNodeOneHotBit ![r, target] = [decide (r.length = target.length)] := rfl

private theorem exchangeEntering_bit (v : Fin 4 → List Bool) (i : ℕ) (hi : i < 2 * (v 0).length) :
    (bimatrixNodeExchangeEnteringWord v)[i]?.getD false = decide (i = (v 2).length) := by
  exact flagTable_bit bimatrixNodeOneHotBit ![v 2] (fun i => decide (i = (v 2).length))
    (fun r => oneHotBit_value r _) ((v 0) ++ (v 0)) i
    (by simpa only [List.length_append, ← two_mul] using hi)

theorem bimatrixNodeExchangeWord_length (v : Fin 4 → List Bool) :
    (bimatrixNodeExchangeWord v).length = (v 1).length := by
  rw [bimatrixNodeExchangeWord]
  split_ifs with h
  · rw [bimatrixNodeAssemble_length]
    exact h.symm
  · rfl

private theorem exchangeWord_valid (v : Fin 4 → List Bool)
    (hv : (v 1).length = 4 * (v 0).length) :
    bimatrixNodeExchangeWord v = bimatrixNodeAssemble
      ![v 0, bimatrixNodeExchangeBasicWord v, bimatrixNodeExchangeEnteringWord v] := by
  exact ite_eq_left hv

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
    ![dimension, bimatrixNodeExchangeBasicWord ![dimension, node, leaving, entering],
      bimatrixNodeExchangeEnteringWord ![dimension, node, leaving, entering]] _ hi).trans ?_
  change (bimatrixNodeExchangeBasicWord ![dimension, node, leaving, entering])[
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
    ![dimension, bimatrixNodeExchangeBasicWord ![dimension, node, leaving, entering],
      bimatrixNodeExchangeEnteringWord ![dimension, node, leaving, entering]] _ hi).trans ?_
  change (bimatrixNodeExchangeEnteringWord ![dimension, node, leaving, entering])[
    (GameTheory.Finite.BimatrixPathBinaryCodec.index u).val]?.getD false = _
  rw [exchangeEntering_bit _ _ hi]
  change decide ((GameTheory.Finite.BimatrixPathBinaryCodec.index u).val = leaving.length) = decide (u ∈ ({l} : Finset _))
  simp only [hl, index_val_eq, Finset.mem_singleton]

/-- Toggle the entering kind only at a duplicated nonzero label. -/
def bimatrixNodeSwitchPositionWord (v : Fin 3 → List Bool) : List Bool :=
  let label := (v 2).length / 2
  let basic := bimatrixNodeBasicWord ![v 0, v 1]
  if label ≠ 0 ∧ basic[2 * label]?.getD false = false ∧
      basic[2 * label + 1]?.getD false = false then
    if (v 2).length % 2 = 1 then (v 2).tail else true :: v 2
  else v 2

private theorem switchPosition_polyTime :
    ComputableInPolyTime bimatrixNodeSwitchPositionWord (encPi encBits) encBits := by
  have hpointer : ComputableInPolyTime (fun v : Fin 3 → List Bool => v 2)
      (encPi encBits) encBits := .pi_apply encBits 2
  have hlength := ComputableInPolyTime.length_bits_comp hpointer
  have hlabel := (ComputableInPolyTime.unary_div_const 2).comp hlength
  have hnonzero := ComputableInPolyTime.of_tidy
    (ComputableTidilyInPolyTime.decide_ne hlabel.tidy (ComputableTidilyInPolyTime.const 0))
  have hargs : ComputableInPolyTime (fun v : Fin 3 → List Bool => ![v 0, v 1])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact .pi_apply encBits (0 : Fin 3)
    · exact .pi_apply encBits (1 : Fin 3)
  have hbasic := bimatrixNodeBasicWord_polyTime.comp hargs
  have hindex0 := ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 2) hlabel
  have hindex1 := ComputableInPolyTime.unary_add' hindex0 (ComputableInPolyTime.const 1)
  have habsent0 := ComputableInPolyTime.decide_eq'
    (ComputableInPolyTime.bitsGetDWithInput hbasic hindex0 false)
    (ComputableInPolyTime.const false)
  have habsent1 := ComputableInPolyTime.decide_eq'
    (ComputableInPolyTime.bitsGetDWithInput hbasic hindex1 false)
    (ComputableInPolyTime.const false)
  have hguard := ComputableInPolyTime.of_tidy
    (ComputableTidilyInPolyTime.decide_and hnonzero.tidy
      (ComputableTidilyInPolyTime.decide_and habsent0.tidy habsent1.tidy))
  have hmod := ComputableInPolyTime.unary_mod.comp
    (hlength.prod (ComputableInPolyTime.const 2))
  have hodd := ComputableInPolyTime.decide_eq' hmod (ComputableInPolyTime.const 1)
  exact hguard.ite_decide (hodd.ite_decide
    (ComputableInPolyTime.bitsTail.comp hpointer)
    (ComputableInPolyTime.bitsCons (ComputableInPolyTime.const true) hpointer)) hpointer

/-- Rebuild the one-hot entering field at the selected switch position. -/
def bimatrixNodeSwitchEnteringWord (v : Fin 3 → List Bool) : List Bool :=
  binarySignedTable bimatrixNodeOneHotBit ((v 0) ++ (v 0)) [false] ![bimatrixNodeSwitchPositionWord v]

private theorem switchEntering_polyTime :
    ComputableInPolyTime bimatrixNodeSwitchEnteringWord (encPi encBits) encBits := by
  have hargs : ComputableInPolyTime (fun v : Fin 3 → List Bool =>
      ![v 0 ++ v 0, [false], bimatrixNodeSwitchPositionWord v])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact ComputableInPolyTime.bitsAppend (.pi_apply encBits (0 : Fin 3))
        (.pi_apply encBits (0 : Fin 3))
    · exact .const [false]
    · exact switchPosition_polyTime
  have htable : ComputableInPolyTime
      (fun v : Fin 3 → List Bool => binarySignedTable bimatrixNodeOneHotBit
        (v 0) (v 1) (Fin.tail (Fin.tail v))) (encPi encBits) encBits :=
    binarySignedTable_polyTime (p := 1) oneHotBit_polyTime
  have hcert := htable.comp hargs
  apply ComputableInPolyTime.of_tidy
  apply hcert.tidy.of_enc_eq (g := bimatrixNodeSwitchEnteringWord)
  intro v
  change binarySignedTable bimatrixNodeOneHotBit (v 0 ++ v 0) [false]
      ![bimatrixNodeSwitchPositionWord v] =
    binarySignedTable bimatrixNodeOneHotBit (v 0 ++ v 0) [false]
      (Fin.tail (Fin.tail (![v 0 ++ v 0, [false], bimatrixNodeSwitchPositionWord v] :
        Fin 3 → List Bool)))
  apply congrArg (binarySignedTable bimatrixNodeOneHotBit (v 0 ++ v 0) [false])
  funext i
  fin_cases i; rfl

/-- Switch a duplicated-label port's kind, retaining dropped-label endpoints.
Inputs are dimension, node, and entering-position ruler. Malformed lengths are preserved. -/
def bimatrixNodeSwitchWord (v : Fin 3 → List Bool) : List Bool :=
  if (v 1).length = 4 * (v 0).length then
    bimatrixNodeAssemble
      ![v 0, bimatrixNodeBasicWord ![v 0, v 1], bimatrixNodeSwitchEnteringWord v]
  else v 1

/-- Switching charges basis unmasking, position selection and one-hot output assembly. -/
@[fun_prop] theorem bimatrixNodeSwitchWord_polyTime :
    ComputableInPolyTime bimatrixNodeSwitchWord (encPi encBits) encBits := by
  have hdimension : ComputableInPolyTime (fun v : Fin 3 → List Bool => v 0)
      (encPi encBits) encBits := .pi_apply encBits 0
  have hnode : ComputableInPolyTime (fun v : Fin 3 → List Bool => v 1)
      (encPi encBits) encBits := .pi_apply encBits 1
  have hguard := ComputableInPolyTime.decide_eq'
    (ComputableInPolyTime.length_bits_comp hnode)
    (ComputableInPolyTime.unary_mul' (.const 4)
      (ComputableInPolyTime.length_bits_comp hdimension))
  have hbasicArgs : ComputableInPolyTime
      (fun v : Fin 3 → List Bool => ![v 0, v 1]) (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact hdimension
    · exact hnode
  have hbasic := bimatrixNodeBasicWord_polyTime.comp hbasicArgs
  have hargs : ComputableInPolyTime (fun v : Fin 3 → List Bool =>
      ![v 0, bimatrixNodeBasicWord ![v 0, v 1], bimatrixNodeSwitchEnteringWord v])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact hdimension
    · exact hbasic
    · exact switchEntering_polyTime
  exact hguard.ite_decide (bimatrixNodeAssemble_polyTime.comp hargs) hnode

theorem bimatrixNodeSwitchWord_length (v : Fin 3 → List Bool) :
    (bimatrixNodeSwitchWord v).length = (v 1).length := by
  rw [bimatrixNodeSwitchWord]
  split_ifs with h
  · rw [bimatrixNodeAssemble_length]
    exact h.symm
  · rfl

private theorem switchPosition_length (v : Fin 3 → List Bool) :
    (bimatrixNodeSwitchPositionWord v).length =
      if (v 2).length / 2 ≠ 0 ∧
          (bimatrixNodeBasicWord ![v 0, v 1])[2 * ((v 2).length / 2)]?.getD false = false ∧
          (bimatrixNodeBasicWord ![v 0, v 1])[2 * ((v 2).length / 2) + 1]?.getD false = false then
        if (v 2).length % 2 = 1 then (v 2).length - 1 else (v 2).length + 1
      else (v 2).length := by
  simp only [bimatrixNodeSwitchPositionWord]
  split_ifs <;> simp only [List.length_tail, List.length_cons]

private theorem switchPosition_port {m n : ℕ} {A B : Fin m → Fin n → ℤ}
    {d : Fin (m + n)} (dimension node pointer : List Bool)
    (hk : dimension.length = m + n) (hd : d.val = 0)
    (port : GameTheory.Finite.BimatrixPathPort A B d)
    (hb : GameTheory.Finite.BimatrixPathBinaryCodec.basic node = port.node.basis.basic)
    (hp : pointer.length = (GameTheory.Finite.BimatrixPathBinaryCodec.index port.entering).val) :
    (bimatrixNodeSwitchPositionWord ![dimension, node, pointer]).length =
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
      ![v 0, bimatrixNodeBasicWord ![v 0, v 1], bimatrixNodeSwitchEnteringWord v] := by
  exact ite_eq_left hw

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
    ![dimension, bimatrixNodeBasicWord ![dimension, node], bimatrixNodeSwitchEnteringWord ![dimension, node, pointer]]
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
    ![dimension, bimatrixNodeBasicWord ![dimension, node], bimatrixNodeSwitchEnteringWord ![dimension, node, pointer]]
    _ hi).trans ?_
  change (bimatrixNodeSwitchEnteringWord ![dimension, node, pointer])[
    (GameTheory.Finite.BimatrixPathBinaryCodec.index u).val]?.getD false = _
  rw [bimatrixNodeSwitchEnteringWord]
  refine (flagTable_bit bimatrixNodeOneHotBit _ (fun i => decide (i = (bimatrixNodeSwitchPositionWord ![dimension, node, pointer]).length))
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
