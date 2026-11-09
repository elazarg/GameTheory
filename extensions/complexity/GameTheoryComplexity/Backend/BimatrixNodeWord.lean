module

public import GameTheoryComplexity.Backend.BinarySignedMatrixMachine
public import GameTheoryComplexity.Backend.BinaryUnaryArithmetic
public import GameTheoryComplexity.Backend.BinarySubsetMachine
public import GameTheoryComplexity.Backend.BinaryIndexedAll
public import GameTheory.Finite.BimatrixPathBinaryCodec

@[expose] public section

/-! Certified unmasking and combinatorial validation of complementary path words.
The dimension is an explicit length ruler and the dropped label is zero.
-/
namespace GameTheory.Complexity.Backend
open Cslib.BitString Turing.MultiTapeTM
open GameTheory.Complexity.Backend.WordOperations

/-- Unmask one basic-variable bit using the ruler's parity. -/
def bimatrixNodeBasicBit (v : Fin 2 → List Bool) : List Bool :=
  [Bool.xor ((v 1)[(v 0).length]?.getD false)
    (!(decide ((v 0).length % 2 = 1)))]

/-- Unmask one entering-variable bit, removing the source bit at position one. -/
def bimatrixNodeEnteringBit (v : Fin 2 → List Bool) : List Bool :=
  [Bool.xor ((v 1)[(v 0).length]?.getD false) (decide ((v 0).length = 1))]

/-- Unmask the basis bits, indexed in canonical label/kind order. -/
def bimatrixNodeBasicWord (v : Fin 2 → List Bool) : List Bool :=
  binarySignedTable bimatrixNodeBasicBit ((v 0) ++ (v 0)) [false] ![v 1]

/-- Unmask the entering bits; the source entering variable has position one. -/
def bimatrixNodeEnteringWord (v : Fin 2 → List Bool) : List Bool :=
  binarySignedTable bimatrixNodeEnteringBit ((v 0) ++ (v 0)) [false]
    ![(v 1).drop (((v 0) ++ (v 0)).length)]

private theorem bimatrixNodeBasicBit_polyTime :
    ComputableInPolyTime bimatrixNodeBasicBit (encPi encBits) encBits := by
  have hr := ComputableInPolyTime.pi_apply encBits (0 : Fin 2)
  have hw := ComputableInPolyTime.pi_apply encBits (1 : Fin 2)
  have hlen := ComputableInPolyTime.length_bits_comp hr
  have hbit := indexedFlag_polyTime.comp (hlen.prod hw)
  have hodd := binaryLengthParity_polyTime.comp hr
  have hhead : ComputableInPolyTime (fun word : List Bool => word.headD false)
      encBits encBool := .headD false
  have hbitBool := hhead.comp hbit
  have hparity := hhead.comp hodd
  have hnot := ComputableInPolyTime.bool_not.comp hparity
  have hxor := ComputableInPolyTime.bool_xor.comp (hbitBool.prod hnot)
  exact ComputableInPolyTime.bitsCons hxor (.const [])

private theorem bimatrixNodeEnteringBit_polyTime :
    ComputableInPolyTime bimatrixNodeEnteringBit (encPi encBits) encBits := by
  have hr := ComputableInPolyTime.pi_apply encBits (0 : Fin 2)
  have hw := ComputableInPolyTime.pi_apply encBits (1 : Fin 2)
  have hlen := ComputableInPolyTime.length_bits_comp hr
  have hbit := indexedFlag_polyTime.comp (hlen.prod hw)
  have heq := ComputableInPolyTime.of_tidy
    ((ComputableTidilyInPolyTime.decide_eq encUnary).comp (hlen.tidy.prod (.const 1)))
  have hhead : ComputableInPolyTime (fun word : List Bool => word.headD false)
      encBits encBool := .headD false
  have hbitBool := hhead.comp hbit
  have hxor := ComputableInPolyTime.bool_xor.comp (hbitBool.prod heq)
  exact ComputableInPolyTime.bitsCons hxor (.const [])

@[fun_prop] theorem bimatrixNodeBasicWord_polyTime :
    ComputableInPolyTime bimatrixNodeBasicWord (encPi encBits) encBits := by
  have hargs : ComputableInPolyTime
      (fun v : Fin 2 → List Bool => ![(v 0) ++ (v 0), [false], v 1])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · change ComputableInPolyTime (fun v : Fin 2 → List Bool => (v 0) ++ (v 0))
        (encPi encBits) encBits
      exact ComputableInPolyTime.bitsAppend (.pi_apply encBits (0 : Fin 2))
        (.pi_apply encBits (0 : Fin 2))
    · change ComputableInPolyTime (fun _ : Fin 2 → List Bool => [false])
        (encPi encBits) encBits
      exact .const [false]
    · change ComputableInPolyTime (fun v : Fin 2 → List Bool => v 1)
        (encPi encBits) encBits
      exact .pi_apply encBits (1 : Fin 2)
  have htable : ComputableInPolyTime
      (fun v : Fin 3 → List Bool =>
        binarySignedTable bimatrixNodeBasicBit (v 0) (v 1) (Fin.tail (Fin.tail v)))
      (encPi encBits) encBits :=
    binarySignedTable_polyTime (p := 1) bimatrixNodeBasicBit_polyTime
  have hcert := htable.comp hargs
  apply ComputableInPolyTime.of_tidy
  apply hcert.tidy.of_enc_eq
  intro v
  rfl

@[fun_prop] theorem bimatrixNodeEnteringWord_polyTime :
    ComputableInPolyTime bimatrixNodeEnteringWord (encPi encBits) encBits := by
  have hclock : ComputableInPolyTime (fun v : Fin 2 → List Bool => v 0 ++ v 0)
      (encPi encBits) encBits :=
    ComputableInPolyTime.bitsAppend (.pi_apply encBits (0 : Fin 2))
      (.pi_apply encBits (0 : Fin 2))
  have hclockLen := ComputableInPolyTime.length_bits_comp hclock
  have hword : ComputableInPolyTime (fun v : Fin 2 → List Bool => v 1)
      (encPi encBits) encBits := .pi_apply encBits 1
  have hdrop : ComputableInPolyTime
      (fun v : Fin 2 → List Bool => (v 1).drop ((v 0 ++ v 0).length))
      (encPi encBits) encBits := hword.bitsDropWithInput hclockLen
  have hargs : ComputableInPolyTime
      (fun v : Fin 2 → List Bool =>
        ![(v 0) ++ (v 0), [false], (v 1).drop (((v 0) ++ (v 0)).length)])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · change ComputableInPolyTime (fun v : Fin 2 → List Bool => v 0 ++ v 0)
        (encPi encBits) encBits
      exact hclock
    · change ComputableInPolyTime (fun _ : Fin 2 → List Bool => [false])
        (encPi encBits) encBits
      exact .const [false]
    · change ComputableInPolyTime
        (fun v : Fin 2 → List Bool => (v 1).drop ((v 0 ++ v 0).length))
        (encPi encBits) encBits
      exact hdrop
  have htable : ComputableInPolyTime
      (fun v : Fin 3 → List Bool =>
        binarySignedTable bimatrixNodeEnteringBit (v 0) (v 1) (Fin.tail (Fin.tail v)))
      (encPi encBits) encBits :=
    binarySignedTable_polyTime (p := 1) bimatrixNodeEnteringBit_polyTime
  have hcert := htable.comp hargs
  apply ComputableInPolyTime.of_tidy
  apply hcert.tidy.of_enc_eq
  intro v
  rfl

@[simp] theorem bimatrixNodeBasicWord_length (v : Fin 2 → List Bool) :
    (bimatrixNodeBasicWord v).length = 2 * (v 0).length := by
  simp [bimatrixNodeBasicWord, two_mul]

@[simp] theorem bimatrixNodeEnteringWord_length (v : Fin 2 → List Bool) :
    (bimatrixNodeEnteringWord v).length = 2 * (v 0).length := by
  simp [bimatrixNodeEnteringWord, two_mul]



private theorem xor_decide (x y : Bool) : some (xor x y) = some (decide (xor x y = true)) := by
  cases x <;> cases y <;> rfl

private theorem basicBit_value (r node : List Bool) :
    bimatrixNodeBasicBit ![r, node] =
      [xor (node[r.length]?.getD false) (!(decide (r.length % 2 = 1)))] := rfl

private theorem enteringBit_value (r node : List Bool) :
    bimatrixNodeEnteringBit ![r, node] =
      [xor (node[r.length]?.getD false) (decide (r.length = 1))] := rfl

/-- Exact unmasked basis bytes, including zero padding for truncated nodes. -/
theorem bimatrixNodeBasicWord_value (v : Fin 2 → List Bool) :
    bimatrixNodeBasicWord v = (List.range (2 * (v 0).length)).map
      (fun i => xor ((v 1)[i]?.getD false) (!(decide (i % 2 = 1)))) := by
  have h := binarySignedTable_flags bimatrixNodeBasicBit ![v 1]
    (fun i => xor ((v 1)[i]?.getD false) (!(decide (i % 2 = 1))))
    (fun r => basicBit_value r (v 1)) ((v 0) ++ (v 0))
  simpa only [bimatrixNodeBasicWord, List.length_append, ← two_mul] using h

/-- Exact entering bytes with the source's one-hot bit removed. -/
theorem bimatrixNodeEnteringWord_value (v : Fin 2 → List Bool) :
    bimatrixNodeEnteringWord v = (List.range (2 * (v 0).length)).map
      (fun i => xor ((v 1)[2 * (v 0).length + i]?.getD false) (decide (i = 1))) := by
  have h := binarySignedTable_flags bimatrixNodeEnteringBit ![(v 1).drop (2 * (v 0).length)]
    (fun i => xor (((v 1).drop (2 * (v 0).length))[i]?.getD false) (decide (i = 1)))
    (fun r => enteringBit_value r _) ((v 0) ++ (v 0))
  simpa only [bimatrixNodeEnteringWord, List.length_append, ← two_mul, List.getElem?_drop] using h

def bimatrixNodeCoverageBit (v : Fin 2 → List Bool) : List Bool :=
  [decide ((v 0).length = 0) ||
    (!((v 1)[2 * (v 0).length]?.getD false) ||
      !((v 1)[2 * (v 0).length + 1]?.getD false))]

def bimatrixNodePortBit (v : Fin 3 → List Bool) : List Bool :=
  let labelLength := (binaryHalfRuler (v 0)).length
  let enteringBit := (v 2)[(v 0).length]?.getD false
  let basicBit := (v 1)[(v 0).length]?.getD false
  let basicLabelFalse := (v 1)[2 * labelLength]?.getD false
  let basicLabelTrue := (v 1)[2 * labelLength + 1]?.getD false
  let condition :=
    (!enteringBit) ||
      ((!basicBit) &&
        ((decide (labelLength = 0)) ||
          ((!basicLabelFalse) && (!basicLabelTrue))))
  [condition]

private theorem bimatrixNodeCoverageBit_polyTime :
    ComputableInPolyTime bimatrixNodeCoverageBit (encPi encBits) encBits := by
  have hr := ComputableInPolyTime.pi_apply encBits (0 : Fin 2)
  have hb := ComputableInPolyTime.pi_apply encBits (1 : Fin 2)
  have hlen := ComputableInPolyTime.length_bits_comp hr
  have hindex0 := ComputableInPolyTime.unary_mul' (.const 2) hlen
  have hindex1 := ComputableInPolyTime.unary_add' hindex0 (.const 1)
  have hbit0 := indexedFlag_polyTime.comp (hindex0.prod hb)
  have hbit1 := indexedFlag_polyTime.comp (hindex1.prod hb)
  have hhead : ComputableInPolyTime (fun word : List Bool => word.headD false)
      encBits encBool := .headD false
  have hnot0 := ComputableInPolyTime.bool_not.comp (hhead.comp hbit0)
  have hnot1 := ComputableInPolyTime.bool_not.comp (hhead.comp hbit1)
  have hzero := ComputableInPolyTime.of_tidy
    ((ComputableTidilyInPolyTime.decide_eq encUnary).comp (hlen.tidy.prod (.const 0)))
  have hzeroOr := ComputableInPolyTime.bool_or.comp (hzero.prod
    (ComputableInPolyTime.bool_or.comp (hnot0.prod hnot1)))
  have hcert := ComputableInPolyTime.bitsCons hzeroOr (.const [])
  apply ComputableInPolyTime.of_tidy
  apply hcert.tidy.of_enc_eq
  intro v
  rfl

private theorem bimatrixNodePortBit_polyTime :
    ComputableInPolyTime bimatrixNodePortBit (encPi encBits) encBits := by
  have hr := ComputableInPolyTime.pi_apply encBits (0 : Fin 3)
  have hb := ComputableInPolyTime.pi_apply encBits (1 : Fin 3)
  have he := ComputableInPolyTime.pi_apply encBits (2 : Fin 3)
  have hlen := ComputableInPolyTime.length_bits_comp hr
  have hhalf := binaryHalfRuler_polyTime.comp hr
  have hhalfLen := ComputableInPolyTime.length_bits_comp hhalf
  have hhalfIndex0 := ComputableInPolyTime.unary_mul' (.const 2) hhalfLen
  have hhalfIndex1 := ComputableInPolyTime.unary_add' hhalfIndex0 (.const 1)
  have henter := indexedFlag_polyTime.comp (hlen.prod he)
  have hbasic := indexedFlag_polyTime.comp (hlen.prod hb)
  have hbasic0 := indexedFlag_polyTime.comp (hhalfIndex0.prod hb)
  have hbasic1 := indexedFlag_polyTime.comp (hhalfIndex1.prod hb)
  have hhead : ComputableInPolyTime (fun word : List Bool => word.headD false)
      encBits encBool := .headD false
  have hnotEnter := ComputableInPolyTime.bool_not.comp (hhead.comp henter)
  have hnotBasic := ComputableInPolyTime.bool_not.comp (hhead.comp hbasic)
  have hnotBasic0 := ComputableInPolyTime.bool_not.comp (hhead.comp hbasic0)
  have hnotBasic1 := ComputableInPolyTime.bool_not.comp (hhead.comp hbasic1)
  have hzero := ComputableInPolyTime.of_tidy
    ((ComputableTidilyInPolyTime.decide_eq encUnary).comp (hhalfLen.tidy.prod (.const 0)))
  have hboth := ComputableInPolyTime.bool_and.comp (hnotBasic0.prod hnotBasic1)
  have hlabelOK := ComputableInPolyTime.bool_or.comp (hzero.prod hboth)
  have hbody := ComputableInPolyTime.bool_and.comp (hnotBasic.prod hlabelOK)
  have hout := ComputableInPolyTime.bool_or.comp (hnotEnter.prod hbody)
  have hcert := ComputableInPolyTime.bitsCons hout (.const [])
  apply ComputableInPolyTime.of_tidy
  apply hcert.tidy.of_enc_eq
  intro v
  rfl

abbrev CoveredAt (basic : List Bool) (i : ℕ) : Prop :=
  i = 0 ∨ basic[2 * i]?.getD false = false ∨ basic[2 * i + 1]?.getD false = false

abbrev PermittedAt (basic entering : List Bool) (i : ℕ) : Prop :=
  entering[i]?.getD false = true → basic[i]?.getD false = false ∧
    (i / 2 = 0 ∨ (basic[2 * (i / 2)]?.getD false = false ∧
      basic[2 * (i / 2) + 1]?.getD false = false))

private theorem coverageBit_value (r basic : List Bool) :
    bimatrixNodeCoverageBit ![r, basic] = [decide (CoveredAt basic r.length)] := by
  change [decide (r.length = 0) ||
      (!(basic[2 * r.length]?.getD false) ||
        !(basic[2 * r.length + 1]?.getD false))] =
    [decide (r.length = 0 ∨ basic[2 * r.length]?.getD false = false ∨
      basic[2 * r.length + 1]?.getD false = false)]
  by_cases hz : r.length = 0 <;>
    by_cases hb : basic[2 * r.length]?.getD false = false <;>
    by_cases hc : basic[2 * r.length + 1]?.getD false = false <;>
    simp [hz, hb, hc]

private theorem portBit_value (r basic entering : List Bool) :
    bimatrixNodePortBit ![r, basic, entering] = [decide (PermittedAt basic entering r.length)] := by
  simp [bimatrixNodePortBit, PermittedAt, binaryHalfRuler_length]

/-- Combinatorial validation: exact size, basis cardinality, one entering variable,
coverage away from label zero, and the complementary-port condition. -/
def bimatrixNodeSyntaxFlag (v : Fin 2 → List Bool) : List Bool :=
  let basic := bimatrixNodeBasicWord v
  let entering := bimatrixNodeEnteringWord v
  andFlag [decide ((v 1).length = 4 * (v 0).length)]
    (andFlag [decide ((binarySubsetTally basic).length = (v 0).length)]
      (andFlag [decide ((binarySubsetTally entering).length = [false].length)]
        (andFlag (binaryIndexedAll bimatrixNodeCoverageBit (v 0) ![basic])
          (binaryIndexedAll bimatrixNodePortBit ((v 0) ++ (v 0)) ![basic, entering]))))

@[fun_prop] theorem bimatrixNodeSyntaxFlag_polyTime :
    ComputableInPolyTime bimatrixNodeSyntaxFlag (encPi encBits) encBits := by
  have hbasic := bimatrixNodeBasicWord_polyTime
  have henter := bimatrixNodeEnteringWord_polyTime
  have hdimension := ComputableInPolyTime.pi_apply encBits (0 : Fin 2)
  have hsource := ComputableInPolyTime.pi_apply encBits (1 : Fin 2)
  have hdimensionLen := ComputableInPolyTime.length_bits_comp hdimension
  have hsourceLen := ComputableInPolyTime.length_bits_comp hsource
  have hsize := ComputableInPolyTime.of_tidy
    ((ComputableTidilyInPolyTime.decide_eq encUnary).comp
      (hsourceLen.tidy.prod (ComputableInPolyTime.unary_mul' (.const 4) hdimensionLen).tidy))
  have hsizeFlag := ComputableInPolyTime.bitsCons hsize (.const [])
  have hbasicCount := ComputableInPolyTime.length_bits_comp
    (binarySubsetTally_polyTime hbasic)
  have hbasicFlag := ComputableInPolyTime.bitsCons
    (ComputableInPolyTime.of_tidy ((ComputableTidilyInPolyTime.decide_eq encUnary).comp
      (hbasicCount.tidy.prod hdimensionLen.tidy))) (.const [])
  have henterCount := ComputableInPolyTime.length_bits_comp
    (binarySubsetTally_polyTime henter)
  have honeFlag := ComputableInPolyTime.bitsCons
    (ComputableInPolyTime.of_tidy ((ComputableTidilyInPolyTime.decide_eq encUnary).comp
      (henterCount.tidy.prod (.const 1)))) (.const [])
  have hcoverageArgs : ComputableInPolyTime
      (fun v : Fin 2 → List Bool => ![v 0, bimatrixNodeBasicWord v])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact .pi_apply encBits 0
    · exact hbasic
  have hcoverage := (binaryIndexedAll_polyTime (p := 1) bimatrixNodeCoverageBit_polyTime)
    |>.comp hcoverageArgs
  have hclock := ComputableInPolyTime.bitsAppend hdimension hdimension
  have hportArgs : ComputableInPolyTime
      (fun v : Fin 2 → List Bool =>
        ![(v 0) ++ (v 0), bimatrixNodeBasicWord v, bimatrixNodeEnteringWord v])
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    fin_cases i
    · exact hclock
    · exact hbasic
    · exact henter
  have hports := (binaryIndexedAll_polyTime (p := 2) bimatrixNodePortBit_polyTime)
    |>.comp hportArgs
  have hlast := andFlag_polyTime.comp (hcoverage.prod hports)
  have hthird := andFlag_polyTime.comp (honeFlag.prod hlast)
  have hsecond := andFlag_polyTime.comp (hbasicFlag.prod hthird)
  have hfirst := andFlag_polyTime.comp (hsizeFlag.prod hsecond)
  have hcert := hfirst
  apply ComputableInPolyTime.of_tidy
  apply hcert.tidy.of_enc_eq
  intro v
  rfl


private theorem and_decide (P Q : Prop) [Decidable P] [Decidable Q] :
    andFlag [decide P] [decide Q] = [decide (P ∧ Q)] := by
  by_cases hp : P <;> by_cases hq : Q <;> simp [hp, hq, andFlag]

/-- All syntactic conditions checked by the bounded Boolean machine. -/
theorem bimatrixNodeSyntaxFlag_value (v : Fin 2 → List Bool) :
    bimatrixNodeSyntaxFlag v = [decide ((v 1).length = 4 * (v 0).length ∧
      (bimatrixNodeBasicWord v).count true = (v 0).length ∧
      (bimatrixNodeEnteringWord v).count true = 1 ∧
      (∀ i < (v 0).length, CoveredAt (bimatrixNodeBasicWord v) i) ∧
      (∀ i < 2 * (v 0).length, PermittedAt (bimatrixNodeBasicWord v)
        (bimatrixNodeEnteringWord v) i))] := by
  rw [bimatrixNodeSyntaxFlag, binarySubsetTally_length, binarySubsetTally_length]
  rw [binaryIndexedAll_value bimatrixNodeCoverageBit _ _ (fun r => coverageBit_value r _),
    binaryIndexedAll_value bimatrixNodePortBit _ _ (fun r => portBit_value r _ _)]
  simp only [List.length_append, List.length_singleton, ← two_mul]
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
