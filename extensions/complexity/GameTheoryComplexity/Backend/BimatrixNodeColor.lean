import GameTheoryComplexity.Backend.BimatrixNodeWord
import GameTheoryComplexity.Backend.BinaryBirdDeterminantMachine
import GameTheory.Finite.BimatrixComputedOrientation

/-! Polynomial-time integer orientation words for canonical complementary ports.
Insertion rank and payoff-kind parity are scanned from explicit membership bits.
Source calibration compares two decoded integer scores and needs no special
source-sign formula or rational inverse computation.
-/
namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham


private theorem lenLe_value (a b : List Bool) : lenLeFlag a b = [decide (b.length ≤ a.length)] := by
  rcases lenLeFlag_flag a b with h | h
  · rw [h]; simp [(lenLeFlag_eq_true_iff a b).mp h]
  · rw [h]
    have hn : ¬ b.length ≤ a.length := by
      intro he
      have := (lenLeFlag_eq_true_iff a b).mpr he
      simp [h] at this
    simp [hn]

private theorem lenEq_value (a b : List Bool) : lenEqFlag a b = [decide (a.length = b.length)] := by
  rcases lenEqFlag_flag a b with h | h
  · rw [h]; simp [(lenEqFlag_eq_true_iff a b).mp h]
  · rw [h]
    have hn : a.length ≠ b.length := by
      intro he
      have := (lenEqFlag_eq_true_iff a b).mpr he
      simp [h] at this
    simp [hn]
private def payoffBit (v : Fin 3 → List Bool) : List Bool :=
  andBit (binaryLengthParity (v 0))
    (andBit (lenLeFlag (v 0) [true, true, true])
      (orBit (bitAt (v 0) (v 1)) (lenEqFlag (v 0) (v 2))))

private theorem payoffBit_cobham : Cobham payoffBit :=
  Cobham.andFn (Cobham.comp binaryLengthParity_cobham fun _ => .proj 0)
    (Cobham.andFn (lenLeFlag_mem (.proj 0) (Cobham.const [true, true, true]))
      (Cobham.orFn (Cobham.comp₂ Cobham.bitAtFn (.proj 0) (.proj 1))
        (lenEqFlag_mem (.proj 0) (.proj 2))))

private theorem payoffBit_value (r basic entering : List Bool) :
    payoffBit ![r, basic, entering] =
      [decide (r.length % 2 = 1 ∧ 3 ≤ r.length ∧
        (basic[r.length]?.getD false = true ∨ r.length = entering.length))] := by
  change andBit (binaryLengthParity r)
    (andBit (lenLeFlag r [true, true, true]) (orBit (bitAt r basic) (lenEqFlag r entering))) = _
  rw [binaryLengthParity_value, lenLe_value, bitAt_getElem?, lenEq_value]
  simp only [List.length_cons, List.length_nil]
  have ha (P Q : Prop) [Decidable P] [Decidable Q] :
      andBit [decide P] [decide Q] = [decide (P ∧ Q)] := by
    by_cases hp : P <;> by_cases hq : Q <;> simp [hp, hq, andBit, caseBit₀]
  have ho (P Q : Prop) [Decidable P] [Decidable Q] :
      orBit [decide P] [decide Q] = [decide (P ∨ Q)] := by
    by_cases hp : P <;> by_cases hq : Q <;> simp [hp, hq, orBit, caseBit₀]
  have hb : [basic[r.length]?.getD false] = [decide (basic[r.length]?.getD false = true)] := by
    cases basic[r.length]?.getD false <;> rfl
  rw [hb, ho, ha, ha]
private def payoffWord (v : Fin 3 → List Bool) : List Bool :=
  binarySignedTable payoffBit (v 0 ++ v 0) [false]
    ![bimatrixNodeBasicWord ![v 0, v 1], v 2]

private theorem payoffWord_cobham : Cobham payoffWord := by
  have h := Cobham.comp (binarySignedTable_cobham payoffBit_cobham)
    (gs := fun i => fun v : Fin 3 → List Bool =>
      ![v 0 ++ v 0, [false], bimatrixNodeBasicWord ![v 0, v 1], v 2] i)
    (fun i => by
      fin_cases i
      · exact Cobham.appendFn (.proj 0) (.proj 0)
      · exact Cobham.const [false]
      · exact Cobham.comp₂ bimatrixNodeBasicWord_cobham (.proj 0) (.proj 1)
      · exact .proj 2)
  exact h.of_eq fun _ => rfl

/-- Integer orientation from dimension, node bits, entering position, and basis determinant. -/
def bimatrixNodeOrientationWord (v : Fin 4 → List Bool) : List Bool :=
  binarySignedMul
    (binarySignedMul
      (binaryBirdSign (binarySubsetTally ((bimatrixNodeBasicWord ![v 0, v 1]).take (v 2).length)))
      (v 3))
    (binaryBirdSign (binarySubsetTally (payoffWord ![v 0, v 1, v 2])))

theorem bimatrixNodeOrientationWord_cobham : Cobham bimatrixNodeOrientationWord := by
  have hb : Cobham fun v : Fin 4 → List Bool => bimatrixNodeBasicWord ![v 0, v 1] :=
    Cobham.comp₂ bimatrixNodeBasicWord_cobham (.proj 0) (.proj 1)
  have hp : Cobham fun v : Fin 4 → List Bool => payoffWord ![v 0, v 1, v 2] :=
    Cobham.comp₃ payoffWord_cobham (.proj 0) (.proj 1) (.proj 2)
  exact Cobham.comp₂ binarySignedMul_cobham
    (Cobham.comp₂ binarySignedMul_cobham
      (Cobham.comp binaryBirdSign_cobham fun _ =>
        Cobham.comp binarySubsetTally_cobham fun _ => Cobham.takeFn (.proj 2) hb) (.proj 3))
    (Cobham.comp binaryBirdSign_cobham fun _ =>
      Cobham.comp binarySubsetTally_cobham fun _ => hp)

theorem bimatrixNodeOrientationWord_mem_FPn : FPn bimatrixNodeOrientationWord :=
  cobham_iff_FPn.mp bimatrixNodeOrientationWord_cobham

/-- Compare the sign of the product of a score and its calibration score. -/
def binaryScoreColor (v : Fin 2 → List Bool) : List Bool :=
  binarySignedLTFlag [] (binarySignedMul (v 0) (v 1))

theorem binaryScoreColor_cobham : Cobham binaryScoreColor :=
  Cobham.comp₂ binarySignedLTFlag_cobham (Cobham.const [])
    (Cobham.comp₂ binarySignedMul_cobham (.proj 0) (.proj 1))

theorem binaryScoreColor_mem_FPn : FPn binaryScoreColor := cobham_iff_FPn.mp binaryScoreColor_cobham

theorem binaryScoreColor_value (v : Fin 2 → List Bool) :
    binaryScoreColor v = [decide (0 < binarySignedValue (v 0) * binarySignedValue (v 1))] := by
  rw [binaryScoreColor, binarySignedLTFlag_value, binarySignedMul_value]
  rfl

theorem binaryScoreColor_length (v : Fin 2 → List Bool) : (binaryScoreColor v).length = 1 := by
  rw [binaryScoreColor_value]
  rfl

private theorem payoff_index_iff {m n : ℕ} (d : Fin (m + n)) (hd : d.val = 0)
    (v : GameTheory.Finite.BimatrixVariable m n) :
    (GameTheory.Finite.BimatrixPathBinaryCodec.index v).val % 2 = 1 ∧
      3 ≤ (GameTheory.Finite.BimatrixPathBinaryCodec.index v).val ↔
      (ofLex v).2 = true ∧ (ofLex v).1 ≠ d := by
  have hz : (ofLex v).1 ≠ d ↔ (ofLex v).1.val ≠ 0 := by
    constructor
    · intro h he
      exact h (Fin.ext (he.trans hd.symm))
    · intro h he
      exact h ((congrArg Fin.val he).trans hd)
  rw [hz]
  simp only [GameTheory.Finite.BimatrixPathBinaryCodec.index]
  cases (ofLex v).2
  · simp
  · simp [Nat.add_mod]; omega

private theorem index_val_iff {m n : ℕ} (u v : GameTheory.Finite.BimatrixVariable m n) :
    (GameTheory.Finite.BimatrixPathBinaryCodec.index u).val =
      (GameTheory.Finite.BimatrixPathBinaryCodec.index v).val ↔ u = v := by
  constructor
  · intro h
    exact GameTheory.Finite.BimatrixPathBinaryCodec.index_strictMono.injective (Fin.ext h)
  · rintro rfl
    rfl

private theorem payoffWord_membership {m n : ℕ} (dimension node pointer : List Bool)
    (hk : dimension.length = m + n) (d : Fin (m + n)) (hd : d.val = 0)
    (e : GameTheory.Finite.BimatrixVariable m n)
    (hp : pointer.length = (GameTheory.Finite.BimatrixPathBinaryCodec.index e).val) :
    payoffWord ![dimension, node, pointer] = GameTheory.Finite.BimatrixPathBinaryCodec.membershipWord
      ((insert e (GameTheory.Finite.BimatrixPathBinaryCodec.basic node)).filter
        (fun v => (ofLex v).2 = true ∧ (ofLex v).1 ≠ d)) := by
  rw [payoffWord]
  change binarySignedTable payoffBit (dimension ++ dimension) [false]
    ![bimatrixNodeBasicWord ![dimension, node], pointer] = _
  rw [binarySignedTable_flags payoffBit ![bimatrixNodeBasicWord ![dimension, node], pointer]
    (fun i => decide (i % 2 = 1 ∧ 3 ≤ i ∧
      ((bimatrixNodeBasicWord ![dimension, node])[i]?.getD false = true ∨ i = pointer.length)))
    (fun r => payoffBit_value r (bimatrixNodeBasicWord ![dimension, node]) pointer)]
  apply List.ext_getElem?
  intro i
  by_cases hi : i < 2 * (m + n)
  · simp only [List.length_append, hk, ← two_mul, List.getElem?_map, List.getElem?_range,
      Option.map_some, GameTheory.Finite.BimatrixPathBinaryCodec.membershipWord,
      List.getElem?_ofFn, hi, ↓reduceDIte]
    let v := GameTheory.Finite.BimatrixPathBinaryCodec.variableAt (m := m) (n := n) ⟨i, hi⟩
    have hidx : (GameTheory.Finite.BimatrixPathBinaryCodec.index v).val = i :=
      congrArg Fin.val (GameTheory.Finite.BimatrixPathBinaryCodec.index_variableAt ⟨i, hi⟩)
    have hb := bimatrixNodeBasicWord_bit dimension node hk v
    rw [hidx] at hb
    change some (decide (i % 2 = 1 ∧ 3 ≤ i ∧
      ((bimatrixNodeBasicWord ![dimension, node])[i]?.getD false = true ∨ i = pointer.length))) =
      some (decide (v ∈ (insert e (GameTheory.Finite.BimatrixPathBinaryCodec.basic node)).filter
        (fun u => (ofLex u).2 = true ∧ (ofLex u).1 ≠ d)))
    rw [hb, hp]
    congr 1
    apply decide_eq_decide.mpr
    simp only [decide_eq_true_eq, Finset.mem_filter, Finset.mem_insert]
    rw [← hidx, index_val_iff]
    have hkind := payoff_index_iff d hd v
    tauto
  · simp [hk, hi, GameTheory.Finite.BimatrixPathBinaryCodec.membershipWord]
    omega
/-- The integer score agrees with the existing determinant orientation of a permitted port. -/
theorem bimatrixNodeOrientationWord_value {m n : ℕ} {A B : Fin m → Fin n → ℤ}
    {d : Fin (m + n)} (dimension node pointer determinantWord : List Bool)
    (hk : dimension.length = m + n) (hd : d.val = 0)
    (port : GameTheory.Finite.BimatrixPathPort A B d)
    (hb : GameTheory.Finite.BimatrixPathBinaryCodec.basic node = port.node.basis.basic)
    (hp : pointer.length = (GameTheory.Finite.BimatrixPathBinaryCodec.index port.entering).val)
    (hdet : binarySignedValue determinantWord =
      GameTheory.Math.IntegerCramerComputation.determinant port.node.basis.integerMatrix) :
    binarySignedValue (bimatrixNodeOrientationWord ![dimension, node, pointer, determinantWord]) =
      port.computedOrientationScore := by
  change binarySignedValue (binarySignedMul
    (binarySignedMul (binaryBirdSign (binarySubsetTally
      ((bimatrixNodeBasicWord ![dimension, node]).take pointer.length))) determinantWord)
    (binaryBirdSign (binarySubsetTally (payoffWord ![dimension, node, pointer])))) = _
  rw [binarySignedMul_value, binarySignedMul_value, binaryBirdSign_value, binaryBirdSign_value,
    binarySubsetTally_length, binarySubsetTally_length]
  rw [bimatrixNodeBasicWord_membership dimension node hk, hp,
    GameTheory.Finite.BimatrixPathBinaryCodec.membershipWord_prefix_count,
    payoffWord_membership dimension node pointer hk d hd port.entering hp,
    GameTheory.Finite.BimatrixPathBinaryCodec.membershipWord_count, hb, hdet]
  have hrank : (insert port.entering port.node.basis.basic).filter (fun u => u < port.entering) =
      port.node.basis.basic.filter (fun u => u < port.entering) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hu | hu, hlt⟩
      · subst u
        exact (lt_irrefl _ hlt).elim
      · exact ⟨hu, hlt⟩
    · rintro ⟨hu, hlt⟩
      exact ⟨Or.inr hu, hlt⟩
  unfold GameTheory.Finite.BimatrixPathPort.computedOrientationScore
    GameTheory.Math.ComplementaryPortOrder.payoffParity
  rw [hrank]

/-- Calibration by a correctly computed source score gives the canonical mathematical color. -/
theorem binaryScoreColor_eq {m n : ℕ} {A B : Fin m → Fin n → ℤ} {d : Fin (m + n)}
    (port : GameTheory.Finite.BimatrixPathPort A B d) (score sourceScore : List Bool)
    (hs : binarySignedValue score = port.computedOrientationScore)
    (hsource : binarySignedValue sourceScore =
      (GameTheory.Finite.bimatrixSourcePort A B d).computedOrientationScore) :
    binaryScoreColor ![score, sourceScore] = [port.color] := by
  rw [binaryScoreColor_value]
  change [decide (0 < binarySignedValue score * binarySignedValue sourceScore)] = _
  rw [hs, hsource]
  change [port.computedColor] = [port.color]
  rw [port.computedColor_eq]
end GameTheory.Complexity.Backend