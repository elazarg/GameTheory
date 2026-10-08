import GameTheoryComplexity.Backend.BinarySignedMatrixMachine

/-! Fixed-width, materialized Bird determinant machines.

Dimension and field widths are unary length rulers. Diagonal and product sums
normalize every stored accumulator; rows and complete stages are materialized
as packed fixed-width tables.
-/

namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham
open scoped BigOperators

private theorem reindexFn {m n : ℕ} {f : (Fin m → List Bool) → List Bool}
    (hf : Cobham f) (index : Fin m → Fin n) :
    Cobham fun v : Fin n → List Bool => f (fun i => v (index i)) :=
  Cobham.comp hf fun i => Cobham.proj (index i)

/-- Arguments: row-index ruler, column-index ruler, dimension ruler, width ruler, packed matrix. -/
def binaryBirdField (v : Fin 5 → List Bool) : List Bool :=
  binarySignedRowField ![smash (v 0) (v 2) ++ v 1, v 3, v 4]

theorem binaryBirdField_cobham : Cobham binaryBirdField :=
  (Cobham.comp₃ binarySignedRowField_cobham
    (Cobham.appendFn (Cobham.comp₂ Cobham.smash (.proj 0) (.proj 2)) (.proj 1))
    (.proj 3) (.proj 4)).of_eq fun _ => rfl

private def binaryBirdDiagTerm (v : Fin 5 → List Bool) : List Bool :=
  caseBit₀ (lenLeFlag (v 4) (v 0)) []
    (binaryBirdField ![v 0, v 0, v 2, v 1, v 3])

private theorem binaryBirdDiagTerm_cobham : Cobham binaryBirdDiagTerm := by
  have hf := reindexFn binaryBirdField_cobham (![0, 0, 2, 1, 3] : Fin 5 → Fin 5)
  have hf' : Cobham fun v : Fin 5 → List Bool => binaryBirdField ![v 0, v 0, v 2, v 1, v 3] :=
    hf.of_eq fun v => by congr 1; ext i; fin_cases i <;> rfl
  exact Cobham.iteFn (lenLeFlag_mem (.proj 4) (.proj 0)) Cobham.empty hf'

/-- Arguments: dimension, width, previous matrix, row-index ruler. -/
def binaryBirdDiagSum (v : Fin 4 → List Bool) : List Bool :=
  binarySignedSum binaryBirdDiagTerm (v 0) (v 1) ![v 1, v 0, v 2, v 3]

theorem binaryBirdDiagSum_cobham : Cobham binaryBirdDiagSum := by
  have hf := reindexFn (binarySignedSum_cobham binaryBirdDiagTerm_cobham)
    (![0, 1, 1, 0, 2, 3] : Fin 6 → Fin 4)
  exact hf.of_eq fun v => by
    change binarySignedSum binaryBirdDiagTerm (v 0) (v 1) _ = _
    congr 1
    ext i
    fin_cases i <;> rfl

private def binaryBirdCrossTerm (v : Fin 7 → List Bool) : List Bool :=
  caseBit₀ (lenLeFlag (v 5) (v 0)) []
    (binarySignedMul (binaryBirdField ![v 5, v 0, v 2, v 1, v 4])
      (binaryBirdField ![v 0, v 6, v 2, v 1, v 3]))

private theorem binaryBirdCrossTerm_cobham : Cobham binaryBirdCrossTerm := by
  have hF := reindexFn binaryBirdField_cobham (![5, 0, 2, 1, 4] : Fin 5 → Fin 7)
  have hF' : Cobham fun v : Fin 7 → List Bool => binaryBirdField ![v 5, v 0, v 2, v 1, v 4] :=
    hF.of_eq fun v => by congr 1; ext i; fin_cases i <;> rfl
  have hA := reindexFn binaryBirdField_cobham (![0, 6, 2, 1, 3] : Fin 5 → Fin 7)
  have hA' : Cobham fun v : Fin 7 → List Bool => binaryBirdField ![v 0, v 6, v 2, v 1, v 3] :=
    hA.of_eq fun v => by congr 1; ext i; fin_cases i <;> rfl
  exact Cobham.iteFn (lenLeFlag_mem (.proj 5) (.proj 0)) Cobham.empty
    ((Cobham.comp₂ binarySignedMul_cobham hF' hA').of_eq fun _ => rfl)

/-- Arguments: dimension, width, original matrix, previous matrix, row and column rulers. -/
def binaryBirdCrossSum (v : Fin 6 → List Bool) : List Bool :=
  binarySignedSum binaryBirdCrossTerm (v 0) (v 1) ![v 1, v 0, v 2, v 3, v 4, v 5]

theorem binaryBirdCrossSum_cobham : Cobham binaryBirdCrossSum := by
  have hf := reindexFn (binarySignedSum_cobham binaryBirdCrossTerm_cobham)
    (![0, 1, 1, 0, 2, 3, 4, 5] : Fin 8 → Fin 6)
  exact hf.of_eq fun v => by
    change binarySignedSum binaryBirdCrossTerm (v 0) (v 1) _ = _
    congr 1
    ext i
    fin_cases i <;> rfl

/-- One fixed-width division-free Bird entry. -/
def binaryBirdEntry (v : Fin 6 → List Bool) : List Bool :=
  binarySignedFixedAdd (v 1)
    (binarySignedFixedMul (v 1)
      (binarySignedNeg (binaryBirdDiagSum ![v 0, v 1, v 3, v 4]))
      (binaryBirdField ![v 4, v 5, v 0, v 1, v 2]))
    (binaryBirdCrossSum v)

@[simp] theorem binaryBirdEntry_length (v : Fin 6 → List Bool) :
    (binaryBirdEntry v).length = (v 1).length := binarySignedFixedAdd_length _ _ _

theorem binaryBirdEntry_cobham : Cobham binaryBirdEntry := by
  have hD := reindexFn binaryBirdDiagSum_cobham (![0, 1, 3, 4] : Fin 4 → Fin 6)
  have hD' : Cobham fun v : Fin 6 → List Bool => binaryBirdDiagSum ![v 0, v 1, v 3, v 4] :=
    hD.of_eq fun v => by congr 1; ext i; fin_cases i <;> rfl
  have hA := reindexFn binaryBirdField_cobham (![4, 5, 0, 1, 2] : Fin 5 → Fin 6)
  have hA' : Cobham fun v : Fin 6 → List Bool => binaryBirdField ![v 4, v 5, v 0, v 1, v 2] :=
    hA.of_eq fun v => by congr 1; ext i; fin_cases i <;> rfl
  have hN := Cobham.comp binarySignedNeg_cobham fun _ : Fin 1 => hD'
  exact (Cobham.comp₃ binarySignedFixedAdd_cobham (.proj 1)
    (Cobham.comp₃ binarySignedFixedMul_cobham (.proj 1) hN hA') binaryBirdCrossSum_cobham).of_eq
    fun _ => rfl

private def binaryBirdRowTerm (v : Fin 6 → List Bool) : List Bool :=
  binaryBirdEntry ![v 1, v 2, v 3, v 4, v 5, v 0]

private theorem binaryBirdRowTerm_cobham : Cobham binaryBirdRowTerm :=
  (reindexFn binaryBirdEntry_cobham (![1, 2, 3, 4, 5, 0] : Fin 6 → Fin 6)).of_eq fun v => by
    congr 1
    ext i
    fin_cases i <;> rfl

/-- Materialize one row; arguments are dimension, width, original and previous matrices, row ruler. -/
def binaryBirdRow (v : Fin 5 → List Bool) : List Bool :=
  binarySignedTable binaryBirdRowTerm (v 0) (v 1) ![v 0, v 1, v 2, v 3, v 4]

@[simp] theorem binaryBirdRow_length (v : Fin 5 → List Bool) :
    (binaryBirdRow v).length = (v 0).length * (v 1).length := binarySignedTable_length _ _ _ _

theorem binaryBirdRow_cobham : Cobham binaryBirdRow := by
  have hf := reindexFn (binarySignedTable_cobham binaryBirdRowTerm_cobham)
    (![0, 1, 0, 1, 2, 3, 4] : Fin 7 → Fin 5)
  exact hf.of_eq fun v => by
    change binarySignedTable binaryBirdRowTerm (v 0) (v 1) _ = _
    congr 1
    ext i
    fin_cases i <;> rfl

private def binaryBirdStageTerm (v : Fin 5 → List Bool) : List Bool :=
  binaryBirdRow ![v 1, v 2, v 3, v 4, v 0]

private theorem binaryBirdStageTerm_cobham : Cobham binaryBirdStageTerm :=
  (reindexFn binaryBirdRow_cobham (![1, 2, 3, 4, 0] : Fin 5 → Fin 5)).of_eq fun v => by
    congr 1
    ext i
    fin_cases i <;> rfl

/-- Materialize a complete Bird stage; arguments are dimension, width, original and previous matrices. -/
def binaryBirdStage (v : Fin 4 → List Bool) : List Bool :=
  binarySignedTable binaryBirdStageTerm (v 0) (smash (v 0) (v 1)) ![v 0, v 1, v 2, v 3]

@[simp] theorem binaryBirdStage_length (v : Fin 4 → List Bool) :
    (binaryBirdStage v).length = (v 0).length * (v 0).length * (v 1).length := by
  rw [binaryBirdStage, binarySignedTable_length, smash_length, Nat.mul_assoc]

theorem binaryBirdStage_cobham : Cobham binaryBirdStage := by
  have inputs : ∀ i : Fin 6, Cobham fun v : Fin 4 → List Bool =>
      (![v 0, smash (v 0) (v 1), v 0, v 1, v 2, v 3] : Fin 6 → List Bool) i := by
    intro i
    fin_cases i
    · exact .proj 0
    · exact Cobham.comp₂ Cobham.smash (.proj 0) (.proj 1)
    · exact .proj 0
    · exact .proj 1
    · exact .proj 2
    · exact .proj 3
  exact (Cobham.comp (binarySignedTable_cobham binaryBirdStageTerm_cobham) inputs).of_eq fun v => by
    change binarySignedTable binaryBirdStageTerm (v 0) (smash (v 0) (v 1)) _ = _
    rfl

private def binaryBirdStagesStep (v : Fin 5 → List Bool) : List Bool :=
  binaryBirdStage ![v 2, v 3, v 4, v 1]

private def binaryBirdStagesInit (v : Fin 3 → List Bool) : List Bool :=
  padTo (smash (smash (v 0) (v 0)) (v 1)) (v 2)

/-- Iterate materialized stages; the stored matrix size depends only on dimension and width. -/
def binaryBirdStages (clock dim width A : List Bool) : List Bool :=
  recNotation binaryBirdStagesInit binaryBirdStagesStep binaryBirdStagesStep clock ![dim, width, A]

@[simp] theorem binaryBirdStages_length (clock dim width A : List Bool) :
    (binaryBirdStages clock dim width A).length = dim.length * dim.length * width.length := by
  cases clock with
  | nil => simp [binaryBirdStages, binaryBirdStagesInit, smash_length]
  | cons b r =>
    simp only [binaryBirdStages, recNotation_cons, Bool.cond_self, binaryBirdStagesStep,
      binaryBirdStage_length]
    rfl

theorem binaryBirdStages_cobham : Cobham fun v : Fin 4 → List Bool =>
    binaryBirdStages (v 0) (v 1) (v 2) (v 3) := by
  have hg : Cobham binaryBirdStagesInit :=
    Cobham.padFn (Cobham.comp₂ Cobham.smash
      (Cobham.comp₂ Cobham.smash (.proj 0) (.proj 0)) (.proj 1)) (.proj 2)
  have hs : Cobham binaryBirdStagesStep :=
    (reindexFn binaryBirdStage_cobham (![2, 3, 4, 1] : Fin 4 → Fin 5)).of_eq fun v => by
      congr 1
      ext i
      fin_cases i <;> rfl
  have hj : Cobham fun v : Fin 4 → List Bool => smash (smash (v 1) (v 1)) (v 2) :=
    Cobham.comp₂ Cobham.smash (Cobham.comp₂ Cobham.smash (.proj 1) (.proj 1)) (.proj 2)
  exact (Cobham.boundedRec hg hs hs hj (fun r v => by
    have hv : v = ![v 0, v 1, v 2] := by ext i; fin_cases i <;> rfl
    rw [hv]
    change (binaryBirdStages r (v 0) (v 1) (v 2)).length ≤ _
    rw [binaryBirdStages_length, smash_length, smash_length]
    exact le_rfl)).of_eq fun v => by
      congr 1
      ext i
      fin_cases i <;> rfl

theorem binaryBirdStages_mem_FPn :
    FPn (fun v : Fin 4 → List Bool => binaryBirdStages (v 0) (v 1) (v 2) (v 3)) :=
  cobham_iff_FPn.mp binaryBirdStages_cobham

private def binaryBirdSignStep (v : Fin 2 → List Bool) : List Bool :=
  notBit (bitAt [] (v 1)) ++ [true]

/-- A two-bit signed word for `(-1)` raised to the clock length. -/
def binaryBirdSign (clock : List Bool) : List Bool :=
  recNotation (fun _ : Fin 0 → List Bool => [false, true])
    binaryBirdSignStep binaryBirdSignStep clock ![]

private theorem sign_headFlag (x : List Bool) : bitAt [] x = [x.headD false] := by
  cases x with
  | nil => rfl
  | cons b x => cases b <;> rfl

@[simp] theorem binaryBirdSign_length (clock : List Bool) : (binaryBirdSign clock).length = 2 := by
  cases clock with
  | nil => rfl
  | cons b r =>
    simp only [binaryBirdSign, recNotation_cons, Bool.cond_self, binaryBirdSignStep]
    change (notBit (bitAt [] (binaryBirdSign r)) ++ [true]).length = 2
    rw [sign_headFlag]
    generalize (binaryBirdSign r).headD false = a
    cases a <;> rfl

private theorem binaryBirdSign_tail (clock : List Bool) : (binaryBirdSign clock).tail = [true] := by
  cases clock with
  | nil => rfl
  | cons b r =>
    simp only [binaryBirdSign, recNotation_cons, Bool.cond_self, binaryBirdSignStep]
    change (notBit (bitAt [] (binaryBirdSign r)) ++ [true]).tail = [true]
    rw [sign_headFlag]
    generalize (binaryBirdSign r).headD false = a
    cases a <;> rfl

theorem binaryBirdSign_value (clock : List Bool) :
    binarySignedValue (binaryBirdSign clock) = (-1 : ℤ) ^ clock.length := by
  induction clock with
  | nil => rfl
  | cons b r ih =>
    simp only [binaryBirdSign, recNotation_cons, Bool.cond_self, binaryBirdSignStep]
    change binarySignedValue (notBit (bitAt [] (binaryBirdSign r)) ++ [true]) = _
    have he : notBit (bitAt [] (binaryBirdSign r)) ++ [true] = binarySignedNeg (binaryBirdSign r) := by
      rw [binarySignedNeg, binaryBirdSign_tail]
    rw [he, binarySignedNeg_value, ih, List.length_cons, pow_succ]
    ring

theorem binaryBirdSign_cobham : Cobham fun v : Fin 1 → List Bool => binaryBirdSign (v 0) := by
  have hs : Cobham binaryBirdSignStep := Cobham.appendFn
    (Cobham.notFn (Cobham.comp₂ Cobham.bitAtFn (Cobham.const []) (.proj 1))) (Cobham.const [true])
  exact (Cobham.boundedRec (Cobham.const [false, true]) hs hs
    (Cobham.const [false, false]) (fun r v => by
      have hv : v = (![] : Fin 0 → List Bool) := by ext i; exact Fin.elim0 i
      rw [hv]
      exact (binaryBirdSign_length r).le)).of_eq fun v => by
        change recNotation _ _ _ (v 0) (Fin.tail v) = recNotation _ _ _ (v 0) ![]
        congr 1
        ext i
        exact Fin.elim0 i

/-- Fixed-width division-free determinant computation; arguments are dimension, width, packed matrix. -/
def binaryBirdDeterminant (v : Fin 3 → List Bool) : List Bool :=
  caseBit₀ (nonemptyFlag (v 0))
    (binarySignedFixedMul (v 1) (binaryBirdSign (v 0).tail)
      (binaryBirdField ![[], [], v 0, v 1, binaryBirdStages (v 0).tail (v 0) (v 1) (v 2)]))
    (binarySignedFixed (v 1) [false, true])

@[simp] theorem binaryBirdDeterminant_length (v : Fin 3 → List Bool) :
    (binaryBirdDeterminant v).length = (v 1).length := by
  unfold binaryBirdDeterminant
  cases h : v 0 with
  | nil => simp
  | cons b r => simp

theorem binaryBirdDeterminant_cobham : Cobham binaryBirdDeterminant := by
  have hs : Cobham fun v : Fin 3 → List Bool => binaryBirdStages (v 0).tail (v 0) (v 1) (v 2) := by
    have inputs : ∀ i : Fin 4, Cobham fun v : Fin 3 → List Bool =>
        (![ (v 0).tail, v 0, v 1, v 2] : Fin 4 → List Bool) i := by
      intro i
      fin_cases i
      · exact Cobham.tailFn (.proj 0)
      · exact .proj 0
      · exact .proj 1
      · exact .proj 2
    exact (Cobham.comp binaryBirdStages_cobham inputs).of_eq fun _ => rfl
  have hfield : Cobham fun v : Fin 3 → List Bool =>
      binaryBirdField ![[], [], v 0, v 1, binaryBirdStages (v 0).tail (v 0) (v 1) (v 2)] := by
    apply Cobham.comp binaryBirdField_cobham
    intro i
    fin_cases i
    · exact Cobham.empty
    · exact Cobham.empty
    · exact .proj 0
    · exact .proj 1
    · exact hs
  have hsign : Cobham fun v : Fin 3 → List Bool => binaryBirdSign (v 0).tail :=
    (Cobham.comp binaryBirdSign_cobham fun _ : Fin 1 => Cobham.tailFn (.proj 0)).of_eq fun _ => rfl
  exact Cobham.iteFn (Cobham.nonemptyFn (.proj 0))
    ((Cobham.comp₃ binarySignedFixedMul_cobham (.proj 1) hsign hfield).of_eq fun _ => rfl)
    ((Cobham.comp₂ binarySignedFixed_cobham (.proj 1) (Cobham.const [false, true])).of_eq fun _ => rfl)

theorem binaryBirdDeterminant_mem_FPn : FPn binaryBirdDeterminant :=
  cobham_iff_FPn.mp binaryBirdDeterminant_cobham

theorem binaryBirdField_value (v : Fin 5 → List Bool) :
    binarySignedValue (binaryBirdField v) =
      binarySignedRowValue (v 3) (v 4) ((v 0).length * (v 2).length + (v 1).length) := by
  change binarySignedValue (((v 4).drop ((smash (v 0) (v 2) ++ v 1).length * (v 3).length)).take (v 3).length) = _
  rw [List.length_append, smash_length]
  rfl

private theorem binaryBirdDiagTerm_value (v : Fin 5 → List Bool) :
    binarySignedValue (binaryBirdDiagTerm v) =
      if (v 4).length < (v 0).length then
        binarySignedRowValue (v 1) (v 3) ((v 0).length * (v 2).length + (v 0).length) else 0 := by
  rcases lenLeFlag_flag (v 4) (v 0) with h | h
  · have hk : ¬(v 4).length < (v 0).length := not_lt_of_ge ((lenLeFlag_eq_true_iff _ _).mp h)
    simp [binaryBirdDiagTerm, h, caseBit₀, hk, binarySignedValue, Nat.fromBitsLE, Nat.fromBits]
  · have hk : (v 4).length < (v 0).length := by
      by_contra hn
      have ht := (lenLeFlag_eq_true_iff (v 4) (v 0)).mpr (by omega)
      simp [h] at ht
    simp only [binaryBirdDiagTerm, h, caseBit₀, hk, ↓reduceIte]
    exact binaryBirdField_value _

theorem binaryBirdDiagSum_value (v : Fin 4 → List Bool) (hr : 0 < (v 1).length)
    (hbound : ∀ t ≤ (v 0).length,
      (∑ k ∈ Finset.range t, if (v 3).length < k then
        binarySignedRowValue (v 1) (v 2) (k * (v 0).length + k) else 0).natAbs <
          2 ^ ((v 1).length - 1)) :
    binarySignedValue (binaryBirdDiagSum v) =
      ∑ k ∈ Finset.range (v 0).length, if (v 3).length < k then
        binarySignedRowValue (v 1) (v 2) (k * (v 0).length + k) else 0 := by
  apply binarySignedSum_value _ _ _ _ _ hr _ hbound
  intro r
  exact binaryBirdDiagTerm_value _
private theorem binaryBirdCrossTerm_value (v : Fin 7 → List Bool) :
    binarySignedValue (binaryBirdCrossTerm v) =
      if (v 5).length < (v 0).length then
        binarySignedRowValue (v 1) (v 4) ((v 5).length * (v 2).length + (v 0).length) *
        binarySignedRowValue (v 1) (v 3) ((v 0).length * (v 2).length + (v 6).length) else 0 := by
  rcases lenLeFlag_flag (v 5) (v 0) with h | h
  · have hk : ¬(v 5).length < (v 0).length := not_lt_of_ge ((lenLeFlag_eq_true_iff _ _).mp h)
    simp [binaryBirdCrossTerm, h, caseBit₀, hk, binarySignedValue, Nat.fromBitsLE, Nat.fromBits]
  · have hk : (v 5).length < (v 0).length := by
      by_contra hn
      have ht := (lenLeFlag_eq_true_iff (v 5) (v 0)).mpr (by omega)
      simp [h] at ht
    simp only [binaryBirdCrossTerm, h, caseBit₀, hk, ↓reduceIte, Bool.cond_false, binarySignedMul_value,
      binaryBirdField_value]
    rfl

theorem binaryBirdCrossSum_value (v : Fin 6 → List Bool) (hr : 0 < (v 1).length)
    (hbound : ∀ t ≤ (v 0).length,
      (∑ k ∈ Finset.range t, if (v 4).length < k then
        binarySignedRowValue (v 1) (v 3) ((v 4).length * (v 0).length + k) *
        binarySignedRowValue (v 1) (v 2) (k * (v 0).length + (v 5).length) else 0).natAbs <
          2 ^ ((v 1).length - 1)) :
    binarySignedValue (binaryBirdCrossSum v) =
      ∑ k ∈ Finset.range (v 0).length, if (v 4).length < k then
        binarySignedRowValue (v 1) (v 3) ((v 4).length * (v 0).length + k) *
        binarySignedRowValue (v 1) (v 2) (k * (v 0).length + (v 5).length) else 0 := by
  apply binarySignedSum_value _ _ _ _ _ hr _ hbound
  intro r
  exact binaryBirdCrossTerm_value _
theorem binaryBirdEntry_value (v : Fin 6 → List Bool) (D P : ℤ)
    (hr : 0 < (v 1).length)
    (hD : binarySignedValue (binaryBirdDiagSum ![v 0, v 1, v 3, v 4]) = D)
    (hP : binarySignedValue (binaryBirdCrossSum v) = P)
    (hmul : (-D * binarySignedRowValue (v 1) (v 2)
      ((v 4).length * (v 0).length + (v 5).length)).natAbs < 2 ^ ((v 1).length - 1))
    (hadd : (-D * binarySignedRowValue (v 1) (v 2)
      ((v 4).length * (v 0).length + (v 5).length) + P).natAbs < 2 ^ ((v 1).length - 1)) :
    binarySignedValue (binaryBirdEntry v) =
      -D * binarySignedRowValue (v 1) (v 2)
        ((v 4).length * (v 0).length + (v 5).length) + P := by
  have hF : binarySignedValue (binaryBirdField ![v 4, v 5, v 0, v 1, v 2]) =
      binarySignedRowValue (v 1) (v 2) ((v 4).length * (v 0).length + (v 5).length) :=
    binaryBirdField_value _
  have hM : binarySignedValue (binarySignedFixedMul (v 1)
      (binarySignedNeg (binaryBirdDiagSum ![v 0, v 1, v 3, v 4]))
      (binaryBirdField ![v 4, v 5, v 0, v 1, v 2])) =
      -D * binarySignedRowValue (v 1) (v 2)
        ((v 4).length * (v 0).length + (v 5).length) := by
    rw [binarySignedFixedMul_value _ _ _ hr]
    · rw [binarySignedNeg_value, hD, hF]
    · simpa only [binarySignedNeg_value, hD, hF] using hmul
  unfold binaryBirdEntry
  rw [binarySignedFixedAdd_value _ _ _ hr]
  · rw [hM, hP]
  · simpa only [hM, hP] using hadd
theorem binaryBirdRow_field (v : Fin 5 → List Bool) (j : ℕ) (hj : j < (v 0).length) :
    ((binaryBirdRow v).drop (j * (v 1).length)).take (v 1).length =
      binaryBirdEntry ![v 0, v 1, v 2, v 3, v 4, (v 0).drop ((v 0).length - j)] := by
  rw [binaryBirdRow, binarySignedTable_field _ _ _ _ j hj]
  change binarySignedFixed (v 1) (binaryBirdEntry _) = _
  exact binarySignedFixed_eq_of_length _ _ (binaryBirdEntry_length _)

theorem binaryBirdStage_row (v : Fin 4 → List Bool) (i : ℕ) (hi : i < (v 0).length) :
    ((binaryBirdStage v).drop (i * ((v 0).length * (v 1).length))).take
      ((v 0).length * (v 1).length) =
      binaryBirdRow ![v 0, v 1, v 2, v 3, (v 0).drop ((v 0).length - i)] := by
  have h := binarySignedTable_field binaryBirdStageTerm (v 0) (smash (v 0) (v 1))
    ![v 0, v 1, v 2, v 3] i hi
  rw [smash_length] at h
  change _ = binarySignedFixed (smash (v 0) (v 1)) (binaryBirdRow _) at h
  rw [binarySignedFixed_eq_of_length] at h
  · exact h
  · rw [binaryBirdRow_length, smash_length]
    rfl

theorem binaryBirdStage_field (v : Fin 4 → List Bool) (i j : ℕ)
    (hi : i < (v 0).length) (hj : j < (v 0).length) :
    ((binaryBirdStage v).drop ((i * (v 0).length + j) * (v 1).length)).take (v 1).length =
      binaryBirdEntry ![v 0, v 1, v 2, v 3,
        (v 0).drop ((v 0).length - i), (v 0).drop ((v 0).length - j)] := by
  have h := congrArg (fun x : List Bool => (x.drop (j * (v 1).length)).take (v 1).length)
    (binaryBirdStage_row v i hi)
  rw [List.drop_take, List.drop_drop, List.take_take] at h
  have hm : (v 1).length ≤ (v 0).length * (v 1).length - j * (v 1).length := by
    have hb := Nat.mul_le_mul_right (v 1).length (Nat.succ_le_of_lt hj)
    rw [Nat.succ_mul] at hb
    omega
  rw [Nat.min_eq_left hm, ← Nat.mul_assoc, ← Nat.add_mul] at h
  exact h.trans (binaryBirdRow_field ![v 0, v 1, v 2, v 3, (v 0).drop ((v 0).length - i)] j hj)
@[simp] theorem binaryBirdStages_nil (dim width A : List Bool) :
    binaryBirdStages [] dim width A = padTo (smash (smash dim dim) width) A := rfl

@[simp] theorem binaryBirdStages_cons (b : Bool) (r dim width A : List Bool) :
    binaryBirdStages (b :: r) dim width A =
      binaryBirdStage ![dim, width, A, binaryBirdStages r dim width A] := by
  simp only [binaryBirdStages, recNotation_cons, Bool.cond_self, binaryBirdStagesStep]
  rfl
end GameTheory.Complexity.Backend
