import GameTheoryComplexity.Backend.BinaryBirdDeterminantMachine
import GameTheory.Math.BirdIterationBounds
import GameTheory.Math.TabulatedBirdDeterminant

/-! Correctness of the fixed-width Bird machine under explicit storage and magnitude bounds. -/

namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham
open scoped BigOperators

/-- Interpret a packed table using its dimension and signed field width. -/
def binaryBirdMatrix (dim width packed : List Bool) :
    Matrix (Fin dim.length) (Fin dim.length) ℤ :=
  fun i j => binarySignedRowValue width packed (i.val * dim.length + j.val)

private theorem prefix_sum_bound (f : ℕ → ℤ) (n t T : ℕ) (ht : t ≤ n)
    (hf : ∀ k < n, (f k).natAbs ≤ T) :
    (∑ k ∈ Finset.range t, f k).natAbs ≤ n * T := by
  calc
    _ ≤ ∑ k ∈ Finset.range t, (f k).natAbs := Int.natAbs_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range t, T := Finset.sum_le_sum (fun k hk =>
      hf k ((Finset.mem_range.mp hk).trans_le ht))
    _ = t * T := by simp
    _ ≤ n * T := Nat.mul_le_mul_right T ht

private theorem tail_sum_eq (dim width F : List Bool) (i : Fin dim.length) :
    (∑ k ∈ Finset.range dim.length, if i.val < k then
      binarySignedRowValue width F (k * dim.length + k) else 0) =
    ∑ k ∈ Finset.Ioi i, binaryBirdMatrix dim width F k k := by
  rw [← Fin.sum_univ_eq_sum_range]
  simp [binaryBirdMatrix, ← Finset.sum_filter, Finset.filter_lt_eq_Ioi]

private theorem tail_product_eq (dim width A F : List Bool) (i j : Fin dim.length) :
    (∑ k ∈ Finset.range dim.length, if i.val < k then
      binarySignedRowValue width F (i.val * dim.length + k) *
      binarySignedRowValue width A (k * dim.length + j.val) else 0) =
    ∑ k ∈ Finset.Ioi i, binaryBirdMatrix dim width F i k * binaryBirdMatrix dim width A k j := by
  rw [← Fin.sum_univ_eq_sum_range]
  simp [binaryBirdMatrix, ← Finset.sum_filter, Finset.filter_lt_eq_Ioi]

end GameTheory.Complexity.Backend
namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham
open scoped BigOperators

theorem binaryBirdEntry_eq_step (dim width A F : List Bool) (B T : ℕ)
    (i j : Fin dim.length) (hr : 0 < width.length) (hB : 0 < B)
    (hA : ∀ i j, (binaryBirdMatrix dim width A i j).natAbs ≤ B)
    (hF : ∀ i j, (binaryBirdMatrix dim width F i j).natAbs ≤ T)
    (hcap : 2 * dim.length * T * B < 2 ^ (width.length - 1)) :
    binarySignedValue (binaryBirdEntry ![dim, width, A, F,
      dim.drop (dim.length - i.val), dim.drop (dim.length - j.val)]) =
      BirdDet.Spec.stepEntry (binaryBirdMatrix dim width A) (binaryBirdMatrix dim width F) i j := by
  let ri := dim.drop (dim.length - i.val)
  let rj := dim.drop (dim.length - j.val)
  have hi : ri.length = i.val := by dsimp [ri]; rw [List.length_drop]; omega
  have hj : rj.length = j.val := by dsimp [rj]; rw [List.length_drop]; omega
  let D := ∑ k ∈ Finset.Ioi i, binaryBirdMatrix dim width F k k
  let P := ∑ k ∈ Finset.Ioi i, binaryBirdMatrix dim width F i k * binaryBirdMatrix dim width A k j
  have hDb : D.natAbs ≤ dim.length * T :=
    GameTheory.Math.BirdIterationBounds.diagonal_sum_bound _ T hF _
  have hPb : P.natAbs ≤ dim.length * T * B :=
    GameTheory.Math.BirdIterationBounds.row_product_sum_bound _ _ B T hA hF _ _ _
  have hs : dim.length * T ≤ 2 * dim.length * T * B := by
    have hh : dim.length * T ≤ (dim.length * T) * B :=
      Nat.le_mul_of_pos_right _ hB
    nlinarith
  have hp : dim.length * T * B ≤ 2 * dim.length * T * B := by nlinarith
  have hdiag : binarySignedValue (binaryBirdDiagSum ![dim, width, F, ri]) = D := by
    rw [binaryBirdDiagSum_value _ hr]
    · change (∑ k ∈ Finset.range dim.length, if ri.length < k then binarySignedRowValue width F (k * dim.length + k) else 0) = D
      rw [hi]
      exact tail_sum_eq dim width F i
    · intro t ht
      change (∑ k ∈ Finset.range t, if ri.length < k then
        binarySignedRowValue width F (k * dim.length + k) else 0).natAbs < _
      apply (prefix_sum_bound _ dim.length t T ht _).trans_lt (hs.trans_lt hcap)
      intro k hk
      split_ifs
      · exact hF ⟨k, hk⟩ ⟨k, hk⟩
      · simp
  have hcross : binarySignedValue (binaryBirdCrossSum ![dim, width, A, F, ri, rj]) = P := by
    rw [binaryBirdCrossSum_value _ hr]
    · change (∑ k ∈ Finset.range dim.length, if ri.length < k then binarySignedRowValue width F (ri.length * dim.length + k) * binarySignedRowValue width A (k * dim.length + rj.length) else 0) = P
      rw [hi, hj]
      exact tail_product_eq dim width A F i j
    · intro t ht
      change (∑ k ∈ Finset.range t, if ri.length < k then
        binarySignedRowValue width F (ri.length * dim.length + k) *
        binarySignedRowValue width A (k * dim.length + rj.length) else 0).natAbs < _
      apply (prefix_sum_bound _ dim.length t (T * B) ht _).trans_lt _
      · intro k hk
        split_ifs
        · rw [hi, hj, Int.natAbs_mul]
          exact Nat.mul_le_mul (hF i ⟨k, hk⟩) (hA ⟨k, hk⟩ j)
        · simp
      · change dim.length * (T * B) < 2 ^ (width.length - 1)
        simpa only [Nat.mul_assoc] using hp.trans_lt hcap
  have hm : (-D * binarySignedRowValue width A (ri.length * dim.length + rj.length)).natAbs <
      2 ^ (width.length - 1) := by
    rw [hi, hj, Int.natAbs_mul, Int.natAbs_neg]
    exact (Nat.mul_le_mul hDb (hA i j)).trans_lt (hp.trans_lt hcap)
  have ha : (-D * binarySignedRowValue width A (ri.length * dim.length + rj.length) + P).natAbs <
      2 ^ (width.length - 1) := by
    rw [hi, hj]
    exact (GameTheory.Math.BirdIterationBounds.step_bound _ _ B T hA hF i j).trans_lt hcap
  have he := binaryBirdEntry_value ![dim, width, A, F, ri, rj] D P hr hdiag hcross hm ha
  change binarySignedValue (binaryBirdEntry ![dim, width, A, F, ri, rj]) = -D * binarySignedRowValue width A (ri.length * dim.length + rj.length) + P at he
  rw [hi, hj] at he
  exact he
end GameTheory.Complexity.Backend

namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham
open scoped BigOperators

theorem binaryBirdStage_eq_step (dim width A F : List Bool) (B T : ℕ)
    (hr : 0 < width.length) (hB : 0 < B)
    (hA : ∀ i j, (binaryBirdMatrix dim width A i j).natAbs ≤ B)
    (hF : ∀ i j, (binaryBirdMatrix dim width F i j).natAbs ≤ T)
    (hcap : 2 * dim.length * T * B < 2 ^ (width.length - 1)) :
    binaryBirdMatrix dim width (binaryBirdStage ![dim, width, A, F]) =
      BirdDet.Spec.stepEntry (binaryBirdMatrix dim width A) (binaryBirdMatrix dim width F) := by
  ext i j
  exact (congrArg binarySignedValue (binaryBirdStage_field ![dim, width, A, F] i.val j.val i.isLt j.isLt)).trans
    (binaryBirdEntry_eq_step dim width A F B T i j hr hB hA hF hcap)

theorem binaryBirdStages_eq_spec (clock dim width A : List Bool) (h : ℕ)
    (hw : width.length = GameTheory.Math.BirdIterationBounds.workWidth dim.length h)
    (hlen : A.length = dim.length * dim.length * width.length)
    (hA : ∀ i j, (binaryBirdMatrix dim width A i j).natAbs ≤ 2 ^ h)
    (ht : clock.length ≤ dim.length) :
    binaryBirdMatrix dim width (binaryBirdStages clock dim width A) =
      (BirdDet.Spec.stepEntry (binaryBirdMatrix dim width A))^[clock.length]
        (binaryBirdMatrix dim width A) := by
  induction clock with
  | nil =>
    have hl : (smash (smash dim dim) width).length = A.length := by
      rw [smash_length, smash_length, hlen]
    have hp : padTo (smash (smash dim dim) width) A = A := by
      rw [padTo_eq_append _ _ hl.ge, hl, Nat.sub_self]
      simp
    change binaryBirdMatrix dim width (padTo (smash (smash dim dim) width) A) = binaryBirdMatrix dim width A
    rw [hp]
  | cons b r ih =>
    have hrt : r.length ≤ dim.length := by simp only [List.length_cons] at ht; omega
    have hi := ih hrt
    have hF : ∀ i j,
        (binaryBirdMatrix dim width (binaryBirdStages r dim width A) i j).natAbs ≤
          2 ^ GameTheory.Math.BirdIterationBounds.width dim.length h := by
      rw [hi]
      intro i j
      exact (GameTheory.Math.BirdIterationBounds.stages_natAbs_lt_two_pow _ h r.length hA hrt i j).le
    have hr : 0 < width.length := by rw [hw]; exact GameTheory.Math.BirdIterationBounds.workWidth_pos _ _
    have hc : 2 * dim.length * 2 ^ GameTheory.Math.BirdIterationBounds.width dim.length h * 2 ^ h <
        2 ^ (width.length - 1) := by
      rw [hw]
      exact GameTheory.Math.BirdIterationBounds.workWidth_capacity _ _
    have hs := binaryBirdStage_eq_step dim width A (binaryBirdStages r dim width A)
      (2 ^ h) (2 ^ GameTheory.Math.BirdIterationBounds.width dim.length h) hr (by positivity) hA hF hc
    rw [binaryBirdStages_cons]
    rw [hs, hi, List.length_cons, Function.iterate_succ_apply']
end GameTheory.Complexity.Backend




namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham
open scoped BigOperators

theorem binaryBirdDeterminant_value (dim width A : List Bool) (h : ℕ)
    (hw : width.length = GameTheory.Math.BirdIterationBounds.workWidth dim.length h)
    (hlen : A.length = dim.length * dim.length * width.length)
    (hA : ∀ i j, (binaryBirdMatrix dim width A i j).natAbs ≤ 2 ^ h) :
    binarySignedValue (binaryBirdDeterminant ![dim, width, A]) =
      (binaryBirdMatrix dim width A).det := by
  have hr : 0 < width.length := by rw [hw]; exact GameTheory.Math.BirdIterationBounds.workWidth_pos _ _
  cases dim with
  | nil =>
    have hc : 1 < 2 ^ (width.length - 1) := by
      have hl : 2 ≤ width.length := by rw [hw]; unfold GameTheory.Math.BirdIterationBounds.workWidth; omega
      exact Nat.one_lt_two_pow (by omega)
    change binarySignedValue (binarySignedFixed width [false, true]) = _
    rw [binarySignedFixed_value _ _ hr (by exact hc)]
    simp [binarySignedValue, Nat.fromBitsLE, Nat.fromBits]
  | cons b r =>
    let M := binaryBirdMatrix (b :: r) width A
    let z : Fin (b :: r).length := ⟨0, by simp⟩
    have hs := binaryBirdStages_eq_spec r (b :: r) width A h hw hlen hA (by simp)
    have hf : binarySignedValue (binaryBirdField
        ![[], [], b :: r, width, binaryBirdStages r (b :: r) width A]) =
        ((BirdDet.Spec.stepEntry M)^[r.length] M) z z := by
      have h := congrArg (fun F => F z z) hs
      have hd := binaryBirdField_value ![[], [], b :: r, width, binaryBirdStages r (b :: r) width A]
      change binarySignedValue (binaryBirdField ![[], [], b :: r, width, binaryBirdStages r (b :: r) width A]) = binarySignedRowValue width (binaryBirdStages r (b :: r) width A) (0 * (b :: r).length + 0) at hd
      simp only [Nat.zero_mul, Nat.add_zero] at hd
      have hh : binarySignedRowValue width (binaryBirdStages r (b :: r) width A) 0 = ((BirdDet.Spec.stepEntry M)^[r.length] M) z z := by
        simpa only [binaryBirdMatrix, z, Nat.zero_mul, Nat.add_zero] using h
      exact hd.trans hh
    have hz : (((BirdDet.Spec.stepEntry M)^[r.length] M) z z).natAbs <
        2 ^ (width.length - 1) := by
      have hb := GameTheory.Math.BirdIterationBounds.stages_natAbs_lt_two_pow M h r.length hA (by simp) z z
      have he : GameTheory.Math.BirdIterationBounds.width (b :: r).length h < width.length - 1 := by
        rw [hw]
        exact GameTheory.Math.BirdIterationBounds.stageWidth_lt_workWidth _ _
      exact hb.trans (Nat.pow_lt_pow_right (by decide) he)
    have hm : (binarySignedValue (binaryBirdSign r) * binarySignedValue (binaryBirdField
        ![[], [], b :: r, width, binaryBirdStages r (b :: r) width A])).natAbs <
        2 ^ (width.length - 1) := by
      rw [binaryBirdSign_value, hf, Int.natAbs_mul, Int.natAbs_pow]
      simpa using hz
    unfold binaryBirdDeterminant
    change binarySignedValue (caseBit₀ (nonemptyFlag (b :: r)) (binarySignedFixedMul width (binaryBirdSign r) (binaryBirdField ![[], [], b :: r, width, binaryBirdStages r (b :: r) width A])) (binarySignedFixed width [false, true])) = _
    rw [nonemptyFlag_cons]
    simp only [caseBit₀, Bool.cond_true]
    rw [binarySignedFixedMul_value _ _ _ hr hm, binaryBirdSign_value, hf]
    exact (GameTheory.Math.TabulatedBirdDeterminant.det_eq_last_stage M (by simp)).symm
end GameTheory.Complexity.Backend
