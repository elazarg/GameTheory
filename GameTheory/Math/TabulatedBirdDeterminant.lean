import Mathlib.LinearAlgebra.Matrix.Determinant.Bird.Correctness

/-! # Bird determinants with materialized recurrence stages

Every recurrence stage is stored as a flat row-major array. Subsequent entries
read the stored values, avoiding repeated evaluation of nested scalar recurrence
functions. Mathlib's Bird correctness theorem supplies the determinant identity.
-/

namespace GameTheory.Math.TabulatedBirdDeterminant

variable {R : Type*} [CommRing R] {n : ℕ}

/-- Materialize a square array in row-major order. -/
def table (n : ℕ) (f : ℕ → ℕ → R) : Array R :=
  Array.ofFn fun p : Fin (n * n) => f (p.val / n) (p.val % n)

omit [CommRing R] in
@[simp] theorem table_size (n : ℕ) (f : ℕ → ℕ → R) : (table n f).size = n * n :=
  Array.size_ofFn

/-- Materialize one scalar Bird recurrence step. -/
def step (n : ℕ) (A F : Array R) : Array R :=
  table n (BirdDet.stepEntry n A (BirdDet.get n F))

@[simp] theorem step_size (n : ℕ) (A F : Array R) : (step n A F).size = n * n :=
  table_size _ _

theorem get_table (f : ℕ → ℕ → R) (i j : Fin n) :
    BirdDet.get n (table n f) i.val j.val = f i.val j.val := by
  have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
  have hrow : n * i.val + n ≤ n * n := by
    rw [← Nat.mul_succ]
    exact Nat.mul_le_mul_left n (Nat.succ_le_of_lt i.isLt)
  have hidx : n * i.val + j.val < n * n :=
    (Nat.add_lt_add_left j.isLt (n * i.val)).trans_le hrow
  rw [BirdDet.get_eq, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem
    (by simpa only [table_size] using hidx)]
  simp only [table, Option.getD_some, Array.getElem_ofFn]
  rw [Nat.mul_add_div hn, Nat.div_eq_of_lt j.isLt, Nat.add_zero,
    Nat.mul_add_mod, Nat.mod_eq_of_lt j.isLt]

/-- Stored Bird stages, initialized by the input array. -/
def stages (n : ℕ) (A : Array R) : ℕ → Array R
  | 0 => A
  | t + 1 => step n A (stages n A t)

theorem stages_size (A : Array R) (hA : A.size = n * n) (t : ℕ) :
    (stages n A t).size = n * n := by
  cases t
  · exact hA
  · exact step_size _ _ _

private theorem sumFrom_congr (f g : ℕ → R) (hf : ∀ k, k < n → f k = g k) (lo : ℕ) :
    BirdDet.sumFrom n lo f = BirdDet.sumFrom n lo g := by
  induction lo using BirdDet.sumFrom_induct n with
  | step lo hlo ih => rw [BirdDet.sumFrom_step n lo f hlo,
      BirdDet.sumFrom_step n lo g hlo, hf lo hlo, ih]
  | stop lo hlo => rw [BirdDet.sumFrom_stop n lo f hlo, BirdDet.sumFrom_stop n lo g hlo]

/-- The materialized stages agree with Mathlib's scalar recurrence on valid indices. -/
theorem stages_get_eq_iterate (A : Array R) (t : ℕ) (i j : Fin n) :
    BirdDet.get n (stages n A t) i.val j.val =
      ((BirdDet.stepEntry n A)^[t] (BirdDet.get n A)) i.val j.val := by
  induction t generalizing i j with
  | zero => rfl
  | succ t ih =>
    rw [stages, step, get_table, Function.iterate_succ_apply']
    let F := (BirdDet.stepEntry n A)^[t] (BirdDet.get n A)
    have hdiag : BirdDet.sumFrom n (i.val + 1)
        (fun k => BirdDet.get n (stages n A t) k k) =
        BirdDet.sumFrom n (i.val + 1) (fun k => F k k) := by
      apply sumFrom_congr
      intro k hk
      exact ih ⟨k, hk⟩ ⟨k, hk⟩
    have hrow : BirdDet.sumFrom n (i.val + 1)
        (fun k => BirdDet.get n (stages n A t) i.val k * BirdDet.get n A k j.val) =
        BirdDet.sumFrom n (i.val + 1) (fun k => F i.val k * BirdDet.get n A k j.val) := by
      apply sumFrom_congr
      intro k hk
      exact congrArg (· * BirdDet.get n A k j.val) (ih i ⟨k, hk⟩)
    simp only [BirdDet.stepEntry_eq]
    rw [hdiag, hrow]

private theorem sumFrom_eq_sum_Ico (f : ℕ → R) (lo : ℕ) :
    BirdDet.sumFrom n lo f = ∑ k ∈ Finset.Ico lo n, f k := by
  induction lo using BirdDet.sumFrom_induct n with
  | step lo hlo ih => rw [BirdDet.sumFrom_step n lo f hlo, ih,
      ← Finset.sum_eq_sum_Ico_succ_bot hlo f]
  | stop lo hlo => rw [BirdDet.sumFrom_stop n lo f hlo, Finset.Ico_eq_empty hlo,
      Finset.sum_empty]

private theorem sumFrom_fin_tail (i : Fin n) (f : ℕ → R) :
    BirdDet.sumFrom n (i.val + 1) f = ∑ k ∈ Finset.Ioi i, f k.val := by
  rw [sumFrom_eq_sum_Ico]
  calc
    (∑ k ∈ Finset.Ico (i.val + 1) n, f k) =
        ∑ k ∈ (Finset.range n).filter (i.val < ·), f k := by
      congr
      ext k
      simp
      omega
    _ = ∑ k ∈ Finset.range n, if i.val < k then f k else 0 := by rw [Finset.sum_filter]
    _ = ∑ k : Fin n, if i.val < k.val then f k.val else 0 := by
      rw [← Fin.sum_univ_eq_sum_range]
    _ = ∑ k ∈ Finset.Ioi i, f k.val := by
      simp [← Finset.sum_filter, Finset.filter_lt_eq_Ioi]

/-- Stored recurrence entries agree with the independent mathematical Bird stages. -/
theorem stages_get_eq_spec (A : Array R) (hA : A.size = n * n) (t : ℕ) (i j : Fin n) :
    BirdDet.get n (stages n A t) i.val j.val =
      (BirdDet.Spec.stepEntry (Matrix.ofArray A hA))^[t] (Matrix.ofArray A hA) i j := by
  induction t generalizing i j with
  | zero =>
    simp only [stages, Function.iterate_zero_apply, Matrix.ofArray_eq_of_getD,
      Matrix.of_apply, BirdDet.get_eq]
  | succ t ih =>
    rw [stages, step, get_table, Function.iterate_succ_apply']
    simp_rw [BirdDet.stepEntry_eq, BirdDet.Spec.stepEntry_eq, sumFrom_fin_tail, ih]
    simp only [Matrix.ofArray_eq_of_getD, Matrix.of_apply, BirdDet.get_eq]

/-- Compute the determinant from the last stored stage. -/
def determinant (n : ℕ) (A : Array R) : R :=
  match n with
  | 0 => 1
  | k + 1 => (-1 : R) ^ k * BirdDet.get n (stages n A k) 0 0

theorem determinant_eq_birdDet (n : ℕ) (A : Array R) :
    determinant n A = BirdDet.birdDet n A := by
  cases n with
  | zero => rfl
  | succ k =>
    rw [determinant, BirdDet.birdDet_succ]
    exact congrArg ((-1 : R) ^ k * ·)
      (stages_get_eq_iterate A k (0 : Fin (k + 1)) (0 : Fin (k + 1)))

/-- The executable tabulated algorithm computes the mathematical determinant. -/
theorem determinant_eq (A : Array R) (hA : A.size = n * n) :
    determinant n A = Matrix.det (.ofArray A hA) := by
  rw [determinant_eq_birdDet]
  exact (BirdDet.det_eq_birdDet A hA).symm

/-- The first entry of the last mathematical stage determines a nonempty determinant. -/
theorem det_eq_last_stage (M : Matrix (Fin n) (Fin n) R) (hn : 0 < n) :
    M.det = (-1 : R) ^ (n - 1) *
      ((BirdDet.Spec.stepEntry M)^[n - 1] M) ⟨0, hn⟩ ⟨0, hn⟩ := by
  cases n with
  | zero => omega
  | succ k =>
    let A := Array.ofFn fun p : Fin ((k + 1) * (k + 1)) => M p.divNat p.modNat
    have hA : A.size = (k + 1) * (k + 1) := Array.size_ofFn
    have hM : Matrix.ofArray A hA = M := Matrix.ofArray_ofFn M
    have he := determinant_eq A hA
    have hs := stages_get_eq_spec A hA k (0 : Fin (k + 1)) (0 : Fin (k + 1))
    change BirdDet.get (k + 1) (stages (k + 1) A k) 0 0 = _ at hs
    rw [determinant, hs, hM] at he
    exact he.symm

end GameTheory.Math.TabulatedBirdDeterminant
