import GameTheory.Math.IntegerDeterminantBound
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Int.NatAbs

/-! Nonnegative solutions of integer linear systems have bounded rational witnesses.

Finite support elimination gives an independent family of columns. Its Gram matrix
then provides a common denominator, with a coarse bound from the determinant expansion.
-/

noncomputable section

namespace GameTheory.Math

open scoped BigOperators
open Matrix

/-- A nonnegative finite linear combination can be represented by independent vectors,
without adding vectors to its support. -/
theorem exists_nonnegative_independent_representation {ι V : Type*}
    [AddCommGroup V] [Module ℝ V] (v : ι → V) (s : Finset ι)
    (x : ι → ℝ) (hx : ∀ i ∈ s, 0 ≤ x i) :
    ∃ (t : Finset ι) (y : ι → ℝ), t ⊆ s ∧ (∀ i ∈ t, 0 ≤ y i) ∧
      LinearIndepOn ℝ v (t : Set ι) ∧
      ∑ i ∈ t, y i • v i = ∑ i ∈ s, x i • v i := by
  classical
  induction s using Finset.strongInductionOn generalizing x
  rename_i s ih
  by_cases hind : LinearIndepOn ℝ v (s : Set ι)
  · exact ⟨s, x, Finset.Subset.refl _, hx, hind, rfl⟩
  obtain ⟨g, hgzero, j, hjs, hgj⟩ := not_linearIndepOn_finset_iff.mp hind
  have hrel : ∃ g : ι → ℝ, (∑ i ∈ s, g i • v i = 0) ∧ ∃ j ∈ s, 0 < g j := by
    rcases lt_or_gt_of_ne hgj with hneg | hpos
    · refine ⟨fun i => -g i, ?_, j, hjs, neg_pos.mpr hneg⟩
      simp only [neg_smul, Finset.sum_neg_distrib, hgzero, neg_zero]
    · exact ⟨g, hgzero, j, hjs, hpos⟩
  obtain ⟨g, hgzero, j, hjs, hgj⟩ := hrel
  let pos := s.filter (fun i => 0 < g i)
  obtain ⟨k, hkpos, hmin⟩ := pos.exists_min_image (fun i => x i / g i)
    ⟨j, Finset.mem_filter.mpr ⟨hjs, hgj⟩⟩
  have hks : k ∈ s := (Finset.mem_filter.mp hkpos).1
  have hgk : 0 < g k := (Finset.mem_filter.mp hkpos).2
  let y : ι → ℝ := fun i => x i - x k / g k * g i
  have hyk : y k = 0 := by simp [y, ne_of_gt hgk]
  have hy : ∀ i ∈ s.erase k, 0 ≤ y i := by
    intro i hi
    have his : i ∈ s := (Finset.mem_erase.mp hi).2
    change 0 ≤ x i - x k / g k * g i
    apply sub_nonneg.mpr
    by_cases hgi : 0 < g i
    · exact (le_div_iff₀ hgi).mp (hmin i (Finset.mem_filter.mpr ⟨his, hgi⟩))
    · exact le_trans (mul_nonpos_of_nonneg_of_nonpos
        (div_nonneg (hx k hks) hgk.le) (le_of_not_gt hgi)) (hx i his)
  have hsum : ∑ i ∈ s.erase k, y i • v i = ∑ i ∈ s, x i • v i := by
    calc
      ∑ i ∈ s.erase k, y i • v i = ∑ i ∈ s, y i • v i :=
        Finset.sum_erase _ (by rw [hyk, zero_smul])
      _ = ∑ i ∈ s, x i • v i := by
        simp only [y, sub_smul, mul_smul, Finset.sum_sub_distrib,
          ← Finset.smul_sum, hgzero, smul_zero, sub_zero]
  obtain ⟨t, z, hts, hz, htind, htz⟩ :=
    ih (s.erase k) (Finset.erase_ssubset hks) y hy
  exact ⟨t, z, hts.trans (Finset.erase_subset _ _), hz, htind, htz.trans hsum⟩

private theorem gram_det_ne_zero {ρ κ : Type*} [Fintype ρ] [Fintype κ]
    [DecidableEq κ] (C : Matrix ρ κ ℝ) (hC : LinearIndependent ℝ C.col) :
    (Cᵀ * C).det ≠ 0 := by
  apply Matrix.nonsingular_iff_det_ne_zero.mp
  apply Matrix.Nonsingular.of_linearIndependent_col
  apply Matrix.mulVec_injective_iff.mp
  have hker : LinearMap.ker C.mulVecLin = ⊥ :=
    LinearMap.ker_eq_bot.mpr (Matrix.mulVec_injective_iff.mpr hC)
  exact LinearMap.ker_eq_bot.mp ((Matrix.ker_mulVecLin_transpose_mul_self C).trans hker)

private theorem exists_small_independent_solution {ρ κ : Type*}
    [Fintype ρ] [Fintype κ] [DecidableEq κ]
    (C : Matrix ρ κ ℤ) (b : ρ → ℤ) (H : ℕ)
    (hC : ∀ i j, (C i j).natAbs ≤ H) (hb : ∀ i, (b i).natAbs ≤ H)
    (y : κ → ℝ) (hy : ∀ j, 0 ≤ y j)
    (hsol : (C.map (fun z : ℤ => (z : ℝ))) *ᵥ y = fun i => (b i : ℝ))
    (hind : LinearIndependent ℝ (C.map (fun z : ℤ => (z : ℝ))).col) :
    ∃ (D : ℕ) (N : κ → ℕ), 0 < D ∧
      D ≤ (Fintype.card κ).factorial * ((Fintype.card ρ + 1) * (H + 1)^2)^Fintype.card κ ∧
      (∀ j, N j ≤ (Fintype.card κ).factorial *
        ((Fintype.card ρ + 1) * (H + 1)^2)^Fintype.card κ) ∧
      (∀ i, ∑ j, C i j * (N j : ℤ) = (D : ℤ) * b i) := by
  classical
  let G : Matrix κ κ ℤ := Cᵀ * C
  let c : κ → ℤ := Cᵀ *ᵥ b
  let R : Matrix ρ κ ℝ := C.map (fun z : ℤ => (z : ℝ))
  let K := (Fintype.card ρ + 1) * (H + 1)^2
  have hcastG : G.map (fun z : ℤ => (z : ℝ)) = Rᵀ * R := by
    ext j k
    simp [G, R, Matrix.mul_apply]
  have hcastc : (fun j => (c j : ℝ)) = Rᵀ *ᵥ (fun i => (b i : ℝ)) := by
    ext j
    simp [c, R, Matrix.mulVec, dotProduct]
  have hGram : (G.map (fun z : ℤ => (z : ℝ))) *ᵥ y = fun j => (c j : ℝ) := by
    rw [hcastG, hcastc, ← Matrix.mulVec_mulVec, hsol]
  have hdetR : (G.map (fun z : ℤ => (z : ℝ))).det ≠ 0 := by
    rw [hcastG]
    exact gram_det_ne_zero R hind
  have hdet : G.det ≠ 0 := by
    intro hzero
    apply hdetR
    rw [← Int.cast_det, hzero, Int.cast_zero]
  have hcramer (j : κ) : ((G.updateCol j c).det : ℝ) = y j * (G.det : ℝ) := by
    rw [Int.cast_det, Matrix.map_updateCol]
    have hc : (fun k => (c k : ℝ)) =
        fun k => ∑ i, y i • (G.map (fun z : ℤ => (z : ℝ))) k i := by
      ext k
      simpa only [Matrix.mulVec, dotProduct, smul_eq_mul, mul_comm] using (congrFun hGram k).symm
    change ((G.map (fun z : ℤ => (z : ℝ))).updateCol j (fun k => (c k : ℝ))).det = _
    rw [hc, Matrix.det_updateCol_sum, smul_eq_mul, ← Int.cast_det]
  have hdotBound (f g : ρ → ℤ) (hf : ∀ i, (f i).natAbs ≤ H)
      (hg : ∀ i, (g i).natAbs ≤ H) :
      (∑ i, f i * g i).natAbs ≤ K := by
    calc
      (∑ i, f i * g i).natAbs ≤ ∑ i, (f i * g i).natAbs := Int.natAbs_sum_le _ _
      _ ≤ ∑ _i : ρ, H * H := by
        apply Finset.sum_le_sum
        intro i _
        rw [Int.natAbs_mul]
        exact Nat.mul_le_mul (hf i) (hg i)
      _ ≤ K := by
        simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
        dsimp [K]
        nlinarith
  have hG : ∀ j k, (G j k).natAbs ≤ K := by
    intro j k
    exact hdotBound (fun i => C i j) (fun i => C i k) (fun i => hC i j) (fun i => hC i k)
  have hc : ∀ j, (c j).natAbs ≤ K := by
    intro j
    exact hdotBound (fun i => C i j) b (fun i => hC i j) hb
  let Z : κ → ℤ := fun j => Int.sign G.det * (G.updateCol j c).det
  let D := G.det.natAbs
  have hD : 0 < D := Int.natAbs_pos.mpr hdet
  have hZeq (j : κ) : (Z j : ℝ) = y j * (D : ℝ) := by
    dsimp [Z, D]
    rw [Int.cast_mul, hcramer]
    have hs : ((Int.sign G.det : ℤ) : ℝ) * (G.det : ℝ) = (G.det.natAbs : ℝ) := by
      have heq := congrArg (fun z : ℤ => (z : ℝ)) (Int.sign_mul_self_eq_natAbs G.det)
      simpa only [Int.cast_mul, Int.cast_natCast] using heq
    calc
      _ = y j * ((Int.sign G.det : ℝ) * (G.det : ℝ)) := by ring
      _ = _ := by rw [hs]
  have hZnonneg (j : κ) : 0 ≤ Z j := by
    have hz : (0 : ℝ) ≤ (Z j : ℝ) := by
      rw [hZeq]
      exact mul_nonneg (hy j) (Nat.cast_nonneg _)
    exact_mod_cast hz
  have hZbound (j : κ) : (Z j).natAbs ≤ (Fintype.card κ).factorial * K^Fintype.card κ := by
    dsimp only [Z]
    rw [Int.natAbs_mul, Int.natAbs_sign_of_ne_zero hdet, one_mul]
    apply natAbs_det_le
    intro k l
    rw [Matrix.updateCol_apply]
    split_ifs
    · exact hc k
    · exact hG k l
  refine ⟨D, fun j => (Z j).toNat, hD, natAbs_det_le G K hG, ?_, ?_⟩
  · intro j
    apply Int.toNat_le.mpr
    have hz : ((Z j).natAbs : ℤ) ≤
        ((Fintype.card κ).factorial * K^Fintype.card κ : ℕ) := by exact_mod_cast hZbound j
    rwa [Int.natAbs_of_nonneg (hZnonneg j)] at hz
  · intro i
    have heq : (∑ j, C i j * Z j : ℤ) = (D : ℤ) * b i := by
      apply Int.cast_injective (α := ℝ)
      push_cast
      simp_rw [hZeq]
      rw [show (∑ j, (C i j : ℝ) * (y j * (D : ℝ))) =
          (D : ℝ) * ∑ j, (C i j : ℝ) * y j by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring]
      congr 1
      exact congrFun hsol i
    simpa only [Int.toNat_of_nonneg (hZnonneg _)] using heq

/-- A nonnegative real solution of a bounded integer linear system has nonnegative
integer numerators with one positive, bounded common denominator. -/
theorem exists_small_nonnegative_solution {ρ κ : Type*}
    [Fintype ρ] [Fintype κ] [DecidableEq κ]
    (M : Matrix ρ κ ℤ) (b : ρ → ℤ) (H : ℕ)
    (hM : ∀ i j, (M i j).natAbs ≤ H) (hb : ∀ i, (b i).natAbs ≤ H)
    (x : κ → ℝ) (hx : ∀ j, 0 ≤ x j)
    (heq : ∀ i, ∑ j, (M i j : ℝ) * x j = (b i : ℝ)) :
    ∃ (D : ℕ) (N : κ → ℕ), 0 < D ∧
      D ≤ (Fintype.card κ).factorial * ((Fintype.card ρ + 1) * (H + 1)^2)^Fintype.card κ ∧
      (∀ j, N j ≤ (Fintype.card κ).factorial *
        ((Fintype.card ρ + 1) * (H + 1)^2)^Fintype.card κ) ∧
      (∀ i, ∑ j, M i j * (N j : ℤ) = (D : ℤ) * b i) := by
  classical
  let v : κ → ρ → ℝ := fun j i => (M i j : ℝ)
  obtain ⟨s, y, _, hy, hind, hrep⟩ :=
    exists_nonnegative_independent_representation v Finset.univ x (fun j _ => hx j)
  let C : Matrix ρ s ℤ := fun i j => M i j
  have hsol : (C.map (fun z : ℤ => (z : ℝ))) *ᵥ (fun j : s => y j) =
      fun i => (b i : ℝ) := by
    ext i
    change (∑ j : s, (M i j : ℝ) * y j) = _
    have hi := congrFun hrep i
    calc
      (∑ j : s, (M i j : ℝ) * y j) = ∑ j ∈ s, (M i j : ℝ) * y j :=
        Finset.sum_coe_sort s (fun j => (M i j : ℝ) * y j)
      _ = (b i : ℝ) := by
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, v] at hi
        simpa only [mul_comm] using hi.trans (by simpa only [mul_comm] using heq i)
  have hCind : LinearIndependent ℝ (C.map (fun z : ℤ => (z : ℝ))).col := hind
  obtain ⟨D, Ns, hD, hDbound, hNbound, hEq⟩ :=
    exists_small_independent_solution C b H (fun i j => hM i j) hb
      (fun j : s => y j) (fun j => hy j j.property) hsol hCind
  let K := (Fintype.card ρ + 1) * (H + 1)^2
  have hK : 1 ≤ K := by
    have hpos : 0 < K := by dsimp [K]; positivity
    exact hpos
  have hcard : Fintype.card s ≤ Fintype.card κ := Fintype.card_subtype_le _
  have hbound : (Fintype.card s).factorial * K^Fintype.card s ≤
      (Fintype.card κ).factorial * K^Fintype.card κ :=
    Nat.mul_le_mul (Nat.factorial_le hcard) (pow_le_pow_right' hK hcard)
  let N : κ → ℕ := fun j => if hj : j ∈ s then Ns ⟨j, hj⟩ else 0
  refine ⟨D, N, hD, hDbound.trans hbound, ?_, ?_⟩
  · intro j
    dsimp [N]
    split_ifs with hj
    · exact (hNbound ⟨j, hj⟩).trans hbound
    · exact Nat.zero_le _
  · intro i
    calc
      ∑ j, M i j * (N j : ℤ) = ∑ j ∈ s, M i j * (N j : ℤ) := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro j _ hj
        simp [N, hj]
      _ = ∑ j : s, C i j * (Ns j : ℤ) := by
        rw [← Finset.sum_coe_sort]
        apply Finset.sum_congr rfl
        intro j _
        simp [N, C, j.property]
      _ = (D : ℤ) * b i := hEq i

end GameTheory.Math
