/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.ZeroSum.MatrixGame.Geometry
import Math.LinearProgramming.StrongComplementarity

/-!
# Strong complementarity for finite matrix games

Finite zero-sum matrix games admit optimal mixed strategies whose supports are
exactly the pure strategies that bind the opponent's value constraints.
-/

noncomputable section

open scoped BigOperators

namespace GameTheory

open Math.Probability

namespace MatrixGame

variable {S : Type} [Fintype S] [Nonempty S]

private theorem shifted_value_pos (A : Square S) :
    0 < value A + (1 + |value A| + ∑ p : S × S, |A p.1 p.2|) := by
  have hsum_nonneg : 0 ≤ ∑ p : S × S, |A p.1 p.2| :=
    Finset.sum_nonneg fun p _ => abs_nonneg (A p.1 p.2)
  have hvalue_nonneg : 0 ≤ value A + |value A| := by
    have h := neg_le_abs (value A)
    linarith
  linarith

open Classical in
/-- Finite zero-sum matrix games have an optimal pair with exact supports:
a row pure strategy is used exactly when its payoff against the column mix is
the value, and a column pure strategy is used exactly when the row mix gives it
the value. -/
theorem exists_strong_complementary_optimal_pair (A : Square S) :
    ∃ row col : PMF S,
      row ∈ optimalRowStrategies A ∧
      col ∈ optimalColumnStrategies A ∧
      (∀ x : S,
        row x ≠ 0 ↔
          columnVectorPayoff A (Math.ProbabilityMassFunction.toVector col) x = value A) ∧
      (∀ y : S,
        col y ≠ 0 ↔
          rowVectorPayoff A (Math.ProbabilityMassFunction.toVector row) y = value A) := by
  classical
  let e : S ≃ Fin (Fintype.card S) := Fintype.equivFin S
  let K : ℝ := 1 + |value A| + ∑ p : S × S, |A p.1 p.2|
  let vshift : ℝ := value A + K
  have hvshift_pos : 0 < vshift := by
    simpa [vshift, K] using shifted_value_pos A
  have hvshift_ne : vshift ≠ 0 := hvshift_pos.ne'
  obtain ⟨row₀, hrow₀⟩ := optimalRowStrategies_nonempty A
  obtain ⟨col₀, hcol₀⟩ := optimalColumnStrategies_nonempty A
  have hrow₀_pure :
      ∀ y : S, value A ≤ rowVectorPayoff A (Math.ProbabilityMassFunction.toVector row₀) y :=
    (rowGuarantees_iff_forall_rowVectorPayoff (A := A) row₀ (value A)).1 hrow₀
  have hcol₀_pure :
      ∀ x : S, columnVectorPayoff A (Math.ProbabilityMassFunction.toVector col₀) x ≤ value A :=
    (columnCaps_iff_forall_columnVectorPayoff (A := A) col₀ (value A)).1 hcol₀
  let M : S → Fin (Fintype.card S) → ℝ := fun y k => A (e.symm k) y + K
  let oneS : S → ℝ := fun _ => 1
  let oneFin : Fin (Fintype.card S) → ℝ := fun _ => 1
  let x₀ : Fin (Fintype.card S) → ℝ :=
    fun k => (row₀ (e.symm k)).toReal / vshift
  let u₀ : S → ℝ := fun y => (col₀ y).toReal / vshift
  have hx₀nn : ∀ k, 0 ≤ x₀ k := by
    intro k
    exact div_nonneg ENNReal.toReal_nonneg hvshift_pos.le
  have hu₀nn : Math.LinearProgramming.Nonnegative u₀ := by
    intro y
    exact div_nonneg ENNReal.toReal_nonneg hvshift_pos.le
  have hsum_x₀ : ∑ k, x₀ k = 1 / vshift := by
    calc
      ∑ k, x₀ k = (∑ k, (row₀ (e.symm k)).toReal) / vshift := by
        simp [x₀, Finset.sum_div]
      _ = (∑ x : S, (row₀ x).toReal) / vshift := by
        rw [e.symm.sum_comp (fun x : S => (row₀ x).toReal)]
      _ = 1 / vshift := by
        rw [Math.Probability.pmf_toReal_sum_one]
  have hsum_u₀ : ∑ y, u₀ y = 1 / vshift := by
    calc
      ∑ y, u₀ y = (∑ y : S, (col₀ y).toReal) / vshift := by
        simp [u₀, Finset.sum_div]
      _ = 1 / vshift := by
        rw [Math.Probability.pmf_toReal_sum_one]
  have hrow_eval_x₀ :
      ∀ y : S,
        (∑ k, M y k * x₀ k) =
          (rowVectorPayoff A (Math.ProbabilityMassFunction.toVector row₀) y + K) / vshift := by
    intro y
    calc
      ∑ k, M y k * x₀ k =
          (∑ k, (A (e.symm k) y + K) * (row₀ (e.symm k)).toReal) / vshift := by
        simp [M, x₀, Finset.sum_div, mul_div_assoc]
      _ = (∑ x : S, (A x y + K) * (row₀ x).toReal) / vshift := by
        rw [e.symm.sum_comp (fun x : S => (A x y + K) * (row₀ x).toReal)]
      _ = (rowVectorPayoff A (Math.ProbabilityMassFunction.toVector row₀) y +
            K * ∑ x : S, (row₀ x).toReal) / vshift := by
        congr 1
        unfold rowVectorPayoff Math.ProbabilityMassFunction.toVector
        calc
          ∑ x : S, (A x y + K) * (row₀ x).toReal
              = ∑ x : S, ((row₀ x).toReal * A x y + K * (row₀ x).toReal) := by
                apply Finset.sum_congr rfl
                intro x _
                ring
          _ = (∑ x : S, (row₀ x).toReal * A x y) +
                ∑ x : S, K * (row₀ x).toReal := by
                rw [Finset.sum_add_distrib]
          _ = (∑ x : S, (row₀ x).toReal * A x y) +
                K * ∑ x : S, (row₀ x).toReal := by
                rw [Finset.mul_sum]
      _ = (rowVectorPayoff A (Math.ProbabilityMassFunction.toVector row₀) y + K) / vshift := by
        rw [Math.Probability.pmf_toReal_sum_one, mul_one]
  have hx₀A : ∀ y, oneS y ≤ ∑ k, M y k * x₀ k := by
    intro y
    rw [hrow_eval_x₀ y]
    change (1 : ℝ) ≤ (rowVectorPayoff A (Math.ProbabilityMassFunction.toVector row₀) y + K) /
      vshift
    rw [le_div_iff₀ hvshift_pos]
    have h := hrow₀_pure y
    dsimp [vshift]
    linarith
  have hx₀_val : ∑ k, oneFin k * x₀ k = 1 / vshift := by
    simpa [oneFin] using hsum_x₀
  have hcol_eval_u₀ :
      ∀ k : Fin (Fintype.card S),
        (∑ y, u₀ y * M y k) =
          (columnVectorPayoff A (Math.ProbabilityMassFunction.toVector col₀) (e.symm k) + K) /
            vshift := by
    intro k
    calc
      ∑ y, u₀ y * M y k =
          (∑ y : S, (col₀ y).toReal * (A (e.symm k) y + K)) / vshift := by
        simp [u₀, M, Finset.sum_div, div_mul_eq_mul_div]
      _ = (columnVectorPayoff A (Math.ProbabilityMassFunction.toVector col₀) (e.symm k) +
            K * ∑ y : S, (col₀ y).toReal) / vshift := by
        congr 1
        unfold columnVectorPayoff Math.ProbabilityMassFunction.toVector
        calc
          ∑ y : S, (col₀ y).toReal * (A (e.symm k) y + K)
              = ∑ y : S, ((col₀ y).toReal * A (e.symm k) y +
                    K * (col₀ y).toReal) := by
                apply Finset.sum_congr rfl
                intro y _
                ring
          _ = (∑ y : S, (col₀ y).toReal * A (e.symm k) y) +
                ∑ y : S, K * (col₀ y).toReal := by
                rw [Finset.sum_add_distrib]
          _ = (∑ y : S, (col₀ y).toReal * A (e.symm k) y) +
                K * ∑ y : S, (col₀ y).toReal := by
                rw [Finset.mul_sum]
      _ = (columnVectorPayoff A (Math.ProbabilityMassFunction.toVector col₀) (e.symm k) + K) /
            vshift := by
        rw [Math.Probability.pmf_toReal_sum_one, mul_one]
  have hu₀ : Math.LinearProgramming.MaxDualFeasible M oneFin u₀ := by
    constructor
    · exact hu₀nn
    · intro k
      change (∑ y, u₀ y * M y k) ≤ oneFin k
      rw [hcol_eval_u₀ k]
      change (columnVectorPayoff A (Math.ProbabilityMassFunction.toVector col₀) (e.symm k) + K) /
        vshift ≤ (1 : ℝ)
      rw [div_le_iff₀ hvshift_pos]
      have h := hcol₀_pure (e.symm k)
      dsimp [vshift]
      linarith
  have hu₀_val : ∑ y, u₀ y * oneS y = 1 / vshift := by
    simpa [oneS] using hsum_u₀
  have hN_pos : (0 : ℝ) < ((Fintype.card S + Fintype.card S : ℕ) : ℝ) := by
    have hcard : 0 < Fintype.card S := Fintype.card_pos_iff.mpr inferInstance
    exact_mod_cast Nat.add_pos_left hcard (Fintype.card S)
  obtain ⟨xstar, ustar, hxstarA, hxstarnn, hustar, hxstar_val, hustar_val,
      hrow_strict, hcol_strict⟩ :=
    Math.LinearProgramming.exists_strong_complementary_pair M oneS oneFin (1 / vshift)
      hN_pos hx₀A hx₀nn hx₀_val hu₀ hu₀_val
  have hstrong :
      Math.LinearProgramming.IsStrongComplementaryPair M oneS oneFin xstar ustar := by
    refine ⟨⟨hxstarnn, hxstarA⟩, hustar, ?_, ?_, ?_⟩
    · simpa [Math.LinearProgramming.minPrimalValue, Math.LinearProgramming.maxDualValue,
        Math.LinearProgramming.dot, oneS, oneFin, mul_comm] using hxstar_val.trans hustar_val.symm
    · intro y
      simpa [Math.LinearProgramming.minPrimalSlack, Math.LinearProgramming.rowEval]
        using hrow_strict y
    · intro k
      simpa [Math.LinearProgramming.maxDualSlack, Math.LinearProgramming.colEval]
        using hcol_strict k
  let rowVec : S → ℝ := fun x => vshift * xstar (e x)
  let colVec : S → ℝ := fun y => vshift * ustar y
  have hsum_xstar : ∑ k, xstar k = 1 / vshift := by
    simpa [oneFin] using hxstar_val
  have hsum_ustar : ∑ y, ustar y = 1 / vshift := by
    simpa [oneS] using hustar_val
  have hrowVec_simplex : rowVec ∈ stdSimplex ℝ S := by
    constructor
    · intro x
      exact mul_nonneg hvshift_pos.le (hxstarnn (e x))
    · calc
        ∑ x : S, rowVec x = vshift * ∑ x : S, xstar (e x) := by
          simp [rowVec, Finset.mul_sum]
        _ = vshift * ∑ k, xstar k := by
          rw [e.sum_comp (fun k : Fin (Fintype.card S) => xstar k)]
        _ = vshift * (1 / vshift) := by rw [hsum_xstar]
        _ = 1 := by field_simp [hvshift_ne]
  have hcolVec_simplex : colVec ∈ stdSimplex ℝ S := by
    constructor
    · intro y
      exact mul_nonneg hvshift_pos.le (hustar.1 y)
    · calc
        ∑ y : S, colVec y = vshift * ∑ y : S, ustar y := by
          simp [colVec, Finset.mul_sum]
        _ = vshift * (1 / vshift) := by rw [hsum_ustar]
        _ = 1 := by field_simp [hvshift_ne]
  let row : PMF S := Math.ProbabilityMassFunction.ofVector rowVec hrowVec_simplex
  let col : PMF S := Math.ProbabilityMassFunction.ofVector colVec hcolVec_simplex
  have hrow_toVector : Math.ProbabilityMassFunction.toVector row = rowVec :=
    Math.ProbabilityMassFunction.toVector_ofVector hrowVec_simplex
  have hcol_toVector : Math.ProbabilityMassFunction.toVector col = colVec :=
    Math.ProbabilityMassFunction.toVector_ofVector hcolVec_simplex
  have hrowVec_payoff :
      ∀ y : S,
        rowVectorPayoff A rowVec y =
          vshift * ((∑ k, M y k * xstar k) - K * (∑ k, xstar k)) := by
    intro y
    calc
      rowVectorPayoff A rowVec y =
          vshift * ∑ x : S, xstar (e x) * A x y := by
        unfold rowVectorPayoff rowVec
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = vshift * ∑ k, xstar k * A (e.symm k) y := by
        congr 1
        simpa using (e.symm.sum_comp (fun x : S => xstar (e x) * A x y)).symm
      _ = vshift * ((∑ k, M y k * xstar k) - K * (∑ k, xstar k)) := by
        congr 1
        calc
          ∑ k, xstar k * A (e.symm k) y =
              ∑ k, (M y k * xstar k - K * xstar k) := by
                apply Finset.sum_congr rfl
                intro k _
                simp [M]
                ring
          _ = (∑ k, M y k * xstar k) - ∑ k, K * xstar k := by
                rw [Finset.sum_sub_distrib]
          _ = (∑ k, M y k * xstar k) - K * (∑ k, xstar k) := by
                rw [Finset.mul_sum]
  have hcolVec_payoff :
      ∀ x : S,
        columnVectorPayoff A colVec x =
          vshift * ((∑ y, ustar y * M y (e x)) - K * (∑ y, ustar y)) := by
    intro x
    calc
      columnVectorPayoff A colVec x =
          vshift * ∑ y : S, ustar y * A x y := by
        unfold columnVectorPayoff colVec
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        ring
      _ = vshift * ((∑ y, ustar y * M y (e x)) - K * (∑ y, ustar y)) := by
        congr 1
        calc
          ∑ y : S, ustar y * A x y =
              ∑ y : S, (ustar y * M y (e x) - K * ustar y) := by
                apply Finset.sum_congr rfl
                intro y _
                simp [M]
                ring
          _ = (∑ y : S, ustar y * M y (e x)) - ∑ y : S, K * ustar y := by
                rw [Finset.sum_sub_distrib]
          _ = (∑ y : S, ustar y * M y (e x)) - K * (∑ y : S, ustar y) := by
                rw [Finset.mul_sum]
  have hrow_payoff_ge :
      ∀ y : S, value A ≤ rowVectorPayoff A rowVec y := by
    intro y
    rw [hrowVec_payoff y, hsum_xstar]
    have h := hxstarA y
    dsimp [oneS] at h
    have hmul : vshift ≤ vshift * (∑ k, M y k * xstar k) := by
      simpa [one_mul] using mul_le_mul_of_nonneg_left h hvshift_pos.le
    calc
      value A = vshift - K := by simp [vshift]
      _ ≤ vshift * (∑ k, M y k * xstar k) - K := by linarith
      _ = vshift * ((∑ k, M y k * xstar k) - K * (1 / vshift)) := by
        field_simp [hvshift_ne]
  have hcol_payoff_le :
      ∀ x : S, columnVectorPayoff A colVec x ≤ value A := by
    intro x
    rw [hcolVec_payoff x, hsum_ustar]
    have h := hustar.2 (e x)
    have h' : (∑ y, ustar y * M y (e x)) ≤ 1 := by
      simpa [Math.LinearProgramming.colEval, oneFin] using h
    have hmul : vshift * (∑ y, ustar y * M y (e x)) ≤ vshift :=
      by simpa [mul_one] using mul_le_mul_of_nonneg_left h' hvshift_pos.le
    calc
      vshift * ((∑ y, ustar y * M y (e x)) - K * (1 / vshift))
          = vshift * (∑ y, ustar y * M y (e x)) - K := by
            field_simp [hvshift_ne]
      _ ≤ vshift - K := by linarith
      _ = value A := by simp [vshift]
  have hrow_opt : row ∈ optimalRowStrategies A := by
    exact (rowGuarantees_iff_forall_rowVectorPayoff (A := A) row (value A)).2 (by
      simpa [hrow_toVector] using hrow_payoff_ge)
  have hcol_opt : col ∈ optimalColumnStrategies A := by
    exact (columnCaps_iff_forall_columnVectorPayoff (A := A) col (value A)).2 (by
      simpa [hcol_toVector] using hcol_payoff_le)
  have hrow_support :
      ∀ x : S,
        row x ≠ 0 ↔
          columnVectorPayoff A (Math.ProbabilityMassFunction.toVector col) x = value A := by
    intro x
    have hiff :=
      Math.LinearProgramming.IsStrongComplementaryPair.primal_pos_iff_maxDualSlack_eq_zero
        (A := M) (b := oneS) (c := oneFin) hstrong (e x)
    rw [Math.ProbabilityMassFunction.ofVector_ne_zero_iff hrowVec_simplex x]
    rw [hcol_toVector]
    constructor
    · intro hpos
      have hxpos : 0 < xstar (e x) := by
        by_contra hnot
        have hxle : xstar (e x) ≤ 0 := le_of_not_gt hnot
        have hmul_nonpos : rowVec x ≤ 0 := by
          dsimp [rowVec]
          exact mul_nonpos_of_nonneg_of_nonpos hvshift_pos.le hxle
        linarith
      have hslack : Math.LinearProgramming.maxDualSlack M oneFin ustar (e x) = 0 :=
        hiff.mp hxpos
      have hpay := hcolVec_payoff x
      dsimp [Math.LinearProgramming.maxDualSlack, Math.LinearProgramming.colEval, oneFin] at hslack
      change (1 : ℝ) - ∑ i, ustar i * M i (e x) = 0 at hslack
      rw [hsum_ustar] at hpay
      calc
        columnVectorPayoff A colVec x =
            vshift * ((∑ y, ustar y * M y (e x)) - K * (1 / vshift)) := by
              exact hpay
        _ = vshift - K := by
              have hsum : (∑ y, ustar y * M y (e x)) = 1 := by linarith
              rw [hsum]
              field_simp [hvshift_ne]
        _ = value A := by simp [vshift]
    · intro hpay
      have hslack : Math.LinearProgramming.maxDualSlack M oneFin ustar (e x) = 0 := by
        dsimp [Math.LinearProgramming.maxDualSlack, Math.LinearProgramming.colEval, oneFin]
        have hpay' := hcolVec_payoff x
        rw [hsum_ustar] at hpay'
        have hsum : (∑ y, ustar y * M y (e x)) = 1 := by
          have hcalc : value A =
              vshift * ((∑ y, ustar y * M y (e x)) - K * (1 / vshift)) := by
            rw [← hpay]
            simpa [hcol_toVector] using hpay'
          have hcalc' : value A = vshift * (∑ y, ustar y * M y (e x)) - K := by
            calc
              value A = vshift * ((∑ y, ustar y * M y (e x)) - K * (1 / vshift)) := hcalc
              _ = vshift * (∑ y, ustar y * M y (e x)) - K := by
                field_simp [hvshift_ne]
          have hvdef : value A = vshift - K := by simp [vshift]
          nlinarith [hcalc', hvdef, hvshift_pos]
        linarith
      have hxpos : 0 < xstar (e x) := hiff.mpr hslack
      exact mul_pos hvshift_pos hxpos
  have hcol_support :
      ∀ y : S,
        col y ≠ 0 ↔
          rowVectorPayoff A (Math.ProbabilityMassFunction.toVector row) y = value A := by
    intro y
    have hiff :=
      Math.LinearProgramming.IsStrongComplementaryPair.dual_pos_iff_minPrimalSlack_eq_zero
        (A := M) (b := oneS) (c := oneFin) hstrong y
    rw [Math.ProbabilityMassFunction.ofVector_ne_zero_iff hcolVec_simplex y]
    rw [hrow_toVector]
    constructor
    · intro hpos
      have hypos : 0 < ustar y := by
        by_contra hnot
        have hyle : ustar y ≤ 0 := le_of_not_gt hnot
        have hmul_nonpos : colVec y ≤ 0 := by
          dsimp [colVec]
          exact mul_nonpos_of_nonneg_of_nonpos hvshift_pos.le hyle
        linarith
      have hslack : Math.LinearProgramming.minPrimalSlack M oneS xstar y = 0 :=
        hiff.mp hypos
      have hpay := hrowVec_payoff y
      dsimp [Math.LinearProgramming.minPrimalSlack, Math.LinearProgramming.rowEval, oneS] at hslack
      change (∑ j, M y j * xstar j) - (1 : ℝ) = 0 at hslack
      rw [hsum_xstar] at hpay
      calc
        rowVectorPayoff A rowVec y =
            vshift * ((∑ k, M y k * xstar k) - K * (1 / vshift)) := by
              exact hpay
        _ = vshift - K := by
              have hsum : (∑ k, M y k * xstar k) = 1 := by linarith
              rw [hsum]
              field_simp [hvshift_ne]
        _ = value A := by simp [vshift]
    · intro hpay
      have hslack : Math.LinearProgramming.minPrimalSlack M oneS xstar y = 0 := by
        dsimp [Math.LinearProgramming.minPrimalSlack, Math.LinearProgramming.rowEval, oneS]
        have hpay' := hrowVec_payoff y
        rw [hsum_xstar] at hpay'
        have hsum : (∑ k, M y k * xstar k) = 1 := by
          have hcalc : value A =
              vshift * ((∑ k, M y k * xstar k) - K * (1 / vshift)) := by
            rw [← hpay]
            simpa [hrow_toVector] using hpay'
          have hcalc' : value A = vshift * (∑ k, M y k * xstar k) - K := by
            calc
              value A = vshift * ((∑ k, M y k * xstar k) - K * (1 / vshift)) := hcalc
              _ = vshift * (∑ k, M y k * xstar k) - K := by
                field_simp [hvshift_ne]
          have hvdef : value A = vshift - K := by simp [vshift]
          nlinarith [hcalc', hvdef, hvshift_pos]
        linarith
      have hypos : 0 < ustar y := hiff.mpr hslack
      exact mul_pos hvshift_pos hypos
  exact ⟨row, col, hrow_opt, hcol_opt, hrow_support, hcol_support⟩

end MatrixGame
end GameTheory
