/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Weighted finite collision concentration

This file contains the game-independent algebra which propagates a one-row
quadratic collision estimate through a finite survival-weighted window.

It deliberately does not prove a product-law pair-union bound.  In a quitting
game that separate probabilistic input has the expected shape

`collision phase ≤ Nat.choose playerCount 2 * absorption phase ^ 2`.

The theorems below consume such a bound and handle every denominator case
explicitly.  In particular, a zero-absorption window has zero collision mass
and no conditional quotient is formed.
-/

namespace Math.Probability

/-- A survival-weighted finite window either has zero absorption and zero
collision, or its conditional collision mass is bounded by `C * rho`.

The assumptions are pointwise: collision is at most `C * absorption²`, and
absorption is at most the common ceiling `rho`. -/
theorem finiteWeightedCollisionConcentration_or_zero
    {κ : Type} [Fintype κ]
    (weight absorption collision : κ → ℝ) (C rho : ℝ)
    (hweight : ∀ phase, 0 ≤ weight phase)
    (habsorption : ∀ phase, 0 ≤ absorption phase)
    (hcollision : ∀ phase, 0 ≤ collision phase)
    (hC : 0 ≤ C)
    (hcap : ∀ phase, absorption phase ≤ rho)
    (hstage : ∀ phase,
      collision phase ≤ C * absorption phase ^ 2) :
    ((∑ phase, weight phase * absorption phase) = 0 ∧
        (∑ phase, weight phase * collision phase) = 0) ∨
      (0 < ∑ phase, weight phase * absorption phase ∧
        (∑ phase, weight phase * collision phase) /
            (∑ phase, weight phase * absorption phase) ≤ C * rho) := by
  let absorbed := ∑ phase, weight phase * absorption phase
  let collided := ∑ phase, weight phase * collision phase
  have habsorbed : 0 ≤ absorbed :=
    Finset.sum_nonneg fun phase _ ↦
      mul_nonneg (hweight phase) (habsorption phase)
  have hcollided : 0 ≤ collided :=
    Finset.sum_nonneg fun phase _ ↦
      mul_nonneg (hweight phase) (hcollision phase)
  have hpoint : ∀ phase,
      weight phase * collision phase ≤
        C * rho * (weight phase * absorption phase) := by
    intro phase
    have hsquare : absorption phase ^ 2 ≤
        rho * absorption phase := by
      nlinarith [habsorption phase, hcap phase]
    have hstage' : collision phase ≤ C * rho * absorption phase :=
      (hstage phase).trans (by
        nlinarith [mul_le_mul_of_nonneg_left hsquare hC])
    nlinarith [mul_le_mul_of_nonneg_left hstage' (hweight phase)]
  have hwindow : collided ≤ C * rho * absorbed := by
    dsimp only [collided, absorbed]
    calc
      (∑ phase, weight phase * collision phase) ≤
          ∑ phase, C * rho *
            (weight phase * absorption phase) :=
        Finset.sum_le_sum fun phase _ ↦ hpoint phase
      _ = C * rho *
          ∑ phase, weight phase * absorption phase := by
        rw [Finset.mul_sum]
  rcases habsorbed.eq_or_lt with hzero | hpositive
  · left
    change absorbed = 0 ∧ collided = 0
    refine ⟨hzero.symm, ?_⟩
    apply le_antisymm
    · rw [← hzero, mul_zero] at hwindow
      exact hwindow
    · exact hcollided
  · right
    refine ⟨hpositive, (div_le_iff₀ hpositive).2 ?_⟩
    simpa [mul_assoc, mul_left_comm, mul_comm] using hwindow

/-- Conditional payoff differs from the normalized singleton mixture by at
most twice the reward bound times the conditional collision mass.

Here `S` is singleton mass, `C` collision mass, `A = S + C`, `X` is the
singleton reward contribution, and `b` is the collision reward contribution.
Both `A > 0` and `S > 0` are explicit because the two conditional objects have
different denominators. -/
theorem abs_conditionalPayoff_sub_singletonMixture_le
    {A S C X b actual mixture M : ℝ}
    (hA : A = S + C) (hApos : 0 < A) (hSpos : 0 < S)
    (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hX : |X| ≤ M * S) (hb : |b| ≤ M * C)
    (hactual : actual = (X + b) / A)
    (hmixture : mixture = X / S) :
    |actual - mixture| ≤ 2 * M * C / A := by
  have hAS : 0 < A * S := mul_pos hApos hSpos
  have hMC : 0 ≤ M * C := mul_nonneg hM hC
  have hexact : actual - mixture = (b * S - X * C) / (A * S) := by
    rw [hactual, hmixture, hA]
    field_simp [hSpos.ne', (show S + C ≠ 0 by linarith)]
    ring
  have hnum : |b * S - X * C| ≤ 2 * M * C * S := by
    calc
      |b * S - X * C| ≤ |b * S| + |X * C| := abs_sub _ _
      _ = |b| * S + |X| * C := by
        rw [abs_mul, abs_mul, abs_of_pos hSpos, abs_of_nonneg hC]
      _ ≤ (M * C) * S + (M * S) * C := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right hb hSpos.le)
          (mul_le_mul_of_nonneg_right hX hC)
      _ = 2 * M * C * S := by ring
  rw [hexact, abs_div, abs_of_pos hAS]
  apply (div_le_iff₀ hAS).2
  have hscaled := mul_le_mul_of_nonneg_right hnum hApos.le
  field_simp [hApos.ne', hSpos.ne']
  nlinarith [hMC]

end Math.Probability
