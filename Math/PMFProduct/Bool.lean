/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.PMFProduct.Update

/-!
# Boolean product PMFs

Small closed-form facts for Boolean marginals and two-coordinate Boolean
product distributions.
-/

namespace Math.PMFProduct

open Math.Probability Math.ProbabilityMassFunction

/-- The mass of `false` in a Boolean PMF is one minus the mass of `true`. -/
lemma pmfBool_false_toReal (mu : PMF Bool) :
    (mu false).toReal = 1 - (mu true).toReal := by
  have h := expect_const mu (1 : ℝ)
  rw [expect_eq_sum, Fintype.sum_bool] at h
  norm_num at h ⊢
  linarith

/-- Fubini expansion of a product of two Boolean PMFs. -/
lemma expect_pmfPi_bool (m : Bool → PMF Bool)
    (f : (Bool → Bool) → ℝ) :
    expect (pmfPi m) f =
      expect (m false) (fun a ↦
        expect (m true) (fun b ↦ f (fun coordinate ↦
          if coordinate then b else a))) := by
  classical
  have hfalse : Function.update m false (m false) = m :=
    Function.update_eq_self false m
  rw [← hfalse, pmfPi_update_bind, expect_bind]
  apply congrArg (expect (m false))
  funext a
  have htrue : Function.update (Function.update m false (PMF.pure a))
      true (m true) = Function.update m false (PMF.pure a) := by
    funext coordinate
    cases coordinate <;> simp
  rw [← htrue, pmfPi_update_bind, expect_bind]
  apply congrArg (expect (m true))
  funext b
  have hpure : Function.update (Function.update m false (PMF.pure a))
        true (PMF.pure b) =
      fun coordinate ↦ PMF.pure (if coordinate then b else a) := by
    funext coordinate
    cases coordinate <;> simp
  rw [hpure, pmfPi_pure, expect_pure]

end Math.PMFProduct
