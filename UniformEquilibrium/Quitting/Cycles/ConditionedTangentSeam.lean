/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.PhantomBoundaryConditioning
import UniformEquilibrium.Quitting.Cycles.PeriodOneTangentAtlas

/-!
# The conditioned charge-tangent seam

A one-stage charge tangent compares the current absorbing delivery with the
unconditioned far annotation.  Conditioning a positive-survival tail on
eventual absorption instead compares that delivery with the honest
conditioned far value.  These are not the same comparison.

This module gives the exact correction term.  A negative unconditioned
tangent has only two possible sources: a negative conditioned delivery gap,
or a strictly lower conditioned value financed by the phantom boundary.  On
a boundary coordinate which the conditioned tail cannot cross from above,
the second source is impossible and the negative tangent becomes a genuine
upward transition of the conditioned chronology.

The statements are accounting and sign-transfer results.  They do not assert
that a conditioned coalition law is an ordinary product root or turn an
upward conditioned transition into a unilateral deviation.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

omit [DecidableEq ι] in
/-- Recover the original annotation from its phantom boundary and its value
conditioned on eventual absorption. -/
theorem quittingValue_eq_boundary_add_eventualAbsorption_mul_conditionedGap
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι) (time : ℕ) (who : ι)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    value time who = boundary who +
      quittingTailEventualAbsorption roots time *
        (quittingTailConditionedValue roots value boundary time who -
          boundary who) := by
  unfold quittingTailConditionedValue
  field_simp [hpositive.ne']
  unfold quittingTailEventualAbsorption
  ring

omit [DecidableEq ι] in
/-- Repeating one positive-absorption root delivers exactly its one-stage
absorbing payoff conditioned on absorption at that root. -/
theorem quittingWindowRestartDelivery_periodOne_one_eq_conditionalAbsorbingDelivery
    (root : ι → PMF Bool) (who : ι) :
    quittingWindowRestartDelivery reward
        (quittingPeriodOneRootSequence root) who 0 1 =
      quittingRootConditionalAbsorbingDelivery reward root who := by
  unfold quittingWindowRestartDelivery quittingWindowAbsorbingIntercept
    quittingRootConditionalAbsorbingDelivery
  simp [quittingRootAbsorptionMass]

omit [DecidableEq ι] in
/-- **Exact conditioned tangent correction.**  The usual one-stage tangent
is the honest conditioned delivery gap plus the surviving phantom share of
the conditioned boundary gap. -/
theorem conditionalAbsorbingDelivery_sub_value_eq_conditionedGap_add_phantomGap
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι) (time : ℕ) (who : ι)
    (hnext : 0 < quittingTailEventualAbsorption roots (time + 1)) :
    quittingRootConditionalAbsorbingDelivery reward (roots time) who -
        value (time + 1) who =
      (quittingRootConditionalAbsorbingDelivery reward (roots time) who -
          quittingTailConditionedValue roots value boundary (time + 1) who) +
        quittingJointSurvivalLimit roots (time + 1) *
          (quittingTailConditionedValue roots value boundary (time + 1) who -
            boundary who) := by
  rw [quittingValue_eq_boundary_add_eventualAbsorption_mul_conditionedGap
    roots value boundary (time + 1) who hnext]
  unfold quittingTailEventualAbsorption
  ring

omit [DecidableEq ι] in
/-- If the conditioned far value is no smaller than the phantom boundary, a
negative ordinary tangent remains negative after conditioning. -/
theorem conditionalAbsorbingDelivery_lt_conditionedValue_of_tangent_neg
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι) (time : ℕ) (who : ι)
    (hnext : 0 < quittingTailEventualAbsorption roots (time + 1))
    (hboundary : boundary who ≤
      quittingTailConditionedValue roots value boundary (time + 1) who)
    (htangent :
      quittingRootConditionalAbsorbingDelivery reward (roots time) who -
        value (time + 1) who < 0) :
    quittingRootConditionalAbsorbingDelivery reward (roots time) who <
      quittingTailConditionedValue roots value boundary (time + 1) who := by
  have hsurvival : 0 ≤ quittingJointSurvivalLimit roots (time + 1) :=
    quittingJointSurvivalLimit_nonneg roots (time + 1)
  have hcorrection : 0 ≤ quittingJointSurvivalLimit roots (time + 1) *
      (quittingTailConditionedValue roots value boundary (time + 1) who -
        boundary who) := mul_nonneg hsurvival (sub_nonneg.mpr hboundary)
  have hidentity :=
    conditionalAbsorbingDelivery_sub_value_eq_conditionedGap_add_phantomGap
      (reward := reward) roots value boundary time who hnext
  linarith

omit [DecidableEq ι] in
/-- **Negative-tangent funding alternative.**  If a negative ordinary
tangent does not remain negative after conditioning, its full magnitude is
funded by positive phantom survival times a strict boundary-over-conditioned
gap. -/
theorem conditionedGap_neg_or_strictPhantomFunding_of_tangent_neg
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι) (time : ℕ) (who : ι)
    (hnext : 0 < quittingTailEventualAbsorption roots (time + 1))
    (htangent :
      quittingRootConditionalAbsorbingDelivery reward (roots time) who -
        value (time + 1) who < 0) :
    (quittingRootConditionalAbsorbingDelivery reward (roots time) who -
        quittingTailConditionedValue roots value boundary (time + 1) who < 0) ∨
      (0 < quittingJointSurvivalLimit roots (time + 1) ∧
        quittingTailConditionedValue roots value boundary (time + 1) who <
          boundary who ∧
        -(quittingRootConditionalAbsorbingDelivery reward (roots time) who -
            value (time + 1) who) ≤
          quittingJointSurvivalLimit roots (time + 1) *
            (boundary who -
              quittingTailConditionedValue roots value boundary
                (time + 1) who)) := by
  by_cases hgap :
      quittingRootConditionalAbsorbingDelivery reward (roots time) who -
        quittingTailConditionedValue roots value boundary (time + 1) who < 0
  · exact Or.inl hgap
  · right
    have hgapNonneg := le_of_not_gt hgap
    have hidentity :=
      conditionalAbsorbingDelivery_sub_value_eq_conditionedGap_add_phantomGap
        (reward := reward) roots value boundary time who hnext
    have hfunding : 0 < quittingJointSurvivalLimit roots (time + 1) *
        (boundary who -
          quittingTailConditionedValue roots value boundary (time + 1) who) := by
      nlinarith
    rcases (mul_pos_iff.mp hfunding) with hpositive | hnegative
    · refine ⟨hpositive.1, sub_pos.mp hpositive.2, ?_⟩
      nlinarith
    · exact (not_lt_of_ge
        (quittingJointSurvivalLimit_nonneg roots (time + 1)) hnegative.1).elim

omit [DecidableEq ι] in
/-- On a boundary-safe coordinate, a negative one-stage tangent produces a
strict upward move of the exact conditioned chronology. -/
theorem quittingTailConditionedValue_lt_succ_of_tangent_neg
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (time : ℕ) (who : ι)
    (habsorption : 0 < quittingRootAbsorptionMass (roots time))
    (hcurrent : 0 < quittingTailEventualAbsorption roots time)
    (hnext : 0 < quittingTailEventualAbsorption roots (time + 1))
    (hboundary : boundary who ≤
      quittingTailConditionedValue roots value boundary (time + 1) who)
    (htangent :
      quittingRootConditionalAbsorbingDelivery reward (roots time) who -
        value (time + 1) who < 0) :
    quittingTailConditionedValue roots value boundary time who <
      quittingTailConditionedValue roots value boundary (time + 1) who := by
  have hgap := conditionalAbsorbingDelivery_lt_conditionedValue_of_tangent_neg
    (reward := reward) roots value boundary time who hnext hboundary htangent
  have hweight : 0 < quittingTailConditionedAbsorptionWeight roots time :=
    div_pos habsorption hcurrent
  have hstep := congrFun
    (quittingTailConditionedValue_sub_succ roots value boundary hpolicy time
      habsorption hcurrent hnext) who
  change quittingTailConditionedValue roots value boundary time who -
      quittingTailConditionedValue roots value boundary (time + 1) who =
    quittingTailConditionedAbsorptionWeight roots time *
      (quittingRootConditionalAbsorbingDelivery reward (roots time) who -
        quittingTailConditionedValue roots value boundary (time + 1) who) at hstep
  have hproduct : quittingTailConditionedAbsorptionWeight roots time *
      (quittingRootConditionalAbsorbingDelivery reward (roots time) who -
        quittingTailConditionedValue roots value boundary (time + 1) who) < 0 :=
    mul_neg_of_pos_of_neg hweight (sub_neg.mpr hgap)
  linarith

end GameTheory
