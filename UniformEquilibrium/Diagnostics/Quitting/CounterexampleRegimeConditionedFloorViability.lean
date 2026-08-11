/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeBallisticity
import UniformEquilibrium.Quitting.Cycles.ConditionedDiffuseChronology

/-!
# Punishment-floor viability after removing the phantom boundary

Conditioning an exact quitting tail on eventual absorption preserves its
chronology, but need not preserve every player's punishment floor.  This
module identifies the exact obstruction for the canonical tail of a
hypothetical counterexample.

Write `v` for the displayed value, `b` for the phantom boundary, `L` for
Never mass, `a = 1 - L` for eventual-absorption mass, and `y` for the value
conditioned on eventual absorption.  Then

`a * (p - y) = L * (b - p) - (v - p)`.

Since the canonical displayed tail satisfies `v >= p`, its conditioned floor
deficit is funded entirely by strict slack of the phantom boundary above the
punishment value.  In particular every coordinate on the tight plateau face
`b = p` remains punishment-rational after conditioning, at every date where
conditioning is defined.  Conversely, any conditioned floor violation forces
`p < b` in that coordinate and obeys the displayed quantitative budget.

This is a sharp viability theorem, not a strategic realization theorem.  The
counterexample machinery does not force the tight plateau face to be nonempty,
and when `a` tends to zero a fixed strict plateau slack can conceal an
order-one conditioned deficit.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

omit [DecidableEq ι] in
/-- Eventual-absorption mass is nonnegative. -/
theorem quittingTailEventualAbsorption_nonneg
    (roots : ℕ → ι → PMF Bool) (time : ℕ) :
    0 ≤ quittingTailEventualAbsorption roots time := by
  unfold quittingTailEventualAbsorption
  exact sub_nonneg.mpr <| le_of_tendsto'
    (tendsto_quittingJointSurvivalLimit roots time)
    (fun fuel ↦ quittingJointSurvivalWeight_le_one roots time fuel)

omit [DecidableEq ι] in
/-- Zero remaining absorption is absorbing for the conditioned clock: the
current row has zero absorption and the successor still has zero remaining
absorption. -/
theorem quittingTailEventualAbsorption_eq_zero_step
    (roots : ℕ → ι → PMF Bool) (time : ℕ)
    (hzero : quittingTailEventualAbsorption roots time = 0) :
    quittingRootAbsorptionMass (roots time) = 0 ∧
      quittingTailEventualAbsorption roots (time + 1) = 0 := by
  have hdecomposition :=
    quittingTailEventualAbsorption_eq_absorption_add_continue_mul_succ
      roots time
  have habsorption := quittingRootAbsorptionMass_nonneg (roots time)
  have hcontinuation := quittingStationaryContinueMass_nonneg (roots time)
  have hnext := quittingTailEventualAbsorption_nonneg roots (time + 1)
  have hcontinuationProduct : 0 ≤
      quittingStationaryContinueMass (roots time) *
        quittingTailEventualAbsorption roots (time + 1) :=
    mul_nonneg hcontinuation hnext
  have hproduct : quittingStationaryContinueMass (roots time) *
      quittingTailEventualAbsorption roots (time + 1) = 0 := by
    nlinarith
  have habsorptionZero : quittingRootAbsorptionMass (roots time) = 0 := by
    nlinarith
  have hcontinueOne : quittingStationaryContinueMass (roots time) = 1 := by
    unfold quittingRootAbsorptionMass at habsorptionZero
    linarith
  rw [hcontinueOne, one_mul] at hproduct
  exact ⟨habsorptionZero, hproduct⟩

omit [DecidableEq ι] in
/-- Once eventual absorption vanishes, every later row is all-Continue in
aggregate and conditioning is unavailable forever. -/
theorem quittingTailEventualAbsorption_eq_zero_forall_add
    (roots : ℕ → ι → PMF Bool) (time : ℕ)
    (hzero : quittingTailEventualAbsorption roots time = 0) :
    ∀ fuel,
      quittingTailEventualAbsorption roots (time + fuel) = 0 ∧
        quittingRootAbsorptionMass (roots (time + fuel)) = 0 := by
  intro fuel
  have hmass : quittingTailEventualAbsorption roots (time + fuel) = 0 := by
    induction fuel with
    | zero => simpa using hzero
    | succ fuel ih =>
        have hstep :=
          (quittingTailEventualAbsorption_eq_zero_step
            roots (time + fuel) ih).2
        simpa [Nat.add_assoc] using hstep
  exact ⟨hmass,
    (quittingTailEventualAbsorption_eq_zero_step
      roots (time + fuel) hmass).1⟩

omit [DecidableEq ι] in
/-- Exact accounting identity behind conditioned floor viability.  It uses no
game-theoretic hypotheses: the displayed value is the convex combination of
the conditioned value and the phantom boundary by definition. -/
theorem quittingTailEventualAbsorption_mul_conditionedFloorDeficit
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary floor : Payoff ι) (time : ℕ) (who : ι)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    quittingTailEventualAbsorption roots time *
        (floor who -
          quittingTailConditionedValue roots value boundary time who) =
    quittingJointSurvivalLimit roots time *
          (boundary who - floor who) -
        (value time who - floor who) := by
  have hdenom : 1 - quittingJointSurvivalLimit roots time ≠ 0 := by
    simpa [quittingTailEventualAbsorption] using hpositive.ne'
  unfold quittingTailConditionedValue quittingTailEventualAbsorption
  field_simp [hdenom]
  ring

omit [DecidableEq ι] in
/-- A displayed floor bound leaves only phantom-boundary slack available to
pay a conditioned floor deficit. -/
theorem quittingTailEventualAbsorption_mul_conditionedFloorDeficit_le
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary floor : Payoff ι) (time : ℕ) (who : ι)
    (hpositive : 0 < quittingTailEventualAbsorption roots time)
    (hfloor : floor who ≤ value time who) :
    quittingTailEventualAbsorption roots time *
        (floor who -
          quittingTailConditionedValue roots value boundary time who) ≤
      quittingJointSurvivalLimit roots time *
        (boundary who - floor who) := by
  rw [quittingTailEventualAbsorption_mul_conditionedFloorDeficit
    roots value boundary floor time who hpositive]
  linarith

omit [DecidableEq ι] in
/-- Any conditioned floor violation is possible only in a coordinate where
the phantom boundary has strict punishment slack. -/
theorem boundary_gt_floor_of_quittingTailConditionedValue_lt_floor
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary floor : Payoff ι) (time : ℕ) (who : ι)
    (hpositive : 0 < quittingTailEventualAbsorption roots time)
    (hfloor : floor who ≤ value time who)
    (hviolation :
      quittingTailConditionedValue roots value boundary time who < floor who) :
    floor who < boundary who := by
  have hidentity :=
    quittingTailEventualAbsorption_mul_conditionedFloorDeficit
      roots value boundary floor time who hpositive
  have hdeficit : 0 < quittingTailEventualAbsorption roots time *
      (floor who -
        quittingTailConditionedValue roots value boundary time who) :=
    mul_pos hpositive (sub_pos.mpr hviolation)
  have hsurplus : 0 ≤ value time who - floor who := sub_nonneg.mpr hfloor
  have hproduct : 0 < quittingJointSurvivalLimit roots time *
      (boundary who - floor who) := by
    linarith
  have hsurvival := quittingJointSurvivalLimit_nonneg roots time
  by_contra hnot
  have hslack : boundary who - floor who ≤ 0 :=
    sub_nonpos.mpr (le_of_not_gt hnot)
  have : quittingJointSurvivalLimit roots time *
      (boundary who - floor who) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hsurvival hslack
  linarith

/-! ## The affine-shrink no-free-lunch identity -/

/-- Shrink a conditioned value toward its phantom boundary.  This is the
natural operation for restoring a strict floor coordinate, but it also
restores part of the boundary mass. -/
def quittingConditionedAffineShrink
    (boundary value : Payoff ι) (scale : ℝ) : Payoff ι :=
  fun who ↦ boundary who + scale * (value who - boundary who)

omit [Fintype ι] [DecidableEq ι] in
/-- A finite payoff vector can be moved a common positive distance away from
a floor-dominating boundary while retaining the floor, provided the target
value is floor-safe on every tight boundary coordinate. -/
theorem exists_pos_scale_floor_le_quittingConditionedAffineShrink
    [Finite ι]
    (boundary value floor : Payoff ι)
    (hboundary : ∀ who, floor who ≤ boundary who)
    (htight : ∀ who, boundary who = floor who → floor who ≤ value who) :
    ∃ scale : ℝ, 0 < scale ∧ scale ≤ 1 ∧ ∀ who,
      floor who ≤ quittingConditionedAffineShrink boundary value scale who := by
  have hall : ∀ᶠ scale : ℝ in 𝓝[>] (0 : ℝ), ∀ who,
      floor who ≤ quittingConditionedAffineShrink boundary value scale who := by
    rw [Filter.eventually_all]
    intro who
    by_cases hstrict : floor who < boundary who
    · have hcontinuous : ContinuousAt (fun scale : ℝ ↦
          quittingConditionedAffineShrink boundary value scale who) 0 := by
        unfold quittingConditionedAffineShrink
        fun_prop
      have hzero : floor who <
          quittingConditionedAffineShrink boundary value 0 who := by
        simpa [quittingConditionedAffineShrink] using hstrict
      exact ((continuousAt_const.eventually_lt hcontinuous hzero).filter_mono
        nhdsWithin_le_nhds).mono fun _ h ↦ h.le
    · have htightWho : boundary who = floor who :=
        le_antisymm (le_of_not_gt hstrict) (hboundary who)
      have hvalue := htight who htightWho
      filter_upwards [self_mem_nhdsWithin] with scale hscale
      unfold quittingConditionedAffineShrink
      rw [htightWho]
      have hscaleNonneg : 0 ≤ scale := hscale.le
      nlinarith [mul_nonneg hscaleNonneg (sub_nonneg.mpr hvalue)]
  have hone : ∀ᶠ scale : ℝ in 𝓝 0, scale < 1 :=
    continuousAt_id.eventually_lt continuousAt_const zero_lt_one
  obtain ⟨scale, hproperties, hscalePos⟩ :=
    (hall.and (hone.filter_mono nhdsWithin_le_nhds)).and
      self_mem_nhdsWithin |>.exists
  exact ⟨scale, hscalePos, hproperties.2.le, hproperties.1⟩

omit [Fintype ι] [DecidableEq ι] in
/-- The canonical coefficient recursion under affine shrinking.  If a
conditioned step has absorption coefficient `alpha`, then shrinking its
current state by `scale` and its successor by `nextScale` preserves the same
absorbing delivery with new absorption coefficient `scale * alpha` under the
displayed coefficient transport equation. -/
theorem quittingConditionedAffineShrink_step
    (boundary current next delivery : Payoff ι)
    (alpha scale nextScale : ℝ)
    (hcurrent : current = fun who ↦
      alpha * delivery who + (1 - alpha) * next who)
    (htransport :
      (1 - scale * alpha) * nextScale = scale * (1 - alpha)) :
    quittingConditionedAffineShrink boundary current scale = fun who ↦
      (scale * alpha) * delivery who +
        (1 - scale * alpha) *
          quittingConditionedAffineShrink boundary next nextScale who := by
  funext who
  unfold quittingConditionedAffineShrink
  rw [congrFun hcurrent who]
  calc
    boundary who +
        scale *
          (alpha * delivery who + (1 - alpha) * next who - boundary who) =
      scale * alpha * delivery who +
        (1 - scale * alpha) * boundary who +
          scale * (1 - alpha) * (next who - boundary who) := by ring
    _ = scale * alpha * delivery who +
        (1 - scale * alpha) * boundary who +
          ((1 - scale * alpha) * nextScale) *
            (next who - boundary who) := by rw [htransport]
    _ = scale * alpha * delivery who +
        (1 - scale * alpha) *
          (boundary who + nextScale * (next who - boundary who)) := by ring

/-- The next shrink scale selected by exact coefficient matching. -/
def quittingConditionedAffineShrinkNextScale
    (alpha scale : ℝ) : ℝ :=
  scale * (1 - alpha) / (1 - scale * alpha)

omit [DecidableEq ι] in
/-- The canonical next scale satisfies the exact matching equation whenever
the new continuation coefficient is nonzero. -/
theorem quittingConditionedAffineShrinkNextScale_transport
    (alpha scale : ℝ) (hnonzero : 1 - scale * alpha ≠ 0) :
    (1 - scale * alpha) *
        quittingConditionedAffineShrinkNextScale alpha scale =
      scale * (1 - alpha) := by
  unfold quittingConditionedAffineShrinkNextScale
  field_simp [hnonzero]

omit [DecidableEq ι] in
/-- **One-step no-free-lunch identity.**  Exact coefficient transport moves
the unshrunk boundary share backward through the new continuation weight.
Thus repairing viability by shrinking cannot destroy the missing mass. -/
theorem quittingConditionedAffineShrink_complement_transport
    (alpha scale nextScale : ℝ)
    (htransport :
      (1 - scale * alpha) * nextScale = scale * (1 - alpha)) :
    (1 - scale * alpha) * (1 - nextScale) = 1 - scale := by
  nlinarith

omit [DecidableEq ι] in
/-- The one-step complement identity telescopes exactly.  The product on the
left is the finite survival weight of the shrunk chronology. -/
theorem quittingConditionedAffineShrink_survival_mul_complement
    (alpha scale : ℕ → ℝ)
    (htransport : ∀ time,
      (1 - scale time * alpha time) * (1 - scale (time + 1)) =
        1 - scale time)
    (fuel : ℕ) :
    (∏ time ∈ Finset.range fuel,
        (1 - scale time * alpha time)) * (1 - scale fuel) =
      1 - scale 0 := by
  induction fuel with
  | zero => simp
  | succ fuel ih =>
      rw [Finset.prod_range_succ]
      calc
        ((∏ time ∈ Finset.range fuel,
              (1 - scale time * alpha time)) *
            (1 - scale fuel * alpha fuel)) *
            (1 - scale (fuel + 1)) =
          (∏ time ∈ Finset.range fuel,
              (1 - scale time * alpha time)) *
            ((1 - scale fuel * alpha fuel) *
              (1 - scale (fuel + 1))) := by ring
        _ = (∏ time ∈ Finset.range fuel,
              (1 - scale time * alpha time)) *
            (1 - scale fuel) := by rw [htransport fuel]
        _ = 1 - scale 0 := ih

omit [DecidableEq ι] in
/-- **Persistent survival floor.**  For unit-interval shrink and absorption
weights, the finite survival weight of every exactly matched shrunk path is
at least the initially restored boundary share `1 - scale 0`.  Any strict
initial shrink therefore recreates positive Never mass. -/
theorem one_sub_scale_zero_le_quittingConditionedAffineShrink_survival
    (alpha scale : ℕ → ℝ)
    (hunit : ∀ time, 0 ≤ scale time * alpha time ∧
      scale time * alpha time ≤ 1)
    (hscale : ∀ time, 0 ≤ scale time)
    (htransport : ∀ time,
      (1 - scale time * alpha time) * (1 - scale (time + 1)) =
        1 - scale time)
    (fuel : ℕ) :
    1 - scale 0 ≤
      ∏ time ∈ Finset.range fuel, (1 - scale time * alpha time) := by
  have hproduct : 0 ≤
      ∏ time ∈ Finset.range fuel, (1 - scale time * alpha time) := by
    apply Finset.prod_nonneg
    intro time htime
    exact sub_nonneg.mpr (hunit time).2
  have hcomplement : 1 - scale fuel ≤ 1 := by
    linarith [hscale fuel]
  have hmul :
      (∏ time ∈ Finset.range fuel,
          (1 - scale time * alpha time)) * (1 - scale fuel) ≤
        ∏ time ∈ Finset.range fuel,
          (1 - scale time * alpha time) := by
    nlinarith
  rw [quittingConditionedAffineShrink_survival_mul_complement
    alpha scale htransport fuel] at hmul
  exact hmul

namespace QuittingCounterexampleSeamWitness

variable {regime : QuittingCounterexampleRegime reward}
    (seam : QuittingCounterexampleSeamWitness regime)

/-- The optimized tail value after removing the positive-survival phantom
boundary and conditioning on eventual absorption. -/
def conditionedTailValue (time : ℕ) : Payoff ι :=
  quittingTailConditionedValue
    (quittingDynamicDebtTailRoots seam.tail)
    (fun date ↦ (seam.tail date).1.1) seam.limit.value time

/-- The conditioned annotation is the honest terminal delivery divided by
the remaining eventual-absorption probability. -/
theorem conditionedTailValue_eq_terminalValue_div (time : ℕ) :
    seam.conditionedTailValue time = fun who ↦
      quittingRootSequenceTerminalValue reward
          (quittingDynamicDebtTailRoots seam.tail) who time /
        quittingTailEventualAbsorption
          (quittingDynamicDebtTailRoots seam.tail) time := by
  apply quittingTailConditionedValue_eq_terminalValue_div
    (reward := reward)
  · exact fun date ↦ (seam.tail_edge date).1.1
  · exact quittingRewardBound_nonneg reward
  · exact abs_reward_le_quittingRewardBound reward
  · exact seam.value_tendsto

/-- The conditioned floor deficit of the canonical counterexample tail is
bounded by the corresponding strict slack at its phantom plateau. -/
theorem eventualAbsorption_mul_conditionedPunishmentDeficit_le
    (time : ℕ) (who : ι)
    (hpositive : 0 < quittingTailEventualAbsorption
      (quittingDynamicDebtTailRoots seam.tail) time) :
    quittingTailEventualAbsorption
          (quittingDynamicDebtTailRoots seam.tail) time *
        (quittingPunishmentValue reward who -
          seam.conditionedTailValue time who) ≤
      quittingJointSurvivalLimit
          (quittingDynamicDebtTailRoots seam.tail) time *
        (seam.limit.value who - quittingPunishmentValue reward who) := by
  exact quittingTailEventualAbsorption_mul_conditionedFloorDeficit_le
    (quittingDynamicDebtTailRoots seam.tail)
    (fun date ↦ (seam.tail date).1.1) seam.limit.value
    (quittingPunishmentValue reward) time who hpositive
    (seam.punishmentValue_le_tailValue time who)

/-- Every coordinate on the tight plateau face remains punishment-rational
after conditioning, at every date where eventual absorption is positive. -/
theorem punishmentValue_le_conditionedTailValue_of_limit_tight
    (time : ℕ) (who : ι)
    (hpositive : 0 < quittingTailEventualAbsorption
      (quittingDynamicDebtTailRoots seam.tail) time)
    (htight : seam.limit.value who = quittingPunishmentValue reward who) :
    quittingPunishmentValue reward who ≤
      seam.conditionedTailValue time who := by
  exact floor_le_quittingTailConditionedValue_of_boundary_eq_floor
    (quittingDynamicDebtTailRoots seam.tail)
    (fun date ↦ (seam.tail date).1.1) seam.limit.value
    (quittingPunishmentValue reward) time who hpositive
    htight (seam.punishmentValue_le_tailValue time who)

/-- A conditioned punishment-floor violation forces strict plateau slack in
the same coordinate. -/
theorem punishmentValue_lt_limitValue_of_conditionedTailValue_lt
    (time : ℕ) (who : ι)
    (hpositive : 0 < quittingTailEventualAbsorption
      (quittingDynamicDebtTailRoots seam.tail) time)
    (hviolation : seam.conditionedTailValue time who <
      quittingPunishmentValue reward who) :
    quittingPunishmentValue reward who < seam.limit.value who := by
  exact boundary_gt_floor_of_quittingTailConditionedValue_lt_floor
    (quittingDynamicDebtTailRoots seam.tail)
    (fun date ↦ (seam.tail date).1.1) seam.limit.value
    (quittingPunishmentValue reward) time who hpositive
    (seam.punishmentValue_le_tailValue time who) hviolation

/-- At each conditionable date, either the whole conditioned vector is above
the punishment floor, or one explicit violating coordinate is funded by
strict phantom-plateau slack and satisfies the quantitative deficit budget. -/
theorem conditionedTail_floor_or_strictPlateauSlack
    (time : ℕ)
    (hpositive : 0 < quittingTailEventualAbsorption
      (quittingDynamicDebtTailRoots seam.tail) time) :
    (∀ who, quittingPunishmentValue reward who ≤
        seam.conditionedTailValue time who) ∨
      ∃ who,
        seam.conditionedTailValue time who <
            quittingPunishmentValue reward who ∧
          quittingPunishmentValue reward who < seam.limit.value who ∧
          quittingTailEventualAbsorption
                (quittingDynamicDebtTailRoots seam.tail) time *
              (quittingPunishmentValue reward who -
                seam.conditionedTailValue time who) ≤
            quittingJointSurvivalLimit
                (quittingDynamicDebtTailRoots seam.tail) time *
              (seam.limit.value who -
                quittingPunishmentValue reward who) := by
  classical
  by_cases hall : ∀ who, quittingPunishmentValue reward who ≤
      seam.conditionedTailValue time who
  · exact Or.inl hall
  · push Not at hall
    obtain ⟨who, hviolation⟩ := hall
    exact Or.inr ⟨who, hviolation,
      seam.punishmentValue_lt_limitValue_of_conditionedTailValue_lt
        time who hpositive hviolation,
      seam.eventualAbsorption_mul_conditionedPunishmentDeficit_le
        time who hpositive⟩

/-- Although conditioning can cross the punishment floor, every conditioned
state admits a common strictly positive affine move toward the phantom
boundary that restores all punishment coordinates simultaneously. -/
theorem exists_pos_scale_conditionedTailAffineShrink_floor
    (time : ℕ)
    (hpositive : 0 < quittingTailEventualAbsorption
      (quittingDynamicDebtTailRoots seam.tail) time) :
    ∃ scale : ℝ, 0 < scale ∧ scale ≤ 1 ∧ ∀ who,
      quittingPunishmentValue reward who ≤
        quittingConditionedAffineShrink seam.limit.value
          (seam.conditionedTailValue time) scale who := by
  apply exists_pos_scale_floor_le_quittingConditionedAffineShrink
  · exact seam.punishmentValue_le_limitValue
  · intro who htight
    exact seam.punishmentValue_le_conditionedTailValue_of_limit_tight
      time who hpositive htight

/-- **No-free-lunch for a viable affine shrink of the canonical tail.**
Suppose every conditioned date is defined and a unit-interval scale is
transported by exact coefficient matching.  The putative rescaled absorption
weights `scale_t * alpha_t` leave at least `1 - scale_0` survival after every
finite horizon.  Thus any nontrivial initial shrink toward the floor-safe
phantom boundary recreates a positive Never component. -/
theorem one_sub_scale_zero_le_conditionedTailAffineShrink_survival
    (scale : ℕ → ℝ)
    (hscale : ∀ time, scale time ∈ Set.Icc 0 1)
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption
      (quittingDynamicDebtTailRoots seam.tail) time)
    (htransport : ∀ time,
      (1 - scale time *
          quittingTailConditionedAbsorptionWeight
            (quittingDynamicDebtTailRoots seam.tail) time) *
          (1 - scale (time + 1)) =
        1 - scale time)
    (fuel : ℕ) :
    1 - scale 0 ≤
      ∏ time ∈ Finset.range fuel,
        (1 - scale time *
          quittingTailConditionedAbsorptionWeight
            (quittingDynamicDebtTailRoots seam.tail) time) := by
  let alpha : ℕ → ℝ := fun time ↦
    quittingTailConditionedAbsorptionWeight
      (quittingDynamicDebtTailRoots seam.tail) time
  have halpha : ∀ time, alpha time ∈ Set.Icc 0 1 := by
    intro time
    exact (quittingTailConditionedWeights_mem_unitInterval
      (quittingDynamicDebtTailRoots seam.tail) time
      (hpositive (time + 1)).le (hpositive time)).1
  apply one_sub_scale_zero_le_quittingConditionedAffineShrink_survival
    alpha scale
  · intro time
    constructor
    · exact mul_nonneg (hscale time).1 (halpha time).1
    · calc
        scale time * alpha time ≤ 1 * alpha time :=
          mul_le_mul_of_nonneg_right (hscale time).2 (halpha time).1
        _ ≤ 1 := by simpa using (halpha time).2
  · exact fun time ↦ (hscale time).1
  · exact htransport

/-- If the phantom plateau is the punishment vector coordinatewise, the
entire conditioned tail is floor-admissible wherever conditioning is
defined. -/
theorem punishmentValue_le_conditionedTailValue_of_limit_eq_punishment
    (hboundary : seam.limit.value = quittingPunishmentValue reward)
    (time : ℕ)
    (hpositive : 0 < quittingTailEventualAbsorption
      (quittingDynamicDebtTailRoots seam.tail) time)
    (who : ι) :
    quittingPunishmentValue reward who ≤
      seam.conditionedTailValue time who := by
  apply seam.punishmentValue_le_conditionedTailValue_of_limit_tight
    time who hpositive
  exact congrFun hboundary who

end QuittingCounterexampleSeamWitness

end GameTheory
