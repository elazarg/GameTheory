/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingSupportWitnessAbsorptionBridge
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Support-witness path compiler

A witness-retaining path carries more information than bare membership in a
set-valued quitting correspondence: every action used with positive
probability is approximately optimal at the actual continuation carried by
that path.  This retained support information makes Simon's stochastic
rank-one Case 1 unnecessary.  The ledger clock is dominated deterministically
by the players' own survival clocks, and the first own-survival crossing can
be used as the phase switch.

This module closes the remaining analytic and game-theoretic bridges from
such a path to terminal and uniform equilibrium statements.

* Divergence of the sum of one-stage absorption probabilities implies complete
  absorption.
* Approximate individual rationality supplies the selected player's closed
  tail, with the rationality error charged only once.
* A completely absorbing `δ`-support-witness path that is `r`-rational at
  every continuation compiles to terminal Nash error

  `2δ + r + sqrt(δ) * (2 + 7M)`.

* Consequently, support error `δ` and rationality error `ε` give a direct
  `3ε` theorem whenever

  `2δ + sqrt(δ) * (2 + 7M) ≤ 2ε`.

* If witness-retaining, individually rational, divergently absorbing paths
  exist at every positive accuracy, the quitting game has a uniform-
  equilibrium payoff.

The support contribution is `O(sqrt δ)`.  Thus this retained-witness route
needs only quadratic-scale support accuracy for linear equilibrium accuracy,
in contrast with the fourth-order support restriction in Simon's published
Case-1 argument after the support witness has been forgotten.

The remaining problem is path production: construct witness-retaining paths
which are approximately individually rational at every continuation and have
divergent total absorption.  Punishment assembly, ledger accumulation, and
deleted-survival bookkeeping are discharged here.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The one-stage probability that at least one player quits. -/
def quittingTotalAbsorptionCharge
    (roots : ℕ → ι → PMF Bool) (time : ℕ) : ℝ :=
  quittingRootAbsorptionMass (roots time)

omit [DecidableEq ι] in
/-- Total absorption charge is nonnegative. -/
theorem quittingTotalAbsorptionCharge_nonneg
    (roots : ℕ → ι → PMF Bool) (time : ℕ) :
    0 ≤ quittingTotalAbsorptionCharge roots time := by
  unfold quittingTotalAbsorptionCharge quittingRootAbsorptionMass
  exact sub_nonneg.mpr (quittingStationaryContinueMass_le_one (roots time))

omit [DecidableEq ι] in
/-- A finite joint-survival prefix is bounded by the exponential of minus the
accumulated total absorption charge. -/
theorem quittingSurvivalPrefix_le_exp_neg_sum_totalAbsorptionCharge
    (roots : ℕ → ι → PMF Bool) :
    ∀ cutoff,
      quittingSurvivalPrefix roots cutoff ≤
        Real.exp (-(∑ time ∈ Finset.range cutoff,
          quittingTotalAbsorptionCharge roots time)) := by
  intro cutoff
  induction cutoff with
  | zero =>
      simp [quittingSurvivalPrefix]
  | succ cutoff ih =>
      let accumulated := ∑ time ∈ Finset.range cutoff,
        quittingTotalAbsorptionCharge roots time
      let charge := quittingTotalAbsorptionCharge roots cutoff
      have hcontinue :
          quittingStationaryContinueMass (roots cutoff) = 1 - charge := by
        dsimp only [charge]
        unfold quittingTotalAbsorptionCharge quittingRootAbsorptionMass
        ring
      rw [Finset.sum_range_succ, quittingSurvivalPrefix_succ, hcontinue]
      change
        quittingSurvivalPrefix roots cutoff * (1 - charge) ≤
          Real.exp (-(accumulated + charge))
      calc
        quittingSurvivalPrefix roots cutoff * (1 - charge) ≤
            Real.exp (-accumulated) * Real.exp (-charge) := by
          exact mul_le_mul ih (Real.one_sub_le_exp_neg charge)
            (by
              rw [← hcontinue]
              exact quittingStationaryContinueMass_nonneg (roots cutoff))
            (Real.exp_nonneg _)
        _ = Real.exp (-(accumulated + charge)) := by
          rw [← Real.exp_add]
          congr 1
          ring

omit [DecidableEq ι] in
/-- Simon's path condition `sum q(p_i) = infinity` implies complete
absorption of the root path. -/
theorem isCompletelyAbsorbing_of_not_summable_totalAbsorptionCharge
    (roots : ℕ → ι → PMF Bool)
    (hdiverges : ¬Summable (quittingTotalAbsorptionCharge roots)) :
    IsCompletelyAbsorbing roots := by
  have hsum : Tendsto (fun cutoff : ℕ ↦
      ∑ time ∈ Finset.range cutoff,
        quittingTotalAbsorptionCharge roots time)
      atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg
      (quittingTotalAbsorptionCharge_nonneg roots)).1 hdiverges
  have hexp : Tendsto (fun cutoff : ℕ ↦
      Real.exp (-(∑ time ∈ Finset.range cutoff,
        quittingTotalAbsorptionCharge roots time)))
      atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hsum
  exact squeeze_zero
    (quittingSurvivalPrefix_nonneg roots)
    (quittingSurvivalPrefix_le_exp_neg_sum_totalAbsorptionCharge roots)
    hexp

/-- Approximate individual rationality at a boundary value supplies a
player-specific closed tail.  The rationality error and the approximation of
the stationary punishment infimum are charged additively. -/
theorem exists_quittingTargetClosedTail_le_of_punishmentValue_sub_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : ι) (boundary rationalityError : ℝ)
    {tailSlack : ℝ} (htailSlack : 0 < tailSlack)
    (hir : quittingPunishmentValue reward target - rationalityError ≤ boundary) :
    ∃ tail : ℕ → ι → PMF Bool,
      IsQuittingTargetClosedTail reward tail target ∧
      quittingRootSequenceTerminalValue reward tail target 0 ≤
        boundary + rationalityError + tailSlack := by
  obtain ⟨root, hroot⟩ :=
    exists_stationaryRoot_cap_lt_punishmentValue_add
      reward target htailSlack
  obtain ⟨tail, hclosed, hvalue⟩ :=
    exists_quittingSupportWitnessTargetClosedTail_of_stationaryRoot
      reward root target
  refine ⟨tail, hclosed, ?_⟩
  rw [hvalue]
  linarith

/-- **Quantitative support-witness path compiler.**

A completely absorbing path whose one-stage roots satisfy the support-local
`δ` condition and whose continuation values are within `rationalityError` of
every player's punishment value produces a terminal approximate Nash profile
with error

`2δ + rationalityError + sqrt(δ) * (2 + 7M)`.

The square-root scale is used for both the ledger cap and the own-survival
threshold. -/
theorem
    exists_isεAsymptoticNash_of_completelyAbsorbing_supportRationalPath
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan : ℕ → ι → PMF Bool) {δ rationalityError : ℝ}
    (hδ : 0 < δ) (hrationalityError : 0 ≤ rationalityError)
    (hsupport : IsQuittingRootSequenceSupportApproxNash reward plan δ)
    (habsorbing : IsCompletelyAbsorbing plan)
    (hir : ∀ target time,
      quittingPunishmentValue reward target - rationalityError ≤
        quittingRootSequenceTerminalValue reward plan target time) :
    ∃ profile : (quittingGame reward).BehaviorProfile,
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward)
        (2 * δ + rationalityError +
          Real.sqrt δ * (2 + 7 * quittingRewardBound reward)) profile := by
  let scale := Real.sqrt δ
  have hscalePos : 0 < scale := by
    simpa only [scale] using Real.sqrt_pos.2 hδ
  have hsquare : δ = scale * scale := by
    dsimp only [scale]
    nlinarith [Real.sq_sqrt hδ.le]
  apply exists_isεAsymptoticNash_of_hasQuittingSupportWitnessTailPackage
    reward
  refine ⟨plan, δ, scale, scale, rationalityError + scale,
    hδ.le, hscalePos, hscalePos,
    add_nonneg hrationalityError hscalePos.le, ?_, hsupport, ?_, ?_, ?_⟩
  · exact hsquare.le
  · exact exists_ownSurvival_crossing_of_completelyAbsorbing
      plan hscalePos habsorbing
  · intro target
    obtain ⟨tail, hclosed, htail⟩ :=
      exists_quittingTargetClosedTail_le_of_punishmentValue_sub_le
        reward target
          (quittingRootSequenceTerminalValue reward plan target
            (quittingSupportSurvivalSwitchIndex plan scale))
          rationalityError hscalePos
          (hir target (quittingSupportSurvivalSwitchIndex plan scale))
    exact ⟨tail, hclosed, by simpa [add_assoc] using htail⟩
  · dsimp only [scale]
    ring_nf
    exact le_rfl

/-- The same compiler with divergent total absorption in place of the
already-closed complete-absorption predicate. -/
theorem
    exists_isεAsymptoticNash_of_divergentAbsorption_supportRationalPath
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan : ℕ → ι → PMF Bool) {δ rationalityError : ℝ}
    (hδ : 0 < δ) (hrationalityError : 0 ≤ rationalityError)
    (hsupport : IsQuittingRootSequenceSupportApproxNash reward plan δ)
    (hdiverges : ¬Summable (quittingTotalAbsorptionCharge plan))
    (hir : ∀ target time,
      quittingPunishmentValue reward target - rationalityError ≤
        quittingRootSequenceTerminalValue reward plan target time) :
    ∃ profile : (quittingGame reward).BehaviorProfile,
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward)
        (2 * δ + rationalityError +
          Real.sqrt δ * (2 + 7 * quittingRewardBound reward)) profile :=
  exists_isεAsymptoticNash_of_completelyAbsorbing_supportRationalPath
    reward plan hδ hrationalityError hsupport
      (isCompletelyAbsorbing_of_not_summable_totalAbsorptionCharge
        plan hdiverges)
      hir

/-- **Two-tolerance form matching Simon's parameters.**

Here `δ` is the support error and `ε` is the individual-rationality error.
If the support-generated overhead is at most `2ε`, then the compiled path is
a terminal `3ε`-Nash profile.  The condition is

`2δ + sqrt(δ) * (2 + 7M) ≤ 2ε`.

In particular, support accuracy of quadratic order in `ε` suffices. -/
theorem
    exists_isThreeEpsilonAsymptoticNash_of_divergentAbsorption_supportRationalPath
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan : ℕ → ι → PMF Bool) {δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε)
    (hsupport : IsQuittingRootSequenceSupportApproxNash reward plan δ)
    (hdiverges : ¬Summable (quittingTotalAbsorptionCharge plan))
    (hir : ∀ target time,
      quittingPunishmentValue reward target - ε ≤
        quittingRootSequenceTerminalValue reward plan target time)
    (hoverhead :
      2 * δ + Real.sqrt δ *
        (2 + 7 * quittingRewardBound reward) ≤ 2 * ε) :
    ∃ profile : (quittingGame reward).BehaviorProfile,
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) (3 * ε) profile := by
  obtain ⟨profile, hprofile⟩ :=
    exists_isεAsymptoticNash_of_divergentAbsorption_supportRationalPath
      reward plan hδ hε.le hsupport hdiverges hir
  refine ⟨profile, ?_⟩
  intro who deviation
  have hlocal := hprofile who deviation
  linarith

/-- **Uniform-payoff theorem from witness-retaining paths.**

Assume that for every positive `δ` there is a root path satisfying:

* support-wise `δ` one-stage optimality;
* divergent total absorption `sum q(p_i) = infinity`; and
* `δ`-individual rationality at every continuation.

Then the finite quitting game has a uniform-equilibrium payoff. -/
theorem
    quittingGame_exists_uniformEquilibriumPayoff_of_supportRationalDivergentPaths
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hpaths : ∀ δ : ℝ, 0 < δ →
      ∃ plan : ℕ → ι → PMF Bool,
        IsQuittingRootSequenceSupportApproxNash reward plan δ ∧
        ¬Summable (quittingTotalAbsorptionCharge plan) ∧
        ∀ target time,
          quittingPunishmentValue reward target - δ ≤
            quittingRootSequenceTerminalValue reward plan target time) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors
    reward
  intro ε hε
  let bound := quittingRewardBound reward
  let coefficient := 2 + 7 * bound
  let denominator := ε + coefficient + 3
  let scale := ε / denominator
  let δ := scale ^ 2
  have hbound : 0 ≤ bound := by
    exact quittingRewardBound_nonneg reward
  have hcoefficient : 0 ≤ coefficient := by
    dsimp only [coefficient, bound]
    nlinarith
  have hdenominator : 0 < denominator := by
    dsimp only [denominator]
    nlinarith
  have hscale : 0 < scale := by
    exact div_pos hε hdenominator
  have hscaleOne : scale ≤ 1 := by
    dsimp only [scale]
    rw [div_le_iff₀ hdenominator]
    dsimp only [denominator]
    nlinarith
  have hδ : 0 < δ := by
    dsimp only [δ]
    positivity
  have hsqrt : Real.sqrt δ = scale := by
    dsimp only [δ]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hscale]
  obtain ⟨plan, hsupport, hdiverges, hir⟩ := hpaths δ hδ
  obtain ⟨profile, hprofile⟩ :=
    exists_isεAsymptoticNash_of_divergentAbsorption_supportRationalPath
      reward plan hδ hδ.le hsupport hdiverges hir
  have hsquareLe : scale ^ 2 ≤ scale := by
    nlinarith [sq_nonneg scale]
  have hfactor : (coefficient + 3) * scale ≤ ε := by
    dsimp only [scale]
    rw [show (coefficient + 3) * (ε / denominator) =
        ((coefficient + 3) * ε) / denominator by ring]
    rw [div_le_iff₀ hdenominator]
    dsimp only [denominator]
    nlinarith [sq_nonneg ε]
  have herror :
      2 * δ + δ + Real.sqrt δ * coefficient ≤ ε := by
    rw [hsqrt]
    dsimp only [δ]
    calc
      2 * scale ^ 2 + scale ^ 2 + scale * coefficient =
          3 * scale ^ 2 + coefficient * scale := by ring
      _ ≤ 3 * scale + coefficient * scale := by
        nlinarith
      _ = (coefficient + 3) * scale := by ring
      _ ≤ ε := hfactor
  have herror' :
      2 * δ + δ + Real.sqrt δ *
        (2 + 7 * quittingRewardBound reward) ≤ ε := by
    simpa [coefficient, bound] using herror
  refine ⟨profile, ?_⟩
  intro who deviation
  have hlocal := hprofile who deviation
  linarith

end GameTheory
