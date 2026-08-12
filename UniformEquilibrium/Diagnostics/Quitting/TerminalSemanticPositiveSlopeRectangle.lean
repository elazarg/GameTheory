/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPositiveSlopeAtom

/-!
# Four-profile rectangles from positive stopping-law debt slope

A positive debt increment for an observer under another player's complete
stopping-law mixture has a literal four-profile witness.  If one approximate
best response is chosen at the mixed profile, its payoff cross-difference
between the source and full reset endpoint carries the debt increment.

There are two distinct atom statements.  The positive cross-difference
exposes one absorbing terminal atom of the full endpoint rectangle.  For a
small reset weight, approximate optimality additionally forces the
target-side unilateral edge to be profitable, so that same executable edge
exposes a (possibly different) positive payoff atom.  The theorem does not
identify these two coalitions.

The endpoint rectangle is an order-one comparison of four full corner laws.
At the actually used reset mixture, its signed terminal-law cross-effect is
exactly `lambda` times that rectangle.  This must not be confused with a
separately marked event whose corner mass may stay bounded below by a fixed
constant.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Reward-weighted atom of a four-profile terminal-law rectangle. -/
def quittingTerminalPayoffRectangleAtom
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (x00 x01 x10 x11 : (quittingGame reward).BehaviorProfile)
    (observer : ι) (outcome : QuittingTerminalOutcome ι) : ℝ :=
  (quittingTerminalOutcomeMass reward x11 outcome -
      quittingTerminalOutcomeMass reward x10 outcome -
      quittingTerminalOutcomeMass reward x01 outcome +
      quittingTerminalOutcomeMass reward x00 outcome) *
    quittingTerminalOutcomeReward reward outcome observer

omit [DecidableEq ι] in
/-- The terminal atoms sum to the payoff cross-difference of the same four
literal profiles. -/
theorem sum_quittingTerminalPayoffRectangleAtom
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (x00 x01 x10 x11 : (quittingGame reward).BehaviorProfile)
    (observer : ι) :
    (∑ outcome : QuittingTerminalOutcome ι,
        quittingTerminalPayoffRectangleAtom reward x00 x01 x10 x11
          observer outcome) =
      quittingTerminalPayoff reward x11 observer -
        quittingTerminalPayoff reward x10 observer -
        quittingTerminalPayoff reward x01 observer +
        quittingTerminalPayoff reward x00 observer := by
  simp_rw [← quittingTerminalRewardMoment_outcomeMass reward]
  unfold quittingTerminalRewardMoment quittingTerminalPayoffRectangleAtom
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro outcome _
  ring

omit [DecidableEq ι] in
/-- A positive payoff rectangle is carried by a nonempty quitting coalition;
the zero-reward `Never` atom cannot carry it. -/
theorem exists_absorbingTerminalPayoffRectangleAtom
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (x00 x01 x10 x11 : (quittingGame reward).BehaviorProfile)
    (observer : ι) (charge : ℝ) (hcharge : 0 < charge)
    (hrectangle : charge ≤
      quittingTerminalPayoff reward x11 observer -
        quittingTerminalPayoff reward x10 observer -
        quittingTerminalPayoff reward x01 observer +
        quittingTerminalPayoff reward x00 observer) :
    ∃ terminal : {S : Finset ι // S.Nonempty},
      charge ≤ (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
        quittingTerminalPayoffRectangleAtom reward x00 x01 x10 x11
          observer (some terminal) := by
  let outcomes := (Finset.univ : Finset (QuittingTerminalOutcome ι))
  obtain ⟨outcome, _houtcome, houtcomeMax⟩ :=
    Finset.exists_max_image outcomes
      (quittingTerminalPayoffRectangleAtom reward x00 x01 x10 x11 observer)
      Finset.univ_nonempty
  have hsumLe :
      (∑ other : QuittingTerminalOutcome ι,
          quittingTerminalPayoffRectangleAtom reward x00 x01 x10 x11
            observer other) ≤
        (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
          quittingTerminalPayoffRectangleAtom reward x00 x01 x10 x11
            observer outcome := by
    have hbound := outcomes.sum_le_card_nsmul
      (quittingTerminalPayoffRectangleAtom reward x00 x01 x10 x11 observer)
      (quittingTerminalPayoffRectangleAtom reward x00 x01 x10 x11 observer
        outcome)
      (fun other hother => houtcomeMax other hother)
    simpa [outcomes, nsmul_eq_mul, mul_comm] using hbound
  have houtcomeCharge : charge ≤
      (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
        quittingTerminalPayoffRectangleAtom reward x00 x01 x10 x11
          observer outcome := by
    apply hrectangle.trans
    rw [← sum_quittingTerminalPayoffRectangleAtom]
    exact hsumLe
  cases outcome with
  | none =>
      simp [quittingTerminalPayoffRectangleAtom,
        quittingTerminalOutcomeReward] at houtcomeCharge
      linarith
  | some terminal => exact ⟨terminal, houtcomeCharge⟩

/-- **Positive-slope four-profile decoder.**

Let `mixed` be a complete stopping-law mixture of `source` and `target` for
`mover`.  If `observer`'s debt rises by at least `lambda * charge`, and
`deviation` is an approximate best response at `mixed` with error at most
half that charge, then the four full endpoint profiles have a positive
payoff rectangle.

When `lambda ≤ 1/4`, approximate optimality also forces the forward
target-side edge to be profitable.  Thus this one executable edge exposes a
positive terminal payoff atom, although its coalition need not be the
rectangle coalition. -/
theorem exists_rectangleAtom_and_targetEdgeAtom_of_mixedDebtSlope
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι) (hne : observer ≠ mover)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (deviation : (quittingGame reward).BehaviorStrategy observer)
    (lambda charge error : ℝ)
    (hlambda0 : 0 < lambda) (hlambdaQuarter : lambda ≤ 1 / 4)
    (hcharge : 0 < charge) (herror0 : 0 ≤ error)
    (herror : error ≤ lambda * charge / 2)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hslope : lambda * charge ≤
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update profile mover
              (quittingStoppingLawMixtureBehaviorStrategy reward mover
                source target lambda hlambda0.le
                  (hlambdaQuarter.trans (by norm_num))))) observer -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update profile mover source)) observer)
    (hbest : quittingContinuationBestResponseValue reward
          (Function.update profile mover
            (quittingStoppingLawMixtureBehaviorStrategy reward mover
              source target lambda hlambda0.le
                (hlambdaQuarter.trans (by norm_num)))) observer ≤
        quittingTerminalPayoff reward
          (Function.update
            (Function.update profile mover
              (quittingStoppingLawMixtureBehaviorStrategy reward mover
                source target lambda hlambda0.le
                  (hlambdaQuarter.trans (by norm_num))))
            observer deviation) observer + error) :
    let x00 := Function.update profile mover source
    let x01 := Function.update profile mover target
    let x10 := Function.update x00 observer deviation
    let x11 := Function.update x01 observer deviation
    (∃ terminal : {S : Finset ι // S.Nonempty},
      charge / 2 ≤ (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
        quittingTerminalPayoffRectangleAtom reward x00 x01 x10 x11
          observer (some terminal)) ∧
    charge / 4 ≤ quittingTerminalPayoff reward x11 observer -
      quittingTerminalPayoff reward x01 observer ∧
    ∃ terminal : {S : Finset ι // S.Nonempty},
      charge / 4 ≤ (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
        quittingTerminalPayoffDifferenceAtom reward x11 x01 observer
          (some terminal) := by
  dsimp only
  let mixedStrategy := quittingStoppingLawMixtureBehaviorStrategy reward mover
    source target lambda hlambda0.le (hlambdaQuarter.trans (by norm_num))
  let mixed := Function.update profile mover mixedStrategy
  let x00 := Function.update profile mover source
  let x01 := Function.update profile mover target
  let x10 := Function.update x00 observer deviation
  let x11 := Function.update x01 observer deviation
  have hsourceAffine := quittingTerminalPayoff_stoppingLawMixture_eq
    reward profile mover observer source target lambda hlambda0.le
      (hlambdaQuarter.trans (by norm_num))
  have hdeviationAffine := quittingTerminalPayoff_stoppingLawMixture_eq
    reward (Function.update profile observer deviation) mover observer source
      target lambda hlambda0.le (hlambdaQuarter.trans (by norm_num))
  have hcommuteMixed :
      Function.update (Function.update profile observer deviation) mover
          mixedStrategy = Function.update mixed observer deviation := by
    exact Function.update_comm hne deviation mixedStrategy profile
  have hcommuteSource :
      Function.update (Function.update profile observer deviation) mover source =
        x10 := by
    exact Function.update_comm hne deviation source profile
  have hcommuteTarget :
      Function.update (Function.update profile observer deviation) mover target =
        x11 := by
    exact Function.update_comm hne deviation target profile
  change quittingTerminalPayoff reward mixed observer = _ at hsourceAffine
  change quittingTerminalPayoff reward
      (Function.update (Function.update profile observer deviation) mover
        mixedStrategy) observer = _ at hdeviationAffine
  rw [hcommuteMixed, hcommuteSource, hcommuteTarget] at hdeviationAffine
  change lambda * charge ≤
      (quittingContinuationBestResponseValue reward mixed observer -
          quittingTerminalPayoff reward mixed observer) -
        (quittingContinuationBestResponseValue reward x00 observer -
          quittingTerminalPayoff reward x00 observer) at hslope
  change quittingContinuationBestResponseValue reward mixed observer ≤
    quittingTerminalPayoff reward (Function.update mixed observer deviation)
      observer + error at hbest
  have hsourceCap :=
    quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward x00 observer deviation hM hreward
  change quittingTerminalPayoff reward x10 observer ≤
    quittingContinuationBestResponseValue reward x00 observer at hsourceCap
  let rectangle := quittingTerminalPayoff reward x11 observer -
    quittingTerminalPayoff reward x10 observer -
    quittingTerminalPayoff reward x01 observer +
    quittingTerminalPayoff reward x00 observer
  have hscaledRectangle : lambda * charge ≤ lambda * rectangle + error := by
    dsimp only [rectangle]
    linarith
  have hrectangle : charge / 2 ≤ rectangle := by
    have hscaled : lambda * (charge / 2) ≤ lambda * rectangle := by
      nlinarith
    exact (mul_le_mul_iff_of_pos_left hlambda0).mp hscaled
  have hrectanglePositive : 0 < charge / 2 := by positivity
  have hrectangleAtom := exists_absorbingTerminalPayoffRectangleAtom reward
    x00 x01 x10 x11 observer (charge / 2) hrectanglePositive hrectangle
  have hmixedCapLower :=
    quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward mixed observer (mixed observer) hM hreward
  rw [Function.update_eq_self] at hmixedCapLower
  have hmixedGain : -error ≤
      quittingTerminalPayoff reward (Function.update mixed observer deviation)
          observer - quittingTerminalPayoff reward mixed observer := by
    linarith
  let targetGain := quittingTerminalPayoff reward x11 observer -
    quittingTerminalPayoff reward x01 observer
  have htargetGain : charge / 4 ≤ targetGain := by
    dsimp only [targetGain]
    have hlambda1 : lambda ≤ 1 := hlambdaQuarter.trans (by norm_num)
    have hweight : 0 ≤ 1 - 2 * lambda := by linarith
    have herrorCharge : error ≤ lambda * charge / 2 := herror
    dsimp only [rectangle] at hrectangle
    nlinarith
  have htargetPositive : 0 < charge / 4 := by positivity
  have htargetAtom := exists_absorbingTerminalPayoffDifferenceAtom reward x11
    x01 observer (charge / 4) htargetPositive htargetGain
  exact ⟨hrectangleAtom, htargetGain, htargetAtom⟩

/-- The rectangle seen after the small reset is exactly `lambda` times the
full endpoint rectangle, outcome by outcome.  Hence a cutoff-independent
full-corner atom becomes an order-`lambda` cross-toggle at the actually used
reset. -/
theorem quittingTerminalOutcomeMass_smallResetRectangle_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι) (hne : observer ≠ mover)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (deviation : (quittingGame reward).BehaviorStrategy observer)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (outcome : QuittingTerminalOutcome ι) :
    let mixedStrategy := quittingStoppingLawMixtureBehaviorStrategy reward mover
      source target lambda hlambda0 hlambda1
    let mixed := Function.update profile mover mixedStrategy
    let x00 := Function.update profile mover source
    let x01 := Function.update profile mover target
    let x10 := Function.update x00 observer deviation
    let x11 := Function.update x01 observer deviation
    quittingTerminalOutcomeMass reward
          (Function.update mixed observer deviation) outcome -
        quittingTerminalOutcomeMass reward mixed outcome -
        (quittingTerminalOutcomeMass reward x10 outcome -
          quittingTerminalOutcomeMass reward x00 outcome) =
      lambda *
        (quittingTerminalOutcomeMass reward x11 outcome -
          quittingTerminalOutcomeMass reward x10 outcome -
          quittingTerminalOutcomeMass reward x01 outcome +
          quittingTerminalOutcomeMass reward x00 outcome) := by
  dsimp only
  let mixedStrategy := quittingStoppingLawMixtureBehaviorStrategy reward mover
    source target lambda hlambda0 hlambda1
  have hbase := quittingTerminalOutcomeMass_stoppingLawMixture_eq reward profile
    mover source target lambda hlambda0 hlambda1 outcome
  have hdeviation := quittingTerminalOutcomeMass_stoppingLawMixture_eq reward
    (Function.update profile observer deviation) mover source target lambda
      hlambda0 hlambda1 outcome
  have hcommuteMixed :
      Function.update (Function.update profile observer deviation) mover
          mixedStrategy =
        Function.update (Function.update profile mover mixedStrategy) observer
          deviation := by
    exact Function.update_comm hne deviation mixedStrategy profile
  have hcommuteSource :
      Function.update (Function.update profile observer deviation) mover source =
        Function.update (Function.update profile mover source) observer
          deviation := by
    exact Function.update_comm hne deviation source profile
  have hcommuteTarget :
      Function.update (Function.update profile observer deviation) mover target =
        Function.update (Function.update profile mover target) observer
          deviation := by
    exact Function.update_comm hne deviation target profile
  change quittingTerminalOutcomeMass reward
      (Function.update profile mover mixedStrategy) outcome = _ at hbase
  change quittingTerminalOutcomeMass reward
      (Function.update (Function.update profile observer deviation) mover
        mixedStrategy) outcome = _ at hdeviation
  rw [hcommuteMixed, hcommuteSource, hcommuteTarget] at hdeviation
  rw [hbase, hdeviation]
  ring

end GameTheory
