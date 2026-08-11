/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability.DiscreteHazardMixture
import UniformEquilibrium.Quitting.Paths.BehaviorStoppingPayoff

/-!
# Behavioral realization of convex stopping-law mixtures

Mixing two complete unilateral stopping laws is different from interpolating
their hazards row by row.  The former is exactly affine in terminal payoff and
does not repeatedly spend the mixing weight along a long window.  The hazard
below realizes that law mixture by conditioning its mixed stopping mass on
its mixed survival mass.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.ProbabilityMassFunction
open Math.Probability.DiscreteHazard

variable {iota : Type} [Fintype iota] [DecidableEq iota]

/-- A behavior strategy whose live-path stopping law is the convex mixture
of the live-path stopping laws of `source` and `target`. -/
def quittingStoppingLawMixtureBehaviorStrategy
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (who : iota)
    (source target : (quittingGame reward).BehaviorStrategy who)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    (quittingGame reward).BehaviorStrategy who :=
  fun time _history =>
    BooleanHazard.convexMix
      (quittingBehaviorLiveHazard reward source)
      (quittingBehaviorLiveHazard reward target)
      lambda hlambda0 hlambda1 time

omit [DecidableEq iota] in
@[simp] theorem quittingBehaviorLiveHazard_stoppingLawMixture
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (who : iota)
    (source target : (quittingGame reward).BehaviorStrategy who)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    quittingBehaviorLiveHazard reward
        (quittingStoppingLawMixtureBehaviorStrategy reward who source target
          lambda hlambda0 hlambda1) =
      BooleanHazard.convexMix
        (quittingBehaviorLiveHazard reward source)
        (quittingBehaviorLiveHazard reward target)
        lambda hlambda0 hlambda1 := by
  rfl

omit [DecidableEq iota] in
/-- The induced stopping law is exactly the binary convex PMF mixture. -/
theorem quittingBehaviorStoppingLaw_stoppingLawMixture
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (who : iota)
    (source target : (quittingGame reward).BehaviorStrategy who)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    quittingBehaviorStoppingLaw reward
        (quittingStoppingLawMixtureBehaviorStrategy reward who source target
          lambda hlambda0 hlambda1) =
      (mixtureCoin lambda hlambda0 hlambda1).bind
        (fun choose => if choose
          then quittingBehaviorStoppingLaw reward target
          else quittingBehaviorStoppingLaw reward source) := by
  unfold quittingBehaviorStoppingLaw quittingHazardStoppingLaw
  rw [quittingBehaviorLiveHazard_stoppingLawMixture,
    BooleanHazard.toScalar_convexMix,
    ScalarHazard.stoppingLaw_convexMix]

omit [DecidableEq iota] in
/-- Every stopping-time atom retains its `1 - lambda` share of the source
law. -/
theorem one_sub_mul_stoppingLaw_le_stoppingLawMixture
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (who : iota)
    (source target : (quittingGame reward).BehaviorStrategy who)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (choice : Option ℕ) :
    (1 - lambda) *
        (quittingBehaviorStoppingLaw reward source choice).toReal ≤
      (quittingBehaviorStoppingLaw reward
        (quittingStoppingLawMixtureBehaviorStrategy reward who source target
          lambda hlambda0 hlambda1) choice).toReal := by
  rw [quittingBehaviorStoppingLaw_stoppingLawMixture,
    Math.ProbabilityMassFunction.bind_apply_toReal_eq_sum,
    Fintype.sum_bool]
  simp only [mixtureCoin_false_toReal,
    mixtureCoin_true_toReal, Bool.false_eq_true, ↓reduceIte]
  exact le_add_of_nonneg_left
    (mul_nonneg hlambda0 ENNReal.toReal_nonneg)

/-- Terminal payoff is affine in the complete stopping-law mixture.  This is
the cutoff-free collection identity. -/
theorem quittingTerminalPayoff_update_stoppingLawMixture_eq
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : iota)
    (source target : (quittingGame reward).BehaviorStrategy who)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    quittingTerminalPayoff reward
        (Function.update profile who
          (quittingStoppingLawMixtureBehaviorStrategy reward who source target
            lambda hlambda0 hlambda1)) who =
      (1 - lambda) *
          quittingTerminalPayoff reward (Function.update profile who source) who +
        lambda *
          quittingTerminalPayoff reward (Function.update profile who target) who := by
  let value : Option ℕ → ℝ := fun choice =>
    quittingTerminalPayoff reward
      (Function.update profile who
        (quittingPureTimeBehaviorStrategy reward who choice)) who
  have hvalue : ∀ choice, |value choice| ≤ M := by
    intro choice
    exact abs_quittingTerminalPayoff_le reward _ who hM hreward
  have hsource := quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime
    reward profile who source hM hreward
  have htarget := quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime
    reward profile who target hM hreward
  rw [quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime
      reward profile who
        (quittingStoppingLawMixtureBehaviorStrategy reward who source target
          lambda hlambda0 hlambda1) hM hreward,
    quittingBehaviorStoppingLaw_stoppingLawMixture,
    expect_bind_of_bounded _ _ value hvalue,
    expect_eq_sum, Fintype.sum_bool]
  simp only [mixtureCoin_false_toReal,
    mixtureCoin_true_toReal, Bool.false_eq_true, ↓reduceIte]
  rw [← hsource, ← htarget]
  ring

/-- Mixing the prescribed strategy with any profitable replacement collects
exactly the same fraction of its global unilateral gain, independently of the
length or diffuseness of the window. -/
theorem quittingTerminalPayoff_stoppingLawMixture_sub_eq
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : iota)
    (target : (quittingGame reward).BehaviorStrategy who)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    quittingTerminalPayoff reward
          (Function.update profile who
            (quittingStoppingLawMixtureBehaviorStrategy reward who (profile who)
              target lambda hlambda0 hlambda1)) who -
        quittingTerminalPayoff reward profile who =
      lambda *
        (quittingTerminalPayoff reward (Function.update profile who target) who -
          quittingTerminalPayoff reward profile who) := by
  rw [quittingTerminalPayoff_update_stoppingLawMixture_eq
    reward profile who (profile who) target lambda hlambda0 hlambda1 hM hreward,
    Function.update_eq_self]
  ring

end GameTheory
