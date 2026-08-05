/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingSharedPunishment
import Math.PMFProduct.Bool

/-!
# A sharp three-player obstruction for shared quitting punishment

This module studies the cyclic three-player weight

`r_i(S) = -1` when the next player quits and the remaining player does not,
and `r_i(S) = 0` otherwise.

The first results isolate the exact product calculation behind the obstruction:
quitting immediately against a row costs player `i` the probability
`x_next * (1 - x_other)`.  Some cyclic coordinate is always at most `1/4`.
Since every individual punishment floor is `-1`, every shared plan therefore
leaves some player at least `3/4` above its floor.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

namespace QuittingSharedThreePlayer

/-- Three cyclically ordered players. -/
inductive Player
  | a
  | b
  | c
  deriving DecidableEq, Fintype, Inhabited

/-- The next player in the cycle `a -> b -> c -> a`. -/
def next : Player → Player
  | .a => .b
  | .b => .c
  | .c => .a

/-- The other player, two steps ahead in the cycle. -/
def other : Player → Player
  | .a => .c
  | .b => .a
  | .c => .b

@[simp] theorem next_ne_self (who : Player) : next who ≠ who := by
  cases who <;> decide

@[simp] theorem other_ne_self (who : Player) : other who ≠ who := by
  cases who <;> decide

@[simp] theorem next_ne_other (who : Player) : next who ≠ other who := by
  cases who <;> decide

/-- The cyclic obstruction table. -/
def reward : {S : Finset Player // S.Nonempty} → Payoff Player :=
  fun S who => if next who ∈ S.1 ∧ other who ∉ S.1 then -1 else 0

@[simp] theorem reward_nonpos (S : {S : Finset Player // S.Nonempty})
    (who : Player) : reward S who ≤ 0 := by
  simp [reward]

@[simp] theorem neg_one_le_reward
    (S : {S : Finset Player // S.Nonempty}) (who : Player) :
    -1 ≤ reward S who := by
  simp [reward]

@[simp] theorem abs_reward_le_one
    (S : {S : Finset Player // S.Nonempty}) (who : Player) :
    |reward S who| ≤ 1 := by
  simp [reward]

/-! ## A two-coordinate product expectation -/

/-- Fubini for a function of two distinct coordinates of a finite product
PMF. -/
theorem expect_pmfPi_two_coordinates
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (root : ι → PMF Bool) {first second : ι}
    (hne : first ≠ second) (f : Bool → Bool → ℝ) :
    expect (pmfPi root) (fun action => f (action first) (action second)) =
      expect (root first) (fun a =>
        expect (root second) (fun b => f a b)) := by
  have hpair :
      (pmfPi root).bind
          (fun action => PMF.pure (action first, action second)) =
        (root first).bind (fun a =>
          (root second).bind (fun b => PMF.pure (a, b))) := by
    let g : Bool → (ι → Bool) → PMF (Bool × Bool) :=
      fun a action => PMF.pure (a, action second)
    have hg : Ignores₂ first g := by
      intro a action replacement
      simp [g, Function.update, hne]
    calc
      (pmfPi root).bind
          (fun action => PMF.pure (action first, action second)) =
          (root first).bind (fun a =>
            (pmfPi root).bind (fun action => PMF.pure (a, action second))) := by
        simpa [g] using pmfPi_bind_factor root first g hg
      _ = (root first).bind (fun a =>
          (root second).bind (fun b => PMF.pure (a, b))) := by
        apply congrArg (fun k => (root first).bind k)
        funext a
        simpa using pmfPi_bind_eval root second
          (fun b => PMF.pure (a, b))
  calc
    expect (pmfPi root) (fun action => f (action first) (action second)) =
        expect ((pmfPi root).bind
          (fun action => PMF.pure (action first, action second)))
          (fun pair => f pair.1 pair.2) := by
      rw [expect_bind]
      simp
    _ = expect ((root first).bind (fun a =>
          (root second).bind (fun b => PMF.pure (a, b))))
          (fun pair => f pair.1 pair.2) := by rw [hpair]
    _ = expect (root first) (fun a =>
        expect (root second) (fun b => f a b)) := by
      rw [expect_bind]
      apply congrArg (expect (root first))
      funext a
      rw [expect_bind]
      simp

/-- The expectation of the cyclic bad-event payoff is the negative product
of its two marginal probabilities. -/
theorem expect_pmfPi_badEvent
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (root : ι → PMF Bool) {first second : ι}
    (hne : first ≠ second) :
    expect (pmfPi root) (fun action =>
        if action first = true ∧ action second = false then (-1 : ℝ) else 0) =
      -(root first true).toReal * (root second false).toReal := by
  rw [expect_pmfPi_two_coordinates root hne]
  simp [expect_eq_sum, Fintype.sum_bool]
  ring

/-! ## Exact one-stage coefficients -/

/-- The root payoff is exactly the bad-event indicator. -/
theorem quittingRootPayoff_eq_badEvent
    (action : Player → Bool) (who : Player) :
    quittingRootPayoff reward (0 : Payoff Player) action who =
      if action (next who) = true ∧ action (other who) = false
        then -1 else 0 := by
  by_cases hbad : action (next who) = true ∧ action (other who) = false
  · rw [if_pos hbad]
    have hquit : (quittingQuitters action).Nonempty := by
      refine ⟨next who, ?_⟩
      simpa [quittingQuitters] using hbad.1
    simp [quittingRootPayoff, hquit, reward, quittingQuitters, hbad]
  · rw [if_neg hbad]
    by_cases hquit : (quittingQuitters action).Nonempty
    · simp [quittingRootPayoff, hquit, reward, quittingQuitters, hbad]
    · simp [quittingRootPayoff, hquit]

/-- Quitting now has value `-x_next * (1-x_other)`. -/
theorem quittingStationaryFixedOpponentsQuitValue_eq
    (root : Player → PMF Bool) (who : Player) :
    quittingStationaryFixedOpponentsQuitValue reward root who =
      -(root (next who) true).toReal *
        (root (other who) false).toReal := by
  unfold quittingStationaryFixedOpponentsQuitValue
    quittingFixedOpponentsQuitValue
    quittingRootAbsorbingContribution quittingRootExpectedPayoff
  rw [show (fun action =>
      quittingRootPayoff reward (0 : Payoff Player) action who) =
      (fun action =>
        if action (next who) = true ∧ action (other who) = false
          then (-1 : ℝ) else 0) by
    funext action
    exact quittingRootPayoff_eq_badEvent action who]
  rw [expect_pmfPi_badEvent _ (next_ne_other who)]
  simp [next_ne_self who, other_ne_self who]

/-- The time-indexed form of the same quit-now formula. -/
theorem quittingFixedOpponentsQuitValue_eq
    (roots : ℕ → Player → PMF Bool) (who : Player) (time : ℕ) :
    quittingFixedOpponentsQuitValue reward roots who time =
      -(roots time (next who) true).toReal *
        (roots time (other who) false).toReal := by
  simpa [quittingStationaryFixedOpponentsQuitValue] using
    quittingStationaryFixedOpponentsQuitValue_eq (roots time) who

/-! ## Individual punishment floors -/

/-- Every individual punishment value is exactly `-1`. -/
theorem quittingPunishmentValue_eq_neg_one (who : Player) :
    quittingPunishmentValue reward who = -1 := by
  apply le_antisymm
  · have h := quittingPunishmentValue_le_stationaryUnilateralCap
      reward who (quittingPureSetRoot ({next who} : Finset Player))
    rw [quittingStationaryUnilateralCap_pureSetRoot] at h
    cases who <;> simpa [reward, next, other] using h
  · rw [quittingPunishmentValue_eq_stationaryPunishmentValue]
    haveI : Nonempty (Player → PMF Bool) :=
      ⟨fun _ => PMF.pure false⟩
    exact le_ciInf fun root =>
      le_quittingStationaryUnilateralCap_of_forall_le reward who
        (by norm_num) (fun S => neg_one_le_reward S who) root

/-! ## The cyclic quarter bound -/

private theorem trueMass_nonneg (root : Player → PMF Bool) (who : Player) :
    0 ≤ (root who true).toReal := ENNReal.toReal_nonneg

private theorem trueMass_le_one (root : Player → PMF Bool) (who : Player) :
    (root who true).toReal ≤ 1 := by
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by
    simpa using PMF.coe_le_one (root who) true)

/-- Among the three cyclic products `x_next * (1-x_other)`, one is at most
`1/4`.  The proof chooses a largest marginal. -/
theorem exists_badProbability_le_quarter
    (root : Player → PMF Bool) :
    ∃ who : Player,
      (root (next who) true).toReal *
        (root (other who) false).toReal ≤ (1 / 4 : ℝ) := by
  let xa := (root Player.a true).toReal
  let xb := (root Player.b true).toReal
  let xc := (root Player.c true).toReal
  have hxa0 : 0 ≤ xa := trueMass_nonneg root Player.a
  have hxb0 : 0 ≤ xb := trueMass_nonneg root Player.b
  have hxc0 : 0 ≤ xc := trueMass_nonneg root Player.c
  have hxa1 : xa ≤ 1 := trueMass_le_one root Player.a
  have hxb1 : xb ≤ 1 := trueMass_le_one root Player.b
  have hxc1 : xc ≤ 1 := trueMass_le_one root Player.c
  have hquad : ∀ x : ℝ, x * (1 - x) ≤ (1 / 4 : ℝ) := by
    intro x
    nlinarith [sq_nonneg (x - 1 / 2)]
  by_cases hab : xa ≤ xb
  · by_cases hbc : xb ≤ xc
    · refine ⟨Player.a, ?_⟩
      rw [pmfBool_false_toReal]
      change xb * (1 - xc) ≤ (1 / 4 : ℝ)
      have hmul := mul_le_mul_of_nonneg_right hbc (by linarith : 0 ≤ 1 - xc)
      exact hmul.trans (hquad xc)
    · refine ⟨Player.c, ?_⟩
      rw [pmfBool_false_toReal]
      change xa * (1 - xb) ≤ (1 / 4 : ℝ)
      have hmul := mul_le_mul_of_nonneg_right hab (by linarith : 0 ≤ 1 - xb)
      exact hmul.trans (hquad xb)
  · by_cases hac : xa ≤ xc
    · refine ⟨Player.a, ?_⟩
      rw [pmfBool_false_toReal]
      change xb * (1 - xc) ≤ (1 / 4 : ℝ)
      have hba : xb ≤ xa := le_of_not_ge hab
      have hbc : xb ≤ xc := hba.trans hac
      have hmul := mul_le_mul_of_nonneg_right hbc (by linarith : 0 ≤ 1 - xc)
      exact hmul.trans (hquad xc)
    · refine ⟨Player.b, ?_⟩
      rw [pmfBool_false_toReal]
      change xc * (1 - xa) ≤ (1 / 4 : ℝ)
      have hle : xc ≤ xa := le_of_not_ge hac
      have hmul := mul_le_mul_of_nonneg_right hle (by linarith : 0 ≤ 1 - xa)
      exact hmul.trans (hquad xa)

/-- Against every committed shared plan, some player can secure at least
`-1/4` simply by quitting at the first stage. -/
theorem exists_neg_quarter_le_quittingBestReplyValue
    (profile : (quittingGame reward).BehaviorProfile) :
    ∃ who : Player, (-1 / 4 : ℝ) ≤
      quittingBestReplyValue reward profile who := by
  let roots := quittingProfileLiveRoot reward profile
  obtain ⟨who, hprob⟩ := exists_badProbability_le_quarter (roots 0)
  refine ⟨who, ?_⟩
  have hreply := le_quittingBestReplyValue reward profile who
    (quittingPureTimeBehaviorStrategy reward who (some 0))
  have hpayoff :
      quittingTerminalPayoff reward
          (Function.update profile who
            (quittingPureTimeBehaviorStrategy reward who (some 0))) who =
        -(roots 0 (next who) true).toReal *
          (roots 0 (other who) false).toReal := by
    rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
      quittingRootSequencePureTimeTerminalValue_some_eq]
    simp [quittingLiveLedgerAccum, quittingOpponentSurvivalWeight,
      quittingFixedOpponentsQuitValue_eq]
  rw [hpayoff] at hreply
  linarith

end QuittingSharedThreePlayer

end GameTheory
