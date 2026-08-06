/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingSharedPunishment
import Math.CyclicExposure
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
open QuittingSureSetOwnerRepair

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

/-- The cyclic successor and predecessor maps as a generic exposure system. -/
def cyclicExposureNeighbours : Math.CyclicExposure.Neighbours Player where
  next := next
  prev := other
  prev_next := by
    intro who
    cases who <;> rfl
  next_prev := by
    intro who
    cases who <;> rfl

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
  unfold reward
  split <;> norm_num

@[simp] theorem neg_one_le_reward
    (S : {S : Finset Player // S.Nonempty}) (who : Player) :
    -1 ≤ reward S who := by
  unfold reward
  split <;> norm_num

@[simp] theorem abs_reward_le_one
    (S : {S : Finset Player // S.Nonempty}) (who : Player) :
    |reward S who| ≤ 1 := by
  unfold reward
  split <;> norm_num

/-! ## A two-coordinate product expectation -/


/-- Fubini for a function of two distinct coordinates of a finite product
PMF. -/
theorem expect_pmfPi_two_coordinates
    {ι : Type} [Fintype ι]
    (root : ι → PMF Bool) {first second : ι}
    (hne : first ≠ second) (f : Bool → Bool → ℝ) :
    expect (pmfPi root) (fun action => f (action first) (action second)) =
      expect (root first) (fun a =>
        expect (root second) (fun b => f a b)) := by
  classical
  have hpair :
      (pmfPi root).bind
          (fun action => PMF.pure (action first, action second)) =
        (root first).bind (fun a =>
          (root second).bind (fun b => PMF.pure (a, b))) := by
    let g : Bool → (ι → Bool) → PMF (Bool × Bool) :=
      fun a action => PMF.pure (a, action second)
    have hg : Ignores₂ (A := fun _ : ι => Bool) first g := by
      intro a action replacement
      simp [g, Function.update, hne.symm]
    calc
      (pmfPi root).bind
          (fun action => PMF.pure (action first, action second)) =
          (root first).bind (fun a =>
            (pmfPi root).bind (fun action => PMF.pure (a, action second))) := by
        simpa [g] using
          (pmfPi_bind_factor (A := fun _ : ι => Bool) root first g hg)
      _ = (root first).bind (fun a =>
          (root second).bind (fun b => PMF.pure (a, b))) := by
        apply congrArg (fun k => (root first).bind k)
        funext a
        simpa using
          (pmfPi_bind_eval (A := fun _ : ι => Bool) root second
            (fun b => PMF.pure (a, b)))
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
    {ι : Type} [Fintype ι]
    (root : ι → PMF Bool) {first second : ι}
    (hne : first ≠ second) :
    expect (pmfPi root) (fun action =>
        if action first = true ∧ action second = false then (-1 : ℝ) else 0) =
      -(root first true).toReal * (root second false).toReal := by
  calc
    expect (pmfPi root) (fun action =>
        if action first = true ∧ action second = false then (-1 : ℝ) else 0) =
      expect (root first) (fun a =>
        expect (root second) (fun b =>
          if a = true ∧ b = false then (-1 : ℝ) else 0)) := by
        simpa using
          (expect_pmfPi_two_coordinates root hne
            (fun a b => if a = true ∧ b = false then (-1 : ℝ) else 0))
    _ = -(root first true).toReal * (root second false).toReal := by
      simp [expect_eq_sum]

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
    unfold quittingRootPayoff
    rw [dif_pos hquit]
    unfold reward
    rw [if_pos]
    constructor
    · simpa [quittingQuitters] using hbad.1
    · simpa [quittingQuitters] using hbad.2
  · rw [if_neg hbad]
    by_cases hquit : (quittingQuitters action).Nonempty
    · unfold quittingRootPayoff
      rw [dif_pos hquit]
      unfold reward
      rw [if_neg]
      intro hreward
      apply hbad
      constructor
      · simpa [quittingQuitters] using hreward.1
      · simpa [quittingQuitters] using hreward.2
    · unfold quittingRootPayoff
      rw [dif_neg hquit]
      simp

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
  rw [← quittingStationaryFixedOpponentsQuitValue_apply reward roots who time]
  exact quittingStationaryFixedOpponentsQuitValue_eq (roots time) who

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
`1/4`. This is the three-player specialization of the sharp finite cyclic
exposure theorem. -/
theorem exists_badProbability_le_quarter
    (root : Player → PMF Bool) :
    ∃ who : Player,
      (root (next who) true).toReal *
        (root (other who) false).toReal ≤ (1 / 4 : ℝ) := by
  let x : Player → ℝ := fun who => (root who true).toReal
  obtain ⟨who, hwho⟩ :=
    cyclicExposureNeighbours.exists_exposure_le_quarter x fun player =>
      ⟨trueMass_nonneg root player, trueMass_le_one root player⟩
  refine ⟨who, ?_⟩
  rw [pmfBool_false_toReal]
  simpa [cyclicExposureNeighbours, Math.CyclicExposure.Neighbours.exposure,
    x] using hwho

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
      quittingFixedOpponentsQuitValue_eq, roots]
  rw [hpayoff] at hreply
  linarith

end QuittingSharedThreePlayer

end GameTheory
