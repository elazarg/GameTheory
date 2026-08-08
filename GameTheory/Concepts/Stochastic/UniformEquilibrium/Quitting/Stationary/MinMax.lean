/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Paths.SureExitSet
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalUniformization

/-!
# The quitting min-max is a stationary stopping value

Fix a finite quitting game with reward table `r` and a player `who`.  An
*opponent plan* is an arbitrary behavior profile; `who` replies with an
arbitrary history-dependent behavior strategy.  The **punishment value**

`chi = infimum over plans of (supremum over replies of who's terminal payoff)`

is the min-max the other players can force on `who`.

This module proves that the infimum is already computed by *constant rows*:
product mixed actions repeated at every live stage.  Against a constant row
`y`, writing

* `c(y)` for the probability that every opponent continues,
* `S(y)` for `who`'s expected payoff from quitting now against `y`,
* `H(y)` for `who`'s expected one-stage opponent-absorption reward,

the reply value is the selected stationary cap
`Phi(y) = max (S(y), H(y) / (1 - c(y)))`, already available here as
`quittingStationaryUnilateralCap`.  At the all-continue row this degenerates
to `max (r_who({who}), 0)` because `H = 0` and the Lean convention
`x / 0 = 0` selects the never-quit payoff `0`.

## Main results

* `quittingBestReplyValue_stationary` — the exact reply value against a
  constant row is `Phi(y)`, with no contraction hypothesis
* `quittingPunishmentValue_le_stationaryUnilateralCap` and
  `quittingPunishmentValue_le_stationaryPunishmentValue` — the upper leg
* `quittingStationaryPunishmentValue_le_quittingBestReplyValue` and
  `quittingStationaryPunishmentValue_le_quittingPunishmentValue` — the lower
  leg: *no* plan, however history dependent, punishes below `inf_y Phi(y)`
* `quittingPunishmentValue_eq_stationaryPunishmentValue` — the two values
  agree
* `quittingRootSequenceHazardTerminalValue_const_le_cap` and
  `quittingStationaryPunishmentValue_le_of_forall_hazard_le` — both legs in
  the root-sequence shape used by punishment-plan packages

Exact attainment of the infimum can fail, so nothing is claimed about it.

## Method

The upper leg is the landed stationary Snell cap plus the degenerate
all-continue row.  The lower leg is a ledger argument along the unique live
path.  A plan presents a row `y_t` at each live stage; write `beta_t` for the
opponents' survival product and `A_t` for the accumulated absorption ledger.
The quantity `A_t + beta_t * V` (with `V` the constant-row infimum) is
nondecreasing exactly while the current row favours the absorption branch of
`Phi`, and quitting at the first stage that favours the stop branch already
pays at least `V`.  If no stage ever favours the stop branch, the never-quit
reply collects the whole ledger; when the opponents' survival does not decay
the rows must converge to the all-continue row, whose stop branch pays
`r_who({who}) >= V`, and quitting late is then within any prescribed error.

The characterization is original to this development; the quitting-game
model is that of Solan and Vieille, *Quitting games*, Israel J. Math. 119
(2001).
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability Math.PMFProduct
open QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The punishment vocabulary -/

/-- Player `who`'s best-reply value against a fixed opponent plan: the
supremum of the terminal payoffs of all history-dependent behavior
deviations. -/
def quittingBestReplyValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) : ℝ :=
  ⨆ deviation : (quittingGame reward).BehaviorStrategy who,
    quittingTerminalPayoff reward
      (Function.update profile who deviation) who

/-- The **punishment value** (min-max) of player `who` at the active state:
the infimum over all opponent plans of `who`'s best-reply value.  Only the
opponents' coordinates of the plan matter, since `who`'s own coordinate is
overwritten by the reply. -/
def quittingPunishmentValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) : ℝ :=
  ⨅ profile : (quittingGame reward).BehaviorProfile,
    quittingBestReplyValue reward profile who

/-- The **constant-row punishment value**: the infimum of the selected
stationary caps `Phi(y)` over all product rows `y`. -/
def quittingStationaryPunishmentValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) : ℝ :=
  ⨅ root : ι → PMF Bool, quittingStationaryUnilateralCap reward root who

/-- `Phi(y)` written out: the better of quitting now against `y` and riding
the opponents' absorption forever. -/
theorem quittingStationaryUnilateralCap_eq_max_div
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) :
    quittingStationaryUnilateralCap reward root who =
      max (quittingStationaryFixedOpponentsQuitValue reward root who)
        (quittingStationaryFixedOpponentsContinueReward reward root who /
          (1 - quittingStationaryFixedOpponentsContinueMass root who)) :=
  rfl

/-- The stationary coefficients of a root sequence at one time are the
constant-row coefficients of that time's row. -/
@[simp] theorem quittingStationaryFixedOpponentsQuitValue_apply
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (time : ℕ) :
    quittingStationaryFixedOpponentsQuitValue reward (roots time) who =
      quittingFixedOpponentsQuitValue reward roots who time :=
  rfl

@[simp] theorem quittingStationaryFixedOpponentsContinueReward_apply
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (time : ℕ) :
    quittingStationaryFixedOpponentsContinueReward reward (roots time) who =
      quittingFixedOpponentsContinueReward reward roots who time :=
  rfl

@[simp] theorem quittingStationaryFixedOpponentsContinueMass_apply
    (roots : ℕ → ι → PMF Bool) (who : ι) (time : ℕ) :
    quittingStationaryFixedOpponentsContinueMass (roots time) who =
      quittingFixedOpponentsContinueMass roots who time :=
  rfl

/-! ## Elementary bounds -/

/-- A uniform lower bound on the table's `who` coordinate is a lower bound on
every constant-row cap.  Only the quit branch is used, so no contraction
hypothesis appears. -/
theorem le_quittingStationaryUnilateralCap_of_forall_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι)
    {B : ℝ} (hB : B ≤ 0) (hreward : ∀ S, B ≤ reward S who)
    (root : ι → PMF Bool) :
    B ≤ quittingStationaryUnilateralCap reward root who := by
  refine le_trans ?_ (le_max_left _ _)
  change B ≤ quittingRootAbsorbingContribution reward
    (Function.update root who (PMF.pure true)) who
  unfold quittingRootAbsorbingContribution quittingRootExpectedPayoff
  haveI : Finite (ι → Bool) := inferInstanceAs (Finite (ι → Bool))
  calc B = expect (pmfPi (Function.update root who (PMF.pure true)))
        (fun _ => B) := (expect_const _ B).symm
    _ ≤ _ := by
        apply expect_mono
        intro action
        unfold quittingRootPayoff
        by_cases hquit : (quittingQuitters action).Nonempty
        · rw [dif_pos hquit]
          exact hreward _
        · rw [dif_neg hquit]
          simpa using hB

/-- Every constant-row cap is above the negated canonical reward bound. -/
theorem neg_quittingRewardBound_le_quittingStationaryUnilateralCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι)
    (root : ι → PMF Bool) :
    -quittingRewardBound reward ≤
      quittingStationaryUnilateralCap reward root who := by
  refine le_quittingStationaryUnilateralCap_of_forall_le reward who ?_ ?_ root
  · simpa using quittingRewardBound_nonneg reward
  · intro S
    exact neg_le_of_abs_le (abs_reward_le_quittingRewardBound reward S who)

/-- The constant-row caps are bounded below, so their infimum is genuine. -/
theorem bddBelow_range_quittingStationaryUnilateralCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    BddBelow (Set.range fun root : ι → PMF Bool =>
      quittingStationaryUnilateralCap reward root who) := by
  refine ⟨-quittingRewardBound reward, ?_⟩
  rintro _ ⟨root, rfl⟩
  exact neg_quittingRewardBound_le_quittingStationaryUnilateralCap
    reward who root

/-- The constant-row punishment value is below every constant-row cap. -/
theorem quittingStationaryPunishmentValue_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι)
    (root : ι → PMF Bool) :
    quittingStationaryPunishmentValue reward who ≤
      quittingStationaryUnilateralCap reward root who :=
  ciInf_le (bddBelow_range_quittingStationaryUnilateralCap reward who) root

/-! ## Best-reply values are attained suprema -/

/-- Every deviation payoff is below the best-reply value. -/
theorem le_quittingBestReplyValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (deviation : (quittingGame reward).BehaviorStrategy who) :
    quittingTerminalPayoff reward
        (Function.update profile who deviation) who ≤
      quittingBestReplyValue reward profile who :=
  le_ciSup (bddAbove_range_quittingTerminalPayoff_update reward profile who
    (quittingRewardBound_nonneg reward)
    (abs_reward_le_quittingRewardBound reward)) deviation

/-- A uniform bound on all deviation payoffs bounds the best-reply value. -/
theorem quittingBestReplyValue_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    {bound : ℝ}
    (hbound : ∀ deviation : (quittingGame reward).BehaviorStrategy who,
      quittingTerminalPayoff reward
        (Function.update profile who deviation) who ≤ bound) :
    quittingBestReplyValue reward profile who ≤ bound := by
  haveI : Nonempty ((quittingGame reward).BehaviorStrategy who) :=
    ⟨quittingAlwaysContinueStrategy reward who⟩
  exact ciSup_le hbound

/-- Best-reply values are bounded below by the never-quit reply. -/
theorem neg_quittingRewardBound_le_quittingBestReplyValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    -quittingRewardBound reward ≤
      quittingBestReplyValue reward profile who := by
  refine le_trans ?_ (le_quittingBestReplyValue reward profile who
    (quittingAlwaysContinueStrategy reward who))
  exact neg_le_of_abs_le (abs_quittingTerminalPayoff_le reward _ who
    (quittingRewardBound_nonneg reward)
    (abs_reward_le_quittingRewardBound reward))

/-- The plan-indexed best-reply values are bounded below, so the punishment
value is a genuine infimum. -/
theorem bddBelow_range_quittingBestReplyValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    BddBelow (Set.range fun profile : (quittingGame reward).BehaviorProfile =>
      quittingBestReplyValue reward profile who) := by
  refine ⟨-quittingRewardBound reward, ?_⟩
  rintro _ ⟨profile, rfl⟩
  exact neg_quittingRewardBound_le_quittingBestReplyValue reward profile who

/-- The punishment value is below every plan's best-reply value. -/
theorem quittingPunishmentValue_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingPunishmentValue reward who ≤
      quittingBestReplyValue reward profile who :=
  ciInf_le (bddBelow_range_quittingBestReplyValue reward who) profile

/-! ## Rows agreeing off the deviator -/

/-- The constant-row cap only sees the opponents' coordinates. -/
theorem quittingStationaryUnilateralCap_congr_of_opponents
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {first second : ι → PMF Bool} (who : ι)
    (hagree : ∀ player, player ≠ who → first player = second player) :
    quittingStationaryUnilateralCap reward first who =
      quittingStationaryUnilateralCap reward second who := by
  have hupdate : ∀ marginal : PMF Bool,
      Function.update first who marginal =
        Function.update second who marginal := by
    intro marginal
    funext player
    by_cases hplayer : player = who
    · subst player; simp
    · simp [Function.update_of_ne hplayer, hagree player hplayer]
  unfold quittingStationaryUnilateralCap quittingStationaryFixedOpponentsQuitValue
    quittingStationaryFixedOpponentsContinueReward
    quittingStationaryFixedOpponentsContinueMass
    quittingFixedOpponentsQuitValue quittingFixedOpponentsContinueReward
    quittingFixedOpponentsContinueMass
  rw [hupdate (PMF.pure true), hupdate (PMF.pure false)]

/-- A unilateral deviation only sees the opponents' coordinates. -/
theorem update_quittingStationaryProfile_congr_of_opponents
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {first second : ι → PMF Bool} (who : ι)
    (hagree : ∀ player, player ≠ who → first player = second player)
    (deviation : (quittingGame reward).BehaviorStrategy who) :
    Function.update (quittingStationaryProfile reward first) who deviation =
      Function.update (quittingStationaryProfile reward second) who
        deviation := by
  funext player time history
  by_cases hplayer : player = who
  · subst player; simp
  · simp [Function.update_of_ne hplayer, quittingStationaryProfile,
      StochasticGame.stationaryBehaviorProfile, hagree player hplayer]

omit [DecidableEq ι] in
/-- A product root with all-continue mass one has every marginal pure
Continue. -/
theorem eq_pure_false_of_quittingStationaryContinueMass_eq_one
    {root : ι → PMF Bool}
    (hmass : quittingStationaryContinueMass root = 1) (player : ι) :
    root player = PMF.pure false := by
  classical
  have hprod : ∏ index : ι, (root index false).toReal = 1 := by
    rw [← ENNReal.toReal_prod]
    simpa [quittingStationaryContinueMass, quittingAllContinueAction]
      using hmass
  have hnonneg : ∀ index : ι, 0 ≤ (root index false).toReal :=
    fun _ => ENNReal.toReal_nonneg
  have hle : ∀ index : ι, (root index false).toReal ≤ 1 := by
    intro index
    rw [← ENNReal.toReal_one,
      ENNReal.toReal_le_toReal (PMF.apply_ne_top _ _) (by simp)]
    exact PMF.coe_le_one _ _
  have hsplit : ∏ index : ι, (root index false).toReal =
      (root player false).toReal *
        ∏ index ∈ Finset.univ.erase player, (root index false).toReal :=
    (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ player)).symm
  have hrest : ∏ index ∈ Finset.univ.erase player,
      (root index false).toReal ≤ 1 :=
    Finset.prod_le_one (fun index _ => hnonneg index)
      (fun index _ => hle index)
  have hfalse : (root player false).toReal = 1 := by
    nlinarith [hnonneg player, hle player,
      Finset.prod_nonneg (fun index (_ : index ∈ Finset.univ.erase player) =>
        hnonneg index)]
  have htrue : (root player true).toReal = 0 := by
    have hsum := Math.ProbabilityMassFunction.sum_coe_fintype (root player)
    have hsumReal : (root player true).toReal + (root player false).toReal
        = 1 := by
      have hne : (root player true) + (root player false) ≠ ⊤ := by
        rw [Fintype.sum_bool] at hsum
        rw [hsum]
        simp
      rw [← ENNReal.toReal_add (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)]
      rw [Fintype.sum_bool] at hsum
      rw [hsum]
      simp
    linarith
  have htrueZero : root player true = 0 := by
    rcases (ENNReal.toReal_eq_zero_iff (root player true)).mp htrue with
      hzero | htop
    · exact hzero
    · exact absurd htop (PMF.apply_ne_top _ _)
  have hfalseOne : root player false = 1 := by
    have hsum := Math.ProbabilityMassFunction.sum_coe_fintype (root player)
    rw [Fintype.sum_bool, htrueZero, zero_add] at hsum
    exact hsum
  ext action
  cases action <;> simp [PMF.pure_apply, htrueZero, hfalseOne]

/-- The opponents' one-stage continue mass is a probability. -/
theorem quittingStationaryFixedOpponentsContinueMass_le_one
    (root : ι → PMF Bool) (who : ι) :
    quittingStationaryFixedOpponentsContinueMass root who ≤ 1 :=
  quittingStationaryContinueMass_le_one
    (Function.update root who (PMF.pure false))

/-- A row whose opponents surely continue agrees with the empty exit root
away from the deviator. -/
theorem eq_pureSetRoot_empty_of_fixedOpponentsContinueMass_eq_one
    {root : ι → PMF Bool} {who : ι}
    (hmass : quittingStationaryFixedOpponentsContinueMass root who = 1)
    (player : ι) (hplayer : player ≠ who) :
    root player = quittingPureSetRoot (∅ : Finset ι) player := by
  have hupdate : quittingStationaryContinueMass
      (Function.update root who (PMF.pure false)) = 1 := hmass
  have hpure := eq_pure_false_of_quittingStationaryContinueMass_eq_one
    hupdate player
  rw [Function.update_of_ne hplayer] at hpure
  simp [hpure, quittingPureSetRoot_empty]

/-! ## The reply value against a constant row -/

/-- **The exact reply value against a constant row, degenerate case.**  When
the opponents never quit, the deviator's only alternatives are its own solo
exit and never quitting. -/
theorem quittingStationaryUnilateralCap_of_fixedOpponentsContinueMass_eq_one
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {root : ι → PMF Bool} {who : ι}
    (hmass : quittingStationaryFixedOpponentsContinueMass root who = 1) :
    quittingStationaryUnilateralCap reward root who =
      max (quittingSetReward reward ({who} : Finset ι) who) 0 := by
  rw [quittingStationaryUnilateralCap_congr_of_opponents reward who
      (eq_pureSetRoot_empty_of_fixedOpponentsContinueMass_eq_one hmass),
    quittingStationaryUnilateralCap_pureSetRoot]
  simp

/-- **Constant rows cap every reply.**  Against a row played forever, no
history-dependent randomized reply beats the selected stationary cap.  Unlike
the landed Snell-cap bound this carries no contraction hypothesis: the
degenerate all-continue row is handled by the empty exit set. -/
theorem quittingTerminalPayoff_update_stationary_le_cap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι)
    (deviation : (quittingGame reward).BehaviorStrategy who) :
    quittingTerminalPayoff reward
        (Function.update (quittingStationaryProfile reward root) who
          deviation) who ≤
      quittingStationaryUnilateralCap reward root who := by
  by_cases heq : quittingStationaryFixedOpponentsContinueMass root who = 1
  case neg =>
    exact quittingTerminalPayoff_update_stationary_le_unilateralCap
      reward root who deviation
      (lt_of_le_of_ne
        (quittingStationaryFixedOpponentsContinueMass_le_one root who) heq)
  case pos =>
    have hagree := eq_pureSetRoot_empty_of_fixedOpponentsContinueMass_eq_one
      (root := root) (who := who) heq
    rw [update_quittingStationaryProfile_congr_of_opponents reward who hagree
        deviation,
      quittingStationaryUnilateralCap_congr_of_opponents reward who hagree,
      quittingStationaryUnilateralCap_pureSetRoot]
    exact quittingTerminalPayoff_update_pureSetRoot_le reward ∅ who deviation

/-- Against a pure exit root the cap is attained by a membership toggle. -/
theorem exists_quittingTerminalPayoff_update_pureSetRoot_eq_cap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (S : Finset ι) (who : ι) :
    ∃ deviation : (quittingGame reward).BehaviorStrategy who,
      quittingTerminalPayoff reward
          (Function.update
            (quittingStationaryProfile reward (quittingPureSetRoot S)) who
            deviation) who =
        quittingStationaryUnilateralCap reward (quittingPureSetRoot S) who := by
  rw [quittingStationaryUnilateralCap_pureSetRoot]
  rcases max_choice (quittingSetReward reward (insert who S) who)
      (quittingSetReward reward (S.erase who) who) with hmax | hmax
  · exact ⟨quittingPureTimeBehaviorStrategy reward who (some 0), by
      rw [quittingTerminalPayoff_update_pureSetRoot_quitNow, hmax]⟩
  · exact ⟨quittingAlwaysContinueStrategy reward who, by
      rw [quittingTerminalPayoff_update_pureSetRoot_alwaysContinue, hmax]⟩

/-- The constant-row cap is attained by an actual reply, at every row. -/
theorem exists_quittingTerminalPayoff_update_stationary_eq_cap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) :
    ∃ deviation : (quittingGame reward).BehaviorStrategy who,
      quittingTerminalPayoff reward
          (Function.update (quittingStationaryProfile reward root) who
            deviation) who =
        quittingStationaryUnilateralCap reward root who := by
  by_cases heq : quittingStationaryFixedOpponentsContinueMass root who = 1
  case neg =>
    obtain ⟨choice, hchoice⟩ :=
      exists_pureTimeBehaviorStrategy_terminalPayoff_eq_unilateralCap
        reward root who
        (lt_of_le_of_ne
          (quittingStationaryFixedOpponentsContinueMass_le_one root who) heq)
    exact ⟨quittingPureTimeBehaviorStrategy reward who choice, hchoice⟩
  case pos =>
    have hagree := eq_pureSetRoot_empty_of_fixedOpponentsContinueMass_eq_one
      (root := root) (who := who) heq
    obtain ⟨deviation, hdeviation⟩ :=
      exists_quittingTerminalPayoff_update_pureSetRoot_eq_cap reward ∅ who
    refine ⟨deviation, ?_⟩
    rw [update_quittingStationaryProfile_congr_of_opponents reward who hagree
        deviation,
      quittingStationaryUnilateralCap_congr_of_opponents reward who hagree]
    exact hdeviation

/-- **The exact reply value against a constant row.**  Player `who`'s
best-reply value against the row `root` played forever is exactly the
selected stationary cap. -/
theorem quittingBestReplyValue_stationary
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) :
    quittingBestReplyValue reward (quittingStationaryProfile reward root)
        who =
      quittingStationaryUnilateralCap reward root who := by
  refine le_antisymm (quittingBestReplyValue_le reward _ who ?_) ?_
  · exact fun deviation =>
      quittingTerminalPayoff_update_stationary_le_cap reward root who deviation
  · obtain ⟨deviation, hdeviation⟩ :=
      exists_quittingTerminalPayoff_update_stationary_eq_cap reward root who
    rw [← hdeviation]
    exact le_quittingBestReplyValue reward _ who deviation

/-! ## The upper leg -/

/-- **Upper leg, pointwise.**  Constant rows already punish `who` down to
their own selected cap. -/
theorem quittingPunishmentValue_le_stationaryUnilateralCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι)
    (root : ι → PMF Bool) :
    quittingPunishmentValue reward who ≤
      quittingStationaryUnilateralCap reward root who := by
  rw [← quittingBestReplyValue_stationary reward root who]
  exact quittingPunishmentValue_le reward who _

/-- **Upper leg.**  The punishment value is at most the constant-row
punishment value. -/
theorem quittingPunishmentValue_le_stationaryPunishmentValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    quittingPunishmentValue reward who ≤
      quittingStationaryPunishmentValue reward who := by
  haveI : Nonempty (ι → PMF Bool) := ⟨fun _ => PMF.pure false⟩
  exact le_ciInf fun root =>
    quittingPunishmentValue_le_stationaryUnilateralCap reward who root

/-! ## The live ledger

Along the unique live path a plan presents a row at each stage.  The
*ledger* accumulates the expected opponent-absorption reward collected while
the deviator continues; the survival weight is the probability that the
opponents have not yet absorbed. -/

/-- The absorption reward accumulated over `fuel` live stages from `start`,
each stage weighted by the opponents' survival up to that stage. -/
def quittingLiveLedgerAccum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start fuel : ℕ) : ℝ :=
  ∑ offset ∈ Finset.range fuel,
    quittingOpponentSurvivalWeight roots who start offset *
      quittingFixedOpponentsContinueReward reward roots who (start + offset)

@[simp] theorem quittingLiveLedgerAccum_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start : ℕ) :
    quittingLiveLedgerAccum reward roots who start 0 = 0 := by
  simp [quittingLiveLedgerAccum]

theorem quittingFixedOpponentsContinueMass_nonneg
    (roots : ℕ → ι → PMF Bool) (who : ι) (time : ℕ) :
    0 ≤ quittingFixedOpponentsContinueMass roots who time :=
  quittingStationaryContinueMass_nonneg _

theorem quittingFixedOpponentsContinueMass_le_one
    (roots : ℕ → ι → PMF Bool) (who : ι) (time : ℕ) :
    quittingFixedOpponentsContinueMass roots who time ≤ 1 :=
  quittingStationaryContinueMass_le_one _

theorem quittingOpponentSurvivalWeight_zero_succ
    (roots : ℕ → ι → PMF Bool) (who : ι) (time : ℕ) :
    quittingOpponentSurvivalWeight roots who 0 (time + 1) =
      quittingOpponentSurvivalWeight roots who 0 time *
        quittingFixedOpponentsContinueMass roots who time := by
  simpa using quittingOpponentSurvivalWeight_succ roots who 0 time

theorem quittingLiveLedgerAccum_zero_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (time : ℕ) :
    quittingLiveLedgerAccum reward roots who 0 (time + 1) =
      quittingLiveLedgerAccum reward roots who 0 time +
        quittingOpponentSurvivalWeight roots who 0 time *
          quittingFixedOpponentsContinueReward reward roots who time := by
  simp [quittingLiveLedgerAccum, Finset.sum_range_succ]

/-- Peeling the first live stage off a survival weight. -/
theorem quittingOpponentSurvivalWeight_shift
    (roots : ℕ → ι → PMF Bool) (who : ι) (start fuel : ℕ) :
    quittingOpponentSurvivalWeight roots who start (fuel + 1) =
      quittingFixedOpponentsContinueMass roots who start *
        quittingOpponentSurvivalWeight roots who (start + 1) fuel := by
  unfold quittingOpponentSurvivalWeight
  rw [Finset.prod_range_succ', Nat.add_zero, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun offset _ => ?_
  rw [show start + (offset + 1) = start + 1 + offset from by omega]

/-- Peeling the first live stage off a ledger. -/
theorem quittingLiveLedgerAccum_shift
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start fuel : ℕ) :
    quittingLiveLedgerAccum reward roots who start (fuel + 1) =
      quittingFixedOpponentsContinueReward reward roots who start +
        quittingFixedOpponentsContinueMass roots who start *
          quittingLiveLedgerAccum reward roots who (start + 1) fuel := by
  unfold quittingLiveLedgerAccum
  rw [Finset.sum_range_succ']
  have hzero : quittingOpponentSurvivalWeight roots who start 0 *
      quittingFixedOpponentsContinueReward reward roots who (start + 0) =
      quittingFixedOpponentsContinueReward reward roots who start := by
    simp [quittingOpponentSurvivalWeight]
  rw [hzero, Finset.mul_sum, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun offset _ => ?_
  rw [quittingOpponentSurvivalWeight_shift,
    show start + (offset + 1) = start + 1 + offset from by omega]
  ring

/-- The finite never-quit payoff is exactly the ledger. -/
theorem quittingFiniteRootPayoff_never_eq_ledgerAccum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) :
    ∀ start fuel,
      quittingFiniteRootPayoff reward roots who
          (quittingPureTimeHazard none) start fuel =
        quittingLiveLedgerAccum reward roots who start fuel := by
  intro start fuel
  induction fuel generalizing start with
  | zero => simp [quittingFiniteRootPayoff]
  | succ fuel ih =>
      rw [quittingFiniteRootPayoff_eq_hazardValue, quittingFiniteHazardValue]
      simp only [quittingPureTimeHazard_none, PMF.pure_apply,
        if_neg (by decide : (true : Bool) ≠ false), ENNReal.toReal_zero,
        if_true, ENNReal.toReal_one, zero_mul, one_mul, zero_add]
      rw [← quittingFiniteRootPayoff_eq_hazardValue, ih (start + 1),
        quittingLiveLedgerAccum_shift]

/-- The never-quit reply collects the whole ledger in the limit. -/
theorem tendsto_quittingLiveLedgerAccum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) :
    Tendsto (fun fuel => quittingLiveLedgerAccum reward roots who 0 fuel)
      atTop (nhds (quittingRootSequencePureTimeTerminalValue reward roots who
        none 0)) := by
  have hlimit := tendsto_quittingFiniteRootPayoff_terminal reward roots who
    (quittingPureTimeHazard none) 0
  simpa [quittingFiniteRootPayoff_never_eq_ledgerAccum,
    quittingRootSequencePureTimeTerminalValue,
    quittingRootSequenceHazardTerminalValue,
    quittingRootSequenceTerminalValue] using hlimit

/-- The payoff of quitting at a deterministic date: the ledger accumulated
before that date plus the surviving stake times the quit value there. -/
theorem quittingRootSequencePureTimeTerminalValue_some_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) :
    ∀ start fuel,
      quittingRootSequencePureTimeTerminalValue reward roots who
          (some (start + fuel)) start =
        quittingLiveLedgerAccum reward roots who start fuel +
          quittingOpponentSurvivalWeight roots who start fuel *
            quittingFixedOpponentsQuitValue reward roots who
              (start + fuel) := by
  intro start fuel
  induction fuel generalizing start with
  | zero =>
      unfold quittingRootSequencePureTimeTerminalValue
      rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman]
      simp [quittingOpponentSurvivalWeight]
  | succ fuel ih =>
      unfold quittingRootSequencePureTimeTerminalValue
      rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman]
      have hne : start ≠ start + (fuel + 1) := by omega
      rw [quittingPureTimeHazard_some_of_ne hne]
      simp only [PMF.pure_apply,
        if_neg (by decide : (true : Bool) ≠ false), ENNReal.toReal_zero,
        if_true, ENNReal.toReal_one, zero_mul, one_mul, zero_add]
      have htime : start + (fuel + 1) = (start + 1) + fuel := by omega
      change
        quittingFixedOpponentsContinueReward reward roots who start +
            quittingFixedOpponentsContinueMass roots who start *
              quittingRootSequencePureTimeTerminalValue reward
                roots who (some (start + (fuel + 1))) (start + 1) = _
      rw [htime, ih (start + 1), quittingLiveLedgerAccum_shift,
        quittingOpponentSurvivalWeight_shift]
      ring

/-- The payoff of quitting at date `time`, read from date zero. -/
theorem quittingRootSequencePureTimeTerminalValue_some_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (time : ℕ) :
    quittingRootSequencePureTimeTerminalValue reward roots who (some time) 0 =
      quittingLiveLedgerAccum reward roots who 0 time +
        quittingOpponentSurvivalWeight roots who 0 time *
          quittingFixedOpponentsQuitValue reward roots who time := by
  simpa using
    quittingRootSequencePureTimeTerminalValue_some_add reward roots who 0 time

/-- **The ledger inequality.**  While every stage so far favours riding the
opponents' absorption, the accumulated ledger plus the surviving stake stays
above the target. -/
theorem le_quittingLiveLedgerAccum_add_survival_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (target : ℝ) :
    ∀ fuel : ℕ,
      (∀ time < fuel,
        (1 - quittingFixedOpponentsContinueMass roots who time) * target ≤
          quittingFixedOpponentsContinueReward reward roots who time) →
      target ≤ quittingLiveLedgerAccum reward roots who 0 fuel +
        quittingOpponentSurvivalWeight roots who 0 fuel * target := by
  intro fuel
  induction fuel with
  | zero =>
      intro _
      simp [quittingOpponentSurvivalWeight]
  | succ fuel ih =>
      intro hride
      have hprev := ih fun time htime => hride time (by omega)
      have hstep := hride fuel (by omega)
      have hnonneg := quittingOpponentSurvivalWeight_nonneg roots who 0 fuel
      have hscaled := mul_le_mul_of_nonneg_left hstep hnonneg
      have hexpand : quittingOpponentSurvivalWeight roots who 0 fuel *
          ((1 - quittingFixedOpponentsContinueMass roots who fuel) * target) =
          quittingOpponentSurvivalWeight roots who 0 fuel * target -
            quittingOpponentSurvivalWeight roots who 0 fuel *
              quittingFixedOpponentsContinueMass roots who fuel * target := by
        ring
      rw [hexpand] at hscaled
      rw [quittingLiveLedgerAccum_zero_succ,
        quittingOpponentSurvivalWeight_zero_succ]
      linarith

/-! ## Two facts about rows close to the all-continue row -/

/-- A row whose opponents surely continue contributes no absorption. -/
theorem quittingStationaryFixedOpponentsContinueReward_eq_zero_of_mass_eq_one
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {root : ι → PMF Bool} {who : ι}
    (hmass : quittingStationaryFixedOpponentsContinueMass root who = 1) :
    quittingStationaryFixedOpponentsContinueReward reward root who = 0 := by
  have hall : Function.update root who (PMF.pure false) =
      fun _ : ι => PMF.pure false := by
    funext player
    exact eq_pure_false_of_quittingStationaryContinueMass_eq_one hmass player
  change quittingRootAbsorbingContribution reward
    (Function.update root who (PMF.pure false)) who = 0
  rw [hall]
  unfold quittingRootAbsorbingContribution quittingRootExpectedPayoff
  change expect (pmfPi fun _ : ι => PMF.pure false)
    (fun action => quittingRootPayoff reward (0 : Payoff ι) action who) = 0
  rw [pmfPi_pure, expect_pure]
  simp [quittingRootPayoff, quittingQuitters]

/-- **Quitting now is continuous at the all-continue row.**  The value of
quitting now against a row is within `2 * bound` times the one-stage opponent
absorption probability of the deviator's own solo exit reward. -/
theorem quittingSetReward_singleton_sub_le_fixedOpponentsQuitValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) :
    quittingSetReward reward ({who} : Finset ι) who -
        2 * quittingRewardBound reward *
          (1 - quittingStationaryFixedOpponentsContinueMass root who) ≤
      quittingStationaryFixedOpponentsQuitValue reward root who := by
  classical
  haveI : Finite (ι → Bool) := inferInstanceAs (Finite (ι → Bool))
  set bound := quittingRewardBound reward with hbound
  set solo := quittingSetReward reward ({who} : Finset ι) who with hsoloDef
  set act : ι → Bool := quittingSetAction ({who} : Finset ι) with hactDef
  set law := pmfPi (Function.update root who (PMF.pure true)) with hlawDef
  have hbound0 : 0 ≤ bound := quittingRewardBound_nonneg reward
  have hquitters : quittingQuitters act = ({who} : Finset ι) := by
    rw [hactDef, quittingQuitters_setAction]
  have hactNonempty : (quittingQuitters act).Nonempty := by
    rw [hquitters]; exact Finset.singleton_nonempty who
  have hsoloBound : |solo| ≤ bound := by
    rw [hsoloDef, quittingSetReward_of_nonempty reward
      (Finset.singleton_nonempty who)]
    exact abs_reward_le_quittingRewardBound reward _ who
  have hpayoffBound : ∀ action : ι → Bool,
      |quittingRootPayoff reward (0 : Payoff ι) action who| ≤ bound := by
    intro action
    unfold quittingRootPayoff
    by_cases hquit : (quittingQuitters action).Nonempty
    · rw [dif_pos hquit]
      exact abs_reward_le_quittingRewardBound reward _ who
    · rw [dif_neg hquit]
      simpa using hbound0
  have hmass : (law act).toReal =
      quittingStationaryFixedOpponentsContinueMass root who := by
    change (law act).toReal =
      quittingStationaryContinueMass (Function.update root who (PMF.pure false))
    unfold quittingStationaryContinueMass
    congr 1
    rw [hlawDef]
    simp only [pmfPi_apply]
    refine Finset.prod_congr rfl fun index _ => ?_
    by_cases hindex : index = who
    · subst index
      simp [hactDef, quittingSetAction, quittingAllContinueAction]
    · simp [hactDef, quittingSetAction, hindex, quittingAllContinueAction]
  have hpoint : ∀ action : ι → Bool,
      solo - quittingRootPayoff reward (0 : Payoff ι) action who ≤
        2 * bound * (1 - if action = act then (1 : ℝ) else 0) := by
    intro action
    by_cases haction : action = act
    · subst action
      rw [if_pos rfl]
      have hvalue : quittingRootPayoff reward (0 : Payoff ι) act who = solo := by
        unfold quittingRootPayoff
        rw [dif_pos hactNonempty, hsoloDef,
          quittingSetReward_of_nonempty reward (Finset.singleton_nonempty who)]
        congr 1
        exact Subtype.ext hquitters
      rw [hvalue]
      simp
    · rw [if_neg haction]
      have h1 := abs_le.mp hsoloBound
      have h2 := abs_le.mp (hpayoffBound action)
      simp only [sub_zero, mul_one]
      linarith [h1.2, h2.1]
  have hsplit : solo - quittingStationaryFixedOpponentsQuitValue reward root who =
      expect law (fun action =>
        solo - quittingRootPayoff reward (0 : Payoff ι) action who) := by
    rw [expect_sub, expect_const]
    rfl
  have hcompare : expect law (fun action =>
        solo - quittingRootPayoff reward (0 : Payoff ι) action who) ≤
      expect law (fun action =>
        2 * bound * (1 - if action = act then (1 : ℝ) else 0)) :=
    expect_mono _ _ _ hpoint
  have hvalue : expect law (fun action =>
        2 * bound * (1 - if action = act then (1 : ℝ) else 0)) =
      2 * bound * (1 - (law act).toReal) := by
    rw [expect_const_mul]
    congr 1
    rw [expect_sub, expect_const, ← apply_toReal_eq_expect_indicator]
  rw [hvalue, hmass] at hcompare
  linarith [hsplit ▸ hcompare]

/-! ## The lower leg -/

/-- **No row sequence punishes below the constant-row value.**  If every
deterministic stopping reply against a live-path row sequence pays at most
`bound`, then `bound` is already at least the constant-row punishment value.

This is the heart of the theorem.  The proof splits on whether some live
stage favours the stop branch of `Phi`.  If one does, the first such stage is
reached with the ledger already worth the target, and quitting there pays at
least the target.  If none does, the ledger inequality holds at every stage;
the never-quit reply then collects at least the target unless the opponents'
survival stalls at a positive level, in which case the rows converge to the
all-continue row and quitting late is within any prescribed error. -/
theorem quittingStationaryPunishmentValue_le_of_forall_pureTime_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) {bound : ℝ}
    (hpure : ∀ quitTime : Option ℕ,
      quittingRootSequencePureTimeTerminalValue reward roots who quitTime 0 ≤
        bound) :
    quittingStationaryPunishmentValue reward who ≤ bound := by
  classical
  set target := quittingStationaryPunishmentValue reward who with htarget
  set mass : ℕ → ℝ := fun time =>
    quittingFixedOpponentsContinueMass roots who time with hmassDef
  set absorb : ℕ → ℝ := fun time =>
    quittingFixedOpponentsContinueReward reward roots who time with habsorbDef
  set quitValue : ℕ → ℝ := fun time =>
    quittingFixedOpponentsQuitValue reward roots who time with hquitDef
  set survival : ℕ → ℝ := fun time =>
    quittingOpponentSurvivalWeight roots who 0 time with hsurvivalDef
  set ledger : ℕ → ℝ := fun time =>
    quittingLiveLedgerAccum reward roots who 0 time with hledgerDef
  have hmass0 : ∀ time, 0 ≤ mass time := fun time =>
    quittingFixedOpponentsContinueMass_nonneg roots who time
  have hmass1 : ∀ time, mass time ≤ 1 := fun time =>
    quittingFixedOpponentsContinueMass_le_one roots who time
  have hsurv0 : ∀ time, 0 ≤ survival time := fun time =>
    quittingOpponentSurvivalWeight_nonneg roots who 0 time
  have hsurv1 : ∀ time, survival time ≤ 1 := fun time =>
    quittingOpponentSurvivalWeight_le_one roots who 0 time
  have hsurvSucc : ∀ time, survival (time + 1) = survival time * mass time :=
    fun time => quittingOpponentSurvivalWeight_zero_succ roots who time
  have hquitPayoff : ∀ time,
      ledger time + survival time * quitValue time ≤ bound := by
    intro time
    have h := hpure (some time)
    rwa [quittingRootSequencePureTimeTerminalValue_some_eq] at h
  -- the constant-row bound at each presented row
  have hrow : ∀ time,
      target ≤ max (quitValue time) (absorb time / (1 - mass time)) := by
    intro time
    have h := quittingStationaryPunishmentValue_le reward who (roots time)
    rwa [quittingStationaryUnilateralCap_eq_max_div,
      quittingStationaryFixedOpponentsQuitValue_apply,
      quittingStationaryFixedOpponentsContinueReward_apply,
      quittingStationaryFixedOpponentsContinueMass_apply] at h
  -- the constant-row bound at the all-continue row
  have hsolo : target ≤
      max (quittingSetReward reward ({who} : Finset ι) who) 0 := by
    have h := quittingStationaryPunishmentValue_le reward who
      (quittingPureSetRoot (∅ : Finset ι))
    rw [quittingStationaryUnilateralCap_pureSetRoot] at h
    have hrewrite :
        max (quittingSetReward reward (insert who (∅ : Finset ι)) who)
            (quittingSetReward reward ((∅ : Finset ι).erase who) who) =
          max (quittingSetReward reward ({who} : Finset ι) who) 0 := by
      simp
    rwa [hrewrite] at h
  by_cases hride : ∀ time, (1 - mass time) * target ≤ absorb time
  case neg =>
    -- some stage favours the stop branch; take the first one
    obtain ⟨witness, hwitness⟩ := not_forall.mp hride
    have hex : ∃ time, absorb time < (1 - mass time) * target :=
      ⟨witness, not_le.mp hwitness⟩
    have hbad := Nat.find_spec hex
    have hbefore : ∀ time < Nat.find hex, (1 - mass time) * target ≤
        absorb time := fun time htime => not_lt.mp (Nat.find_min hex htime)
    have hnotOne : mass (Nat.find hex) ≠ 1 := by
      intro hone
      have hzero : absorb (Nat.find hex) = 0 := by
        simp only [habsorbDef]
        exact quittingStationaryFixedOpponentsContinueReward_eq_zero_of_mass_eq_one
          reward (root := roots (Nat.find hex)) (who := who) hone
      rw [hzero, hone] at hbad
      simp at hbad
    have hlt : mass (Nat.find hex) < 1 :=
      lt_of_le_of_ne (hmass1 _) hnotOne
    have hpos : 0 < 1 - mass (Nat.find hex) := by linarith
    have hdiv : absorb (Nat.find hex) / (1 - mass (Nat.find hex)) < target := by
      rw [div_lt_iff₀ hpos]
      linarith [hbad]
    have hquitBig : target ≤ quitValue (Nat.find hex) := by
      rcases le_max_iff.mp (hrow (Nat.find hex)) with h | h
      · exact h
      · linarith
    have hledgerBig := le_quittingLiveLedgerAccum_add_survival_mul
      reward roots who target (Nat.find hex) hbefore
    have hscaled := mul_le_mul_of_nonneg_left hquitBig (hsurv0 (Nat.find hex))
    have hfinal := hquitPayoff (Nat.find hex)
    linarith
  case pos =>
    -- every stage favours the absorption branch
    have hledgerAll : ∀ time,
        target ≤ ledger time + survival time * target := fun time =>
      le_quittingLiveLedgerAccum_add_survival_mul reward roots who target time
        fun step _ => hride step
    have hanti : Antitone survival := by
      apply antitone_nat_of_succ_le
      intro time
      rw [hsurvSucc time]
      nlinarith [hsurv0 time, hmass1 time]
    have hbdd : BddBelow (Set.range survival) :=
      ⟨0, by rintro _ ⟨time, rfl⟩; exact hsurv0 time⟩
    set stall := ⨅ time, survival time with hstall
    have hstallTendsto : Tendsto survival atTop (nhds stall) :=
      tendsto_atTop_ciInf hanti hbdd
    have hstall0 : 0 ≤ stall := le_ciInf hsurv0
    have hstallLe : ∀ time, stall ≤ survival time := fun time =>
      ciInf_le hbdd time
    by_cases hproduct : target * stall ≤ 0
    case pos =>
      -- the never-quit reply collects the whole ledger
      have hlimit : Tendsto (fun time => target - survival time * target) atTop
          (nhds (target - stall * target)) :=
        tendsto_const_nhds.sub (hstallTendsto.mul_const target)
      have hcompare : target - stall * target ≤
          quittingRootSequencePureTimeTerminalValue reward roots who none 0 :=
        le_of_tendsto_of_tendsto' hlimit
          (tendsto_quittingLiveLedgerAccum reward roots who)
          fun time => by linarith [hledgerAll time]
      have := hpure none
      nlinarith
    case neg =>
      replace hproduct : 0 < target * stall := not_le.mp hproduct
      have hstallPos : 0 < stall := by
        rcases hstall0.lt_or_eq with h | h
        · exact h
        · exfalso; rw [← h] at hproduct; simp at hproduct
      have htargetPos : 0 < target := by nlinarith
      have hsoloBig : target ≤
          quittingSetReward reward ({who} : Finset ι) who := by
        rcases le_max_iff.mp hsolo with h | h
        · exact h
        · linarith
      refine le_of_forall_pos_le_add fun ε hε => ?_
      set scale := 2 * quittingRewardBound reward + 1 with hscale
      have hscalePos : 0 < scale := by
        have := quittingRewardBound_nonneg reward
        rw [hscale]; linarith
      have hgap : Tendsto (fun time => survival time - survival (time + 1))
          atTop (nhds 0) := by
        have hshift : Tendsto (fun time => survival (time + 1)) atTop
            (nhds stall) := hstallTendsto.comp (tendsto_add_atTop_nat 1)
        simpa using hstallTendsto.sub hshift
      have hthreshold : 0 < stall * (ε / scale) := by positivity
      obtain ⟨time, htime⟩ :=
        (hgap.eventually (gt_mem_nhds hthreshold)).exists
      have hmassGap : stall * (1 - mass time) ≤
          survival time - survival (time + 1) := by
        rw [hsurvSucc time]
        have hle := mul_le_mul_of_nonneg_right (hstallLe time)
          (by linarith [hmass1 time] : (0 : ℝ) ≤ 1 - mass time)
        nlinarith [hle]
      have hsmall : 1 - mass time < ε / scale := by
        have hchain : stall * (1 - mass time) < stall * (ε / scale) := by
          linarith
        exact lt_of_mul_lt_mul_left (by linarith [hchain]) hstall0
      have hgapNonneg : (0 : ℝ) ≤ 1 - mass time := by linarith [hmass1 time]
      have hdrop : 2 * quittingRewardBound reward * (1 - mass time) < ε := by
        have hle : 2 * quittingRewardBound reward * (1 - mass time) ≤
            scale * (1 - mass time) := by
          have := quittingRewardBound_nonneg reward
          nlinarith
        have hlt : scale * (1 - mass time) < scale * (ε / scale) :=
          mul_lt_mul_of_pos_left hsmall hscalePos
        have hcancel : scale * (ε / scale) = ε := by
          field_simp
        linarith
      have hnear : quittingSetReward reward ({who} : Finset ι) who -
          2 * quittingRewardBound reward * (1 - mass time) ≤
            quitValue time := by
        have hclose := quittingSetReward_singleton_sub_le_fixedOpponentsQuitValue
          reward (roots time) who
        rw [quittingStationaryFixedOpponentsQuitValue_apply,
          quittingStationaryFixedOpponentsContinueMass_apply] at hclose
        rw [hquitDef, hmassDef]
        exact hclose
      have hdiff : target - quitValue time ≤
          2 * quittingRewardBound reward * (1 - mass time) := by linarith
      have hdropNonneg :
          0 ≤ 2 * quittingRewardBound reward * (1 - mass time) := by
        have := quittingRewardBound_nonneg reward
        positivity
      have hscaledDiff : survival time * (target - quitValue time) ≤
          2 * quittingRewardBound reward * (1 - mass time) := by
        have hfirst := mul_le_mul_of_nonneg_left hdiff (hsurv0 time)
        nlinarith [hsurv1 time]
      have hexpand : survival time * target =
          survival time * quitValue time +
            survival time * (target - quitValue time) := by ring
      linarith [hledgerAll time, hquitPayoff time]

/-- **Lower leg.**  No opponent plan, however history dependent, punishes
`who` below the constant-row punishment value. -/
theorem quittingStationaryPunishmentValue_le_quittingBestReplyValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingStationaryPunishmentValue reward who ≤
      quittingBestReplyValue reward profile who := by
  refine quittingStationaryPunishmentValue_le_of_forall_pureTime_le reward
    (quittingProfileLiveRoot reward profile) who fun quitTime => ?_
  rw [← quittingTerminalPayoff_update_pureTimeBehaviorStrategy]
  exact le_quittingBestReplyValue reward profile who _

/-- **Lower leg, infimum form.** -/
theorem quittingStationaryPunishmentValue_le_quittingPunishmentValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    quittingStationaryPunishmentValue reward who ≤
      quittingPunishmentValue reward who := by
  haveI : Nonempty ((quittingGame reward).BehaviorProfile) :=
    ⟨quittingAlwaysContinueProfile reward⟩
  exact le_ciInf fun profile =>
    quittingStationaryPunishmentValue_le_quittingBestReplyValue reward profile
      who

/-- **The quitting min-max is a stationary stopping value.**  Player `who`'s
punishment value at the active state, an infimum over all history-dependent
opponent plans of the supremum over all history-dependent replies, is already
computed by constant opponent rows: it equals the infimum over product rows
`y` of the selected stopping cap `Phi(y) = max (S(y), H(y) / (1 - c(y)))`.

Neither infimum is claimed to be attained. -/
theorem quittingPunishmentValue_eq_stationaryPunishmentValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    quittingPunishmentValue reward who =
      quittingStationaryPunishmentValue reward who :=
  le_antisymm (quittingPunishmentValue_le_stationaryPunishmentValue reward who)
    (quittingStationaryPunishmentValue_le_quittingPunishmentValue reward who)

/-- The punishment value is above the table's own negated bound, so it is a
genuine real number and not a degenerate infimum. -/
theorem neg_quittingRewardBound_le_quittingPunishmentValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    -quittingRewardBound reward ≤ quittingPunishmentValue reward who := by
  rw [quittingPunishmentValue_eq_stationaryPunishmentValue]
  haveI : Nonempty (ι → PMF Bool) := ⟨fun _ => PMF.pure false⟩
  exact le_ciInf fun root =>
    neg_quittingRewardBound_le_quittingStationaryUnilateralCap reward who root

/-- The punishment value never exceeds the solo-clipped ceiling
`max (r_who({who}), 0)` forced by opponents who never quit. -/
theorem quittingPunishmentValue_le_max_solo
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    quittingPunishmentValue reward who ≤
      max (quittingSetReward reward ({who} : Finset ι) who) 0 := by
  have h := quittingPunishmentValue_le_stationaryUnilateralCap reward who
    (quittingPureSetRoot (∅ : Finset ι))
  rw [quittingStationaryUnilateralCap_pureSetRoot] at h
  have hrewrite :
      max (quittingSetReward reward (insert who (∅ : Finset ι)) who)
          (quittingSetReward reward ((∅ : Finset ι).erase who) who) =
        max (quittingSetReward reward ({who} : Finset ι) who) 0 := by
    simp
  rwa [hrewrite] at h

/-! ## Punishment plans presented as root sequences

Consumers of a "punishment plan" present it as a root sequence and ask for a
cap on every hazard reply.  Both legs are available in that shape. -/

/-- **A constant punishment plan caps every hazard reply at its own selected
cap.**  This is the upper leg in the root-sequence shape, with no contraction
hypothesis on the row. -/
theorem quittingRootSequenceHazardTerminalValue_const_le_cap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) (hazard : ℕ → PMF Bool) :
    quittingRootSequenceHazardTerminalValue reward (fun _ => root) who
        hazard 0 ≤
      quittingStationaryUnilateralCap reward root who := by
  have h := quittingTerminalPayoff_update_stationary_le_cap reward root who
    (fun time _ => hazard time)
  rwa [quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue,
    quittingProfileLiveRoot_stationary] at h

/-- **No punishment plan promises a cap below the constant-row value.**  The
lower leg in the root-sequence shape: if a plan caps every hazard reply by
`bound`, then `bound` is at least the constant-row punishment value. -/
theorem quittingStationaryPunishmentValue_le_of_forall_hazard_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) {bound : ℝ}
    (hplan : ∀ hazard : ℕ → PMF Bool,
      quittingRootSequenceHazardTerminalValue reward roots who hazard 0 ≤
        bound) :
    quittingStationaryPunishmentValue reward who ≤ bound :=
  quittingStationaryPunishmentValue_le_of_forall_pureTime_le reward roots who
    fun quitTime => hplan (quittingPureTimeHazard quitTime)

/-! ## A two-coordinate regression

The table punishing each player by `-1000` whenever the other quits has
punishment value exactly `-1000`, attained by the opponent's sure exit. -/

namespace QuittingHostileTwoCoordinate

/-- Each player is paid `-1000` at every terminal state its opponent joins,
and `0` at its own solo exit. -/
def reward : {S : Finset Bool // S.Nonempty} → Payoff Bool :=
  fun S player => if (!player) ∈ S.1 then -1000 else 0

/-- The opponent's sure exit is a pure exit root. -/
theorem quittingStationaryUnilateralCap_opponentExit (who : Bool) :
    quittingStationaryUnilateralCap reward
      (quittingPureSetRoot ({!who} : Finset Bool)) who = -1000 := by
  rw [quittingStationaryUnilateralCap_pureSetRoot]
  have hinsert : quittingSetReward reward (insert who ({!who} : Finset Bool))
      who = -1000 := by
    rw [quittingSetReward_of_nonempty reward (Finset.insert_nonempty _ _)]
    simp [reward]
  have herase : quittingSetReward reward
      (({!who} : Finset Bool).erase who) who = -1000 := by
    rw [Finset.erase_eq_of_notMem (by simp), quittingSetReward_of_nonempty
      reward (Finset.singleton_nonempty _)]
    simp [reward]
  rw [hinsert, herase, max_self]

/-- No row punishes below `-1000`: the quit branch alone already bounds it. -/
theorem neg_thousand_le_quittingStationaryUnilateralCap
    (who : Bool) (root : Bool → PMF Bool) :
    (-1000 : ℝ) ≤ quittingStationaryUnilateralCap reward root who := by
  refine le_quittingStationaryUnilateralCap_of_forall_le reward who
    (by norm_num) (fun S => ?_) root
  change (-1000 : ℝ) ≤ if (!who) ∈ S.1 then -1000 else 0
  split <;> norm_num

/-- **The hostile two-coordinate punishment value is `-1000`.** -/
theorem quittingPunishmentValue_eq (who : Bool) :
    quittingPunishmentValue reward who = -1000 := by
  rw [quittingPunishmentValue_eq_stationaryPunishmentValue]
  refine le_antisymm ?_ ?_
  · rw [← quittingStationaryUnilateralCap_opponentExit who]
    exact quittingStationaryPunishmentValue_le reward who _
  · haveI : Nonempty (Bool → PMF Bool) := ⟨fun _ => PMF.pure false⟩
    exact le_ciInf fun root =>
      neg_thousand_le_quittingStationaryUnilateralCap who root

end QuittingHostileTwoCoordinate

/-! ## The ceiling is a strict over-approximation

The solo-clipped ceiling `max (r_who({who}), 0)` is the constant-row cap at
the all-continue row alone.  On the table below it is `2` while the true
punishment value is `0`: a player whose own solo exit is profitable is still
punished to zero by the opponent's sure exit. -/

namespace QuittingProfitableSoloTwoCoordinate

/-- A solo exit is worth `2`; any terminal state the opponent joins is worth
`0`. -/
def reward : {S : Finset Bool // S.Nonempty} → Payoff Bool :=
  fun S player => if (!player) ∈ S.1 then 0 else 2

/-- The opponent's sure exit caps the deviator at zero. -/
theorem quittingStationaryUnilateralCap_opponentExit (who : Bool) :
    quittingStationaryUnilateralCap reward
      (quittingPureSetRoot ({!who} : Finset Bool)) who = 0 := by
  rw [quittingStationaryUnilateralCap_pureSetRoot]
  have hinsert : quittingSetReward reward
      (insert who ({!who} : Finset Bool)) who = 0 := by
    rw [quittingSetReward_of_nonempty reward (Finset.insert_nonempty _ _)]
    simp [reward]
  have herase : quittingSetReward reward
      (({!who} : Finset Bool).erase who) who = 0 := by
    rw [Finset.erase_eq_of_notMem (by simp), quittingSetReward_of_nonempty
      reward (Finset.singleton_nonempty _)]
    simp [reward]
  rw [hinsert, herase, max_self]

/-- **The profitable-solo punishment value is zero.** -/
theorem quittingPunishmentValue_eq (who : Bool) :
    quittingPunishmentValue reward who = 0 := by
  rw [quittingPunishmentValue_eq_stationaryPunishmentValue]
  refine le_antisymm ?_ ?_
  · rw [← quittingStationaryUnilateralCap_opponentExit who]
    exact quittingStationaryPunishmentValue_le reward who _
  · haveI : Nonempty (Bool → PMF Bool) := ⟨fun _ => PMF.pure false⟩
    refine le_ciInf fun root => ?_
    refine le_quittingStationaryUnilateralCap_of_forall_le reward who le_rfl
      (fun S => ?_) root
    change (0 : ℝ) ≤ if (!who) ∈ S.1 then 0 else 2
    split <;> norm_num

/-- The deviator's own solo exit is worth `2`. -/
theorem quittingSetReward_singleton (who : Bool) :
    quittingSetReward reward ({who} : Finset Bool) who = 2 := by
  rw [quittingSetReward_of_nonempty reward (Finset.singleton_nonempty who)]
  simp [reward]

/-- **The solo-clipped ceiling is strictly loose here.**  The exact
punishment value is `0` while the ceiling is `2`. -/
theorem quittingPunishmentValue_lt_max_solo (who : Bool) :
    quittingPunishmentValue reward who <
      max (quittingSetReward reward ({who} : Finset Bool) who) 0 := by
  rw [quittingPunishmentValue_eq, quittingSetReward_singleton]
  norm_num

end QuittingProfitableSoloTwoCoordinate

end GameTheory
