/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticSimultaneousResetOrientationLocalization
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetIncidenceCapReturn
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStoppingLawTransferBalanceRegression

/-!
# A flat simultaneous recipient need not carry literal incidence

The joint-recipient branch of simultaneous reset localization is a statement
about the behavioral best-response envelope.  It does not identify a terminal
coalition in the prescribed law.  This file records both sides of that seam.

First, an explicit incidence bridge consumes the joint recipient immediately:
in a counterexample regime, its co-realized positive incidence yields a
positive-mass terminal atom with a strict membership toggle.  The other branch
retains the already-localized positive-slope edge.

Second, the bridge is not automatic.  A literal two-player flat reset moves
one unit of debt from a surely quitting mover to the other player while the
target law is `Never`.  Hence the target has zero mover--recipient incidence.
The recipient debt is the value of a counterfactual solo deviation, not mass
of a prescribed coalition.  A reset/cycle or atomic compiler therefore needs
positive co-realized incidence (or an equivalent reached-row state match) in
addition to the debt-rise datum.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability
open QuittingSureSetOwnerRepair

namespace FlatRecipientIncidenceRegression

/-- Reset owner. -/
abbrev owner : Bool := false

/-- Coordinate receiving the owner's lost debt. -/
abbrev recipient : Bool := true

/-- The owner receives `-2` whenever it quits.  The recipient receives `2`
only when it quits alone. -/
def reward : {S : Finset Bool // S.Nonempty} → Payoff Bool :=
  fun terminal player ↦
    if player = owner then
      if owner ∈ terminal.val then -2 else 0
    else if terminal.val = {recipient} then 2 else 0

theorem abs_reward_le_two
    (terminal : {S : Finset Bool // S.Nonempty}) (player : Bool) :
    |reward terminal player| ≤ 2 := by
  unfold reward
  split_ifs <;> norm_num

/-- Literal source: the owner quits surely and the recipient continues. -/
def source : (quittingGame reward).BehaviorProfile :=
  quittingStationaryProfile reward (quittingPureSetRoot {owner})

/-- Literal target: both players continue forever. -/
def target : (quittingGame reward).BehaviorProfile :=
  quittingStationaryProfile reward (quittingPureSetRoot ∅)

theorem target_eq_update_source_never :
    target = Function.update source owner
      (quittingAlwaysContinueStrategy reward owner) := by
  funext player time history
  by_cases hplayer : player = owner
  · subst player
    simp [target, source, quittingStationaryProfile,
      StochasticGame.stationaryBehaviorProfile, quittingPureSetRoot,
      quittingSetAction, quittingAlwaysContinueStrategy]
    rfl
  · have hrecipient : player = recipient := by
      cases player <;> simp_all [owner, recipient]
    subst player
    simp [target, source, quittingStationaryProfile,
      StochasticGame.stationaryBehaviorProfile, quittingPureSetRoot,
      quittingSetAction, owner, recipient]

/-- Exact complete-stopping-law reset ray. -/
def mixed (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    (quittingGame reward).BehaviorProfile :=
  Function.update source owner
    (quittingStoppingLawMixtureBehaviorStrategy reward owner (source owner)
      (quittingAlwaysContinueStrategy reward owner) lambda hlambda0 hlambda1)

/-- The simultaneous family resets every coordinate toward `Never`; the
recipient is already playing that law. -/
def replacement (who : Bool) : (quittingGame reward).BehaviorStrategy who :=
  quittingAlwaysContinueStrategy reward who

theorem simultaneous_one_eq_target :
    quittingSimultaneousStoppingLawMixtureProfile reward source replacement
        1 zero_le_one le_rfl = target := by
  have halways (who : Bool) :
      quittingBehaviorLiveHazard reward
          (quittingAlwaysContinueStrategy reward who) =
        fun _time ↦ PMF.pure false := by
    funext time
    rfl
  have hcoin (hzero : (0 : ℝ) ≤ 0) (hone : (0 : ℝ) ≤ 1) :
      Math.Probability.DiscreteHazard.booleanCoin 0 hzero hone =
        PMF.pure false := by
    apply PMF.ext
    intro action
    apply (ENNReal.toReal_eq_toReal_iff'
      (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
    cases action
    · rw [Math.Probability.DiscreteHazard.booleanCoin_false_toReal]
      simp
    · rw [Math.Probability.DiscreteHazard.booleanCoin_true_toReal]
      simp
  have hmixed (who : Bool)
      (strategy : (quittingGame reward).BehaviorStrategy who) :
      quittingStoppingLawMixtureBehaviorStrategy reward who strategy
          (quittingAlwaysContinueStrategy reward who) 1 zero_le_one le_rfl =
        quittingAlwaysContinueStrategy reward who := by
    cases who
    all_goals
    funext time history
    simpa [quittingStoppingLawMixtureBehaviorStrategy,
      Math.Probability.DiscreteHazard.BooleanHazard.convexMix,
      Math.Probability.DiscreteHazard.ScalarHazard.convexMix,
      Math.Probability.DiscreteHazard.ScalarHazard.mixedSurvival,
      Math.Probability.DiscreteHazard.ScalarHazard.mixedStopMass, halways,
      Math.Probability.DiscreteHazard.ScalarHazard.toBoolean,
      Math.Probability.DiscreteHazard.BooleanHazard.toScalar,
      Math.Probability.DiscreteHazard.stopProbability,
      Math.Probability.DiscreteHazard.ScalarHazard.stopMass,
      Math.Probability.DiscreteHazard.ScalarHazard.survival,
      Math.survivalProduct, quittingAlwaysContinueStrategy, quittingGame] using
        hcoin (by norm_num) (by norm_num)
  funext player
  change quittingStoppingLawMixtureBehaviorStrategy reward player
      (source player) (quittingAlwaysContinueStrategy reward player)
        1 zero_le_one le_rfl = target player
  rw [hmixed]
  funext time history
  cases player <;>
    rfl

theorem source_debt_owner :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward source) owner = 2 := by
  unfold source
  rw [quittingTerminalSemanticDebt_pureSetRoot_eq reward {owner} owner
    (by norm_num) abs_reward_le_two]
  norm_num [owner, quittingSetReward, reward]

theorem source_debt_recipient :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward source) recipient = 0 := by
  unfold source
  rw [quittingTerminalSemanticDebt_pureSetRoot_eq reward {owner} recipient
    (by norm_num) abs_reward_le_two]
  norm_num [owner, recipient, quittingSetReward, reward, Fin.ext_iff,
    show ({true, false} : Finset Bool) ≠ {true} by decide]

theorem target_debt_owner :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward target) owner = 0 := by
  unfold target
  rw [quittingTerminalSemanticDebt_pureSetRoot_eq reward ∅ owner
    (by norm_num) abs_reward_le_two]
  norm_num [owner, quittingSetReward, reward]

theorem target_debt_recipient :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward target) recipient = 2 := by
  unfold target
  rw [quittingTerminalSemanticDebt_pureSetRoot_eq reward ∅ recipient
    (by norm_num) abs_reward_le_two]
  norm_num [recipient, owner, quittingSetReward, reward]

/-- The owner loses debt at rate two. -/
theorem mixed_debt_owner
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (mixed lambda hlambda0 hlambda1)) owner = 2 * (1 - lambda) := by
  have haffine := quittingTerminalSemanticDebt_stoppingLawMixture_eq_self
    reward source owner (source owner)
      (quittingAlwaysContinueStrategy reward owner)
      lambda hlambda0 hlambda1
  rw [Function.update_eq_self, ← target_eq_update_source_never,
    source_debt_owner, target_debt_owner] at haffine
  change quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (mixed lambda hlambda0 hlambda1)) owner = _ at haffine
  nlinarith

/-- Prescribed recipient payoff vanishes along the ray. -/
theorem mixed_payoff_recipient
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    quittingTerminalPayoff reward
        (mixed lambda hlambda0 hlambda1) recipient = 0 := by
  have haffine := quittingTerminalPayoff_stoppingLawMixture_eq
    reward source owner recipient (source owner)
      (quittingAlwaysContinueStrategy reward owner) lambda hlambda0 hlambda1
  rw [Function.update_eq_self, ← target_eq_update_source_never] at haffine
  unfold source target at haffine
  rw [quittingTerminalPayoff_pureSetRoot,
    quittingTerminalPayoff_pureSetRoot] at haffine
  norm_num [mixed, recipient, owner, quittingSetReward, reward] at haffine ⊢
  exact haffine

/-- Quitting immediately is worth exactly the transferred debt. -/
theorem mixed_quitNow_payoff_recipient
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    let deviation := quittingPureTimeBehaviorStrategy reward recipient (some 0)
    quittingTerminalPayoff reward
        (Function.update (mixed lambda hlambda0 hlambda1) recipient deviation)
        recipient = 2 * lambda := by
  dsimp only
  let deviation := quittingPureTimeBehaviorStrategy reward recipient (some 0)
  have haffine := quittingTerminalPayoff_stoppingLawMixture_eq
    reward (Function.update source recipient deviation) owner recipient
      (source owner) (quittingAlwaysContinueStrategy reward owner)
      lambda hlambda0 hlambda1
  have hsourceCommute :
      Function.update (Function.update source recipient deviation) owner
          (source owner) = Function.update source recipient deviation := by
    rw [Function.update_comm (by decide : recipient ≠ owner)]
    simp
  have htargetCommute :
      Function.update (Function.update source recipient deviation) owner
          (quittingAlwaysContinueStrategy reward owner) =
        Function.update target recipient deviation := by
    rw [Function.update_comm (by decide : recipient ≠ owner),
      target_eq_update_source_never]
  have hmixedCommute :
      Function.update (Function.update source recipient deviation) owner
          (quittingStoppingLawMixtureBehaviorStrategy reward owner
            (source owner) (quittingAlwaysContinueStrategy reward owner)
            lambda hlambda0 hlambda1) =
        Function.update (mixed lambda hlambda0 hlambda1) recipient deviation := by
    rw [Function.update_comm (by decide : recipient ≠ owner)]
    rfl
  rw [hmixedCommute, hsourceCommute, htargetCommute] at haffine
  dsimp only [deviation] at haffine
  unfold source target at haffine
  rw [quittingTerminalPayoff_update_pureSetRoot_quitNow,
    quittingTerminalPayoff_update_pureSetRoot_quitNow] at haffine
  norm_num [recipient, owner, quittingSetReward, reward, Fin.ext_iff,
    show ({true, false} : Finset Bool) ≠ {true} by decide] at haffine ⊢
  linarith

theorem mixed_update_recipient_payoff_le
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (deviation : (quittingGame reward).BehaviorStrategy recipient) :
    quittingTerminalPayoff reward
        (Function.update (mixed lambda hlambda0 hlambda1) recipient deviation)
        recipient ≤ 2 * lambda := by
  have haffine := quittingTerminalPayoff_stoppingLawMixture_eq
    reward (Function.update source recipient deviation) owner recipient
      (source owner) (quittingAlwaysContinueStrategy reward owner)
      lambda hlambda0 hlambda1
  have hsourceCommute :
      Function.update (Function.update source recipient deviation) owner
          (source owner) = Function.update source recipient deviation := by
    rw [Function.update_comm (by decide : recipient ≠ owner)]
    simp
  have htargetCommute :
      Function.update (Function.update source recipient deviation) owner
          (quittingAlwaysContinueStrategy reward owner) =
        Function.update target recipient deviation := by
    rw [Function.update_comm (by decide : recipient ≠ owner),
      target_eq_update_source_never]
  have hmixedCommute :
      Function.update (Function.update source recipient deviation) owner
          (quittingStoppingLawMixtureBehaviorStrategy reward owner
            (source owner) (quittingAlwaysContinueStrategy reward owner)
            lambda hlambda0 hlambda1) =
        Function.update (mixed lambda hlambda0 hlambda1) recipient deviation := by
    rw [Function.update_comm (by decide : recipient ≠ owner)]
    rfl
  rw [hmixedCommute, hsourceCommute, htargetCommute] at haffine
  have hsourceUpper := quittingTerminalPayoff_update_pureSetRoot_le
    reward {owner} recipient deviation
  have htargetUpper := quittingTerminalPayoff_update_pureSetRoot_le
    reward ∅ recipient deviation
  change quittingTerminalPayoff reward
      (Function.update source recipient deviation) recipient ≤ _ at hsourceUpper
  change quittingTerminalPayoff reward
      (Function.update target recipient deviation) recipient ≤ _ at htargetUpper
  norm_num [recipient, owner, quittingSetReward, reward, Fin.ext_iff,
    show ({true, false} : Finset Bool) ≠ {true} by decide]
    at hsourceUpper htargetUpper
  nlinarith

theorem mixed_cap_recipient
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    quittingContinuationBestResponseValue reward
        (mixed lambda hlambda0 hlambda1) recipient = 2 * lambda := by
  unfold quittingContinuationBestResponseValue
  apply le_antisymm
  · apply csSup_le
    · exact Set.range_nonempty _
    · rintro payoff ⟨deviation, rfl⟩
      exact mixed_update_recipient_payoff_le lambda hlambda0 hlambda1 deviation
  · apply le_csSup
      (bddAbove_range_quittingTerminalPayoff_update reward
        (mixed lambda hlambda0 hlambda1) recipient (by norm_num)
          abs_reward_le_two)
    let deviation := quittingPureTimeBehaviorStrategy reward recipient (some 0)
    refine ⟨deviation, ?_⟩
    simpa only [deviation] using
      mixed_quitNow_payoff_recipient lambda hlambda0 hlambda1

/-- The recipient gains exactly the debt lost by the owner. -/
theorem mixed_debt_recipient
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (mixed lambda hlambda0 hlambda1)) recipient = 2 * lambda := by
  unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair
  change quittingContinuationBestResponseValue reward
      (mixed lambda hlambda0 hlambda1) recipient -
    quittingTerminalPayoff reward (mixed lambda hlambda0 hlambda1) recipient = _
  rw [mixed_cap_recipient lambda hlambda0 hlambda1,
    mixed_payoff_recipient lambda hlambda0 hlambda1]
  ring

/-- The whole literal reset ray is exactly flat. -/
theorem mixed_totalDebt
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (mixed lambda hlambda0 hlambda1)) = 2 := by
  unfold quittingTerminalSemanticDebtSum
  rw [Fintype.sum_bool, mixed_debt_owner lambda hlambda0 hlambda1,
    mixed_debt_recipient lambda hlambda0 hlambda1]
  ring

theorem source_totalDebt :
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward source) = 2 := by
  unfold quittingTerminalSemanticDebtSum
  rw [Fintype.sum_bool, source_debt_owner, source_debt_recipient]
  norm_num

/-- The literal all-Continue target has all of its terminal-law mass on
`Never`. -/
theorem target_neverMass_eq_one :
    quittingTerminalOutcomeMass reward target none = 1 := by
  change quittingLiveMassLimit reward target = 1
  apply tendsto_nhds_unique (tendsto_quittingLiveMass reward target)
  have hcontinue : quittingStationaryContinueMass
      (quittingPureSetRoot (∅ : Finset Bool)) = 1 :=
    quittingStationaryContinueMass_pureSetRoot_empty
  have hlive : ∀ time,
      quittingLiveMass reward target time = 1 := by
    intro time
    exact quittingLiveMass_stationary_eq_one_of_continueMass_eq_one
      reward (quittingPureSetRoot (∅ : Finset Bool)) hcontinue time
  exact (tendsto_const_nhds :
    Filter.Tendsto (fun _ : ℕ ↦ (1 : ℝ)) Filter.atTop (nhds 1)).congr'
      (Filter.Eventually.of_forall fun time ↦ (hlive time).symm)

/-- Every finite terminal atom of the all-Continue target has zero mass. -/
theorem target_terminalMass_eq_zero
    (terminal : {S : Finset Bool // S.Nonempty}) :
    quittingTerminalOutcomeMass reward target (some terminal) = 0 := by
  let mass := quittingTerminalOutcomeMass reward target
  have hsimplex := quittingTerminalOutcomeMass_mem_stdSimplex reward target
  have hsum := hsimplex.2
  have hnone : mass none = 1 := target_neverMass_eq_one
  have hterminalSum : (∑ candidate, mass (some candidate)) = 0 := by
    rw [Fintype.sum_option] at hsum
    linarith
  have hnonneg : 0 ≤ mass (some terminal) := hsimplex.1 (some terminal)
  have hle : mass (some terminal) ≤ ∑ candidate, mass (some candidate) :=
    Finset.single_le_sum
      (fun candidate _ ↦ hsimplex.1 (some candidate))
      (Finset.mem_univ terminal)
  dsimp only [mass] at hnone hterminalSum hnonneg hle ⊢
  linarith

/-- In particular, the debt recipient has no prescribed terminal incidence
at the flat target. -/
theorem target_owner_recipient_incidence_eq_zero :
    quittingTerminalOpponentIncidenceMass owner recipient
      (quittingTerminalOutcomeMass reward target) = 0 := by
  unfold quittingTerminalOpponentIncidenceMass
  apply Finset.sum_eq_zero
  intro terminal _hterminal
  exact target_terminalMass_eq_zero terminal

/-- The owner's complete-law reset carries the full minimum-reset passport;
the marked-window clause is deliberately instantiated at cutoff zero. -/
theorem owner_reset_passport :
    IsQuittingStoppingLawMinimumResetPassport reward source owner
      (quittingAlwaysContinueStrategy reward owner)
      (quittingSingletonTerminal owner) 0 := by
  dsimp only [IsQuittingStoppingLawMinimumResetPassport]
  have hsourcePayoff : quittingTerminalPayoff reward source owner = -2 := by
    unfold source
    rw [quittingTerminalPayoff_pureSetRoot]
    norm_num [owner, quittingSetReward, reward]
  have htargetPayoff : quittingTerminalPayoff reward target owner = 0 := by
    unfold target
    rw [quittingTerminalPayoff_pureSetRoot]
    norm_num [owner, quittingSetReward, reward]
  rw [source_debt_owner, ← target_eq_update_source_never,
    hsourcePayoff, htargetPayoff]
  constructor
  · norm_num
  constructor
  · norm_num
  intro lambda hlambda0 hlambda1
  norm_num only [sub_neg_eq_add, zero_add]
  change quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (mixed lambda hlambda0 hlambda1)) owner =
        2 - lambda * 2 ∧
      lambda * 2 ≤
        ∑ other ∈ Finset.univ.erase owner,
          quittingTerminalSemanticDebtChange
            (quittingTerminalSemanticPair reward source)
            (quittingTerminalSemanticPair reward
              (mixed lambda hlambda0 hlambda1)) other ∧
      (1 - lambda) *
          (∑ time ∈ Finset.range 0,
            quittingStageCoalitionMass reward source time
              (quittingSingletonTerminal owner)) ≤
        ∑ time ∈ Finset.range 0,
          quittingStageCoalitionMass reward
            (mixed lambda hlambda0 hlambda1) time
              (quittingSingletonTerminal owner)
  refine ⟨?_, ?_, by simp⟩
  · rw [mixed_debt_owner lambda hlambda0 hlambda1]
    ring
  · have herase : Finset.univ.erase owner = {recipient} := by decide
    rw [herase]
    simp only [Finset.sum_singleton, quittingTerminalSemanticDebtChange,
      mixed_debt_recipient lambda hlambda0 hlambda1,
      source_debt_recipient]
    ring_nf
    exact le_rfl

/-- The complete regression: exact flatness and a positive literal debt
transfer coexist with zero co-realized owner--recipient incidence. -/
theorem flat_debtTransfer_without_recipientIncidence :
    quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward target) =
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward source) ∧
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward target) owner = 0 ∧
      quittingTerminalSemanticDebtChange
          (quittingTerminalSemanticPair reward source)
          (quittingTerminalSemanticPair reward target) recipient = 2 ∧
      quittingTerminalOpponentIncidenceMass owner recipient
          (quittingTerminalOutcomeMass reward target) = 0 := by
  rw [show quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward target) = 2 by
        unfold quittingTerminalSemanticDebtSum
        rw [Fintype.sum_bool, target_debt_owner, target_debt_recipient]
        norm_num,
    source_totalDebt, target_debt_owner,
    quittingTerminalSemanticDebtChange, target_debt_recipient,
    source_debt_recipient, target_owner_recipient_incidence_eq_zero]
  norm_num

/-- The regression satisfies the actual simultaneous-reset input, not merely
an abstract two-state debt account.  At unit scale the joint target is the
literal all-Continue profile, the owner passport is retained, and the
quantitative joint-recipient conclusion holds with charge one. -/
theorem simultaneous_flatPassport_recipient_without_incidence :
    let simultaneousProfile :=
      quittingSimultaneousStoppingLawMixtureProfile reward source replacement
        1 zero_le_one le_rfl
    let sourcePair := quittingTerminalSemanticPair reward source
    let targetPair := quittingTerminalSemanticPair reward simultaneousProfile
    simultaneousProfile = target ∧
      IsQuittingStoppingLawMinimumResetPassport reward source owner
        (replacement owner) (quittingSingletonTerminal owner) 0 ∧
      quittingTerminalSemanticDebtSum targetPair =
        quittingTerminalSemanticDebtSum sourcePair ∧
      quittingTerminalSemanticDebt targetPair owner ≤
        quittingTerminalSemanticDebt sourcePair owner - 1 ∧
      recipient ∈ Finset.univ.erase owner ∧
      1 ≤ quittingTerminalSemanticDebtChange sourcePair targetPair recipient ∧
      quittingTerminalOpponentIncidenceMass owner recipient
        (quittingTerminalOutcomeMass reward simultaneousProfile) = 0 := by
  dsimp only
  rw [simultaneous_one_eq_target]
  refine ⟨rfl, ?_, ?_, ?_, by decide, ?_, ?_⟩
  · exact owner_reset_passport
  · exact flat_debtTransfer_without_recipientIncidence.1
  · rw [target_debt_owner, source_debt_owner]
    norm_num
  · rw [quittingTerminalSemanticDebtChange, target_debt_recipient,
      source_debt_recipient]
    norm_num
  · exact target_owner_recipient_incidence_eq_zero

end FlatRecipientIncidenceRegression

/-- A joint-recipient certificate that is ready for the counterexample
regime's atomic toggle consumer.  The debt edge and the positive-mass terminal
atom are kept in the same statement. -/
def HasQuittingFlatJointRecipientAtomicCertificate
    {ι : Type} [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source target : QuittingTerminalSemanticPair ι)
    (mass : QuittingTerminalOutcome ι → ℝ)
    (owner : ι) (opponents : Finset ι) (lambda charge : ℝ) : Prop :=
  ∃ recipient ∈ opponents,
    recipient ≠ owner ∧
      lambda * charge ≤
          quittingTerminalSemanticDebtChange source target recipient ∧
      ∃ terminal : {S : Finset ι // S.Nonempty},
        recipient ∈ terminal.val ∧ 0 < mass (some terminal) ∧
          ((∃ member ∈ terminal.val,
              quittingSetReward reward terminal.val member <
                quittingSetReward reward (terminal.val.erase member) member) ∨
            ∃ outsider ∉ terminal.val,
              quittingSetReward reward terminal.val outsider <
                quittingSetReward reward
                  (insert outsider terminal.val) outsider)

variable {ι : Type} [Fintype ι] [DecidableEq ι]

namespace QuittingCounterexampleRegime

/-- **Exact consumer for the joint-recipient branch.**

If every quantitative joint debt recipient is backed by positive incidence in
the complete law of that same literal simultaneous target, then reset
orientation localization reaches a named consumer on both branches:

* the joint branch gives a positive-mass terminal atom with a strict static
  toggle in the counterexample regime;
* the interaction branch retains its literal positive-slope atom.

The incidence bridge is the only additional premise.  The two-player
regression above proves that it cannot be inferred from flatness, the owner
drop, the recipient rise, and the full reset passport. -/
theorem activePassport_flatSimultaneous_atomicRecipient_or_localizedPositiveSlope
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (regime : QuittingCounterexampleRegime reward)
    (profile : (quittingGame reward).BehaviorProfile)
    (replacement : ∀ who, (quittingGame reward).BehaviorStrategy who)
    (who : ι) (terminal : {S : Finset ι // S.Nonempty}) (cutoff : ℕ)
    (lambda : ℝ) (hlambda0 : 0 < lambda) (hlambda1 : lambda ≤ 1)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ outcome player, |reward outcome player| ≤ M)
    (hpassport : IsQuittingStoppingLawMinimumResetPassport reward profile who
      (replacement who) terminal cutoff)
    (hflat : quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingSimultaneousStoppingLawMixtureProfile reward profile
            replacement lambda hlambda0.le hlambda1)) =
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward profile))
    (hincidenceBridge :
      let source := quittingTerminalSemanticPair reward profile
      let simultaneousProfile :=
        quittingSimultaneousStoppingLawMixtureProfile reward profile replacement
          lambda hlambda0.le hlambda1
      let simultaneousTarget :=
        quittingTerminalSemanticPair reward simultaneousProfile
      let endpointProfile := Function.update profile who (replacement who)
      let gain := quittingTerminalPayoff reward endpointProfile who -
        quittingTerminalPayoff reward profile who
      let opponents := Finset.univ.erase who
      let charge := gain / (2 * (opponents.card : ℝ))
      ∀ recipient ∈ opponents,
        lambda * charge ≤
            quittingTerminalSemanticDebtChange source simultaneousTarget
              recipient →
          0 < quittingTerminalOpponentIncidenceMass who recipient
            (quittingTerminalOutcomeMass reward simultaneousProfile)) :
    let source := quittingTerminalSemanticPair reward profile
    let simultaneousProfile :=
      quittingSimultaneousStoppingLawMixtureProfile reward profile replacement
        lambda hlambda0.le hlambda1
    let simultaneousTarget :=
      quittingTerminalSemanticPair reward simultaneousProfile
    let endpointProfile := Function.update profile who (replacement who)
    let gain := quittingTerminalPayoff reward endpointProfile who -
      quittingTerminalPayoff reward profile who
    let opponents := Finset.univ.erase who
    let charge := gain / (2 * (opponents.card : ℝ))
    HasQuittingFlatJointRecipientAtomicCertificate reward source
        simultaneousTarget
        (quittingTerminalOutcomeMass reward simultaneousProfile)
        who opponents lambda charge ∨
      ∃ moved ⊆ opponents, ∃ mover ∈ opponents, mover ∉ moved ∧
        let edgeSource := quittingStoppingLawMixtureHybridProfile reward profile
          replacement who lambda hlambda0.le hlambda1 moved
        let edgeTarget := quittingStoppingLawMixtureHybridProfile reward profile
          replacement who lambda hlambda0.le hlambda1 (insert mover moved)
        lambda * charge ≤
            quittingTerminalSemanticDebt
                (quittingTerminalSemanticPair reward edgeTarget) who -
              quittingTerminalSemanticDebt
                (quittingTerminalSemanticPair reward edgeSource) who ∧
          HasQuittingStoppingLawPositiveSlopeAtom reward edgeSource mover who
            (replacement mover) charge := by
  dsimp only at hincidenceBridge ⊢
  have hlocalized :=
    activePassport_flatSimultaneous_directed_or_localizedPositiveSlope
      reward profile replacement who terminal cutoff lambda hlambda0 hlambda1
        hM hreward hpassport hflat
  dsimp only at hlocalized
  rcases hlocalized with hrecipient | hslope
  · left
    rcases hrecipient with ⟨_hownerDrop, recipient, hrecipientMem,
      hrecipientDebt⟩
    refine ⟨recipient, hrecipientMem,
      Finset.ne_of_mem_erase hrecipientMem, hrecipientDebt, ?_⟩
    have hincidence := hincidenceBridge recipient hrecipientMem hrecipientDebt
    have hsimplex := quittingTerminalOutcomeMass_mem_stdSimplex reward
      (quittingSimultaneousStoppingLawMixtureProfile reward profile replacement
        lambda hlambda0.le hlambda1)
    exact regime.exists_supportedStrictToggle_of_incidence who recipient
      (quittingTerminalOutcomeMass reward
        (quittingSimultaneousStoppingLawMixtureProfile reward profile replacement
          lambda hlambda0.le hlambda1)) hsimplex hincidence
  · exact Or.inr hslope

end QuittingCounterexampleRegime

end GameTheory
