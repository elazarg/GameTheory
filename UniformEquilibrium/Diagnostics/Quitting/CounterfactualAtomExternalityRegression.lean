/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeAtomContinuePrefixAccess
import UniformEquilibrium.Diagnostics.Quitting.TerminalDebtLiteralStackAllContinueRegression

/-!
# Counterfactual payoff atoms can be pure debt transfer

A positive prescribed-payoff atom comparing two deviations by `mover` is a
payoff externality for `observer`; it is not an `observer` deviation.  This
two-player quitting regression keeps all of the literal prefix data which
might otherwise appear to repair that mismatch:

* the replacement is an exact terminal best response of `mover`;
* arbitrarily deep all-Continue prefixes are exact Nash root stacks;
* mover-deleted prefix survival is exactly one;
* the complete terminal semantic pair, hence total debt, is unchanged by the
  exact prefix; and
* the counterfactual atom has charge one at the reached terminal coalition.

Nevertheless `observer` has zero gain from every unilateral behavioral
deviation at the original prefixed profile.  The reset merely transfers the
unit debt from `mover` to `observer`, leaving total debt unchanged.

This does not satisfy the positive *global-minimum* provenance of a quitting
counterexample regime: the same reward table has other zero-debt profiles.
Accordingly it is a sharp local fence, not a counterexample to uniform
equilibrium existence.  Any atom-to-strategy compiler must use global
minimum provenance after the counterfactual reset (or add an explicit
observer-side strategic sign); exact-prefix chronology alone cannot do so.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

namespace CounterfactualAtomExternalityRegression

abbrev Player := Bool
abbrev mover : Player := false
abbrev observer : Player := true

/-- Only a joint quit is nonzero: it rewards `mover` and charges `observer`.
Both singleton quitting rewards vanish. -/
def reward : {S : Finset Player // S.Nonempty} → Payoff Player :=
  fun terminal who =>
    if terminal.val = {mover, observer} then
      if who = mover then 1 else -1
    else 0

/-- Cemetery background before the displayed pure-time updates. -/
def cemetery : (quittingGame reward).BehaviorProfile :=
  quittingRootSequenceProfile reward (fun _ _ => PMF.pure false) 0

/-- `observer` quits alone immediately; `mover` Continues forever. -/
def source : (quittingGame reward).BehaviorProfile :=
  Function.update cemetery observer
    (quittingPureTimeBehaviorStrategy reward observer (some 0))

/-- `mover`'s selected terminal replacement joins `observer` immediately. -/
def replacement : (quittingGame reward).BehaviorStrategy mover :=
  quittingPureTimeBehaviorStrategy reward mover (some 0)

/-- The full reset endpoint, at which both players quit immediately. -/
def target : (quittingGame reward).BehaviorProfile :=
  Function.update source mover replacement

def jointTerminal : {S : Finset Player // S.Nonempty} :=
  ⟨{mover, observer}, by simp⟩

/-- Arbitrarily long literal exact-prefix words used by the regression. -/
def roots (depth : ℕ) : List (Player → PMF Bool) :=
  List.replicate depth quittingAllContinueRoot

theorem reward_bound (terminal : {S : Finset Player // S.Nonempty})
    (who : Player) : |reward terminal who| ≤ 1 := by
  unfold reward
  split_ifs <;> norm_num

theorem reward_observer_nonpos
    (terminal : {S : Finset Player // S.Nonempty}) :
    reward terminal observer ≤ 0 := by
  by_cases hterminal : terminal.val = {mover, observer}
  · simp [reward, hterminal, mover, observer]
  · simp [reward, hterminal]

theorem terminalPayoff_observer_nonpos
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingTerminalPayoff reward profile observer ≤ 0 := by
  rw [← congrFun (quittingTerminalRewardMoment_outcomeMass reward profile)
    observer]
  unfold quittingTerminalRewardMoment
  apply Finset.sum_nonpos
  intro outcome _
  exact mul_nonpos_of_nonneg_of_nonpos
    ((quittingTerminalOutcomeMass_mem_stdSimplex reward profile).1 outcome)
    (by cases outcome with
      | none => simp [quittingTerminalOutcomeReward]
      | some terminal =>
          simpa [quittingTerminalOutcomeReward] using
            reward_observer_nonpos terminal)

theorem source_liveRoot_zero :
    quittingProfileLiveRoot reward source 0 = fun who =>
      if who = observer then PMF.pure true else PMF.pure false := by
  funext who
  cases who <;>
    simp [source, cemetery, quittingProfileLiveRoot,
      quittingRootSequenceProfile, quittingPureTimeBehaviorStrategy,
      quittingPureTimeHazard, observer]

theorem target_liveRoot_zero :
    quittingProfileLiveRoot reward target 0 = fun _ => PMF.pure true := by
  funext who
  cases who <;>
    simp [target, replacement, source, cemetery, quittingProfileLiveRoot,
      quittingPureTimeBehaviorStrategy,
      quittingPureTimeHazard, mover, observer]

theorem source_joint_mass_eq_zero :
    quittingTerminalOutcomeMass reward source (some jointTerminal) = 0 := by
  rw [source,
    quittingTerminalOutcomeMass_update_pureTime_some_mem_eq_at
      reward cemetery observer 0 jointTerminal (by simp [jointTerminal])]
  rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
    show quittingProfileLiveRoot reward
      (Function.update cemetery observer
        (quittingPureTimeBehaviorStrategy reward observer (some 0))) 0 =
        (fun who => if who = observer then PMF.pure true else PMF.pure false) by
          exact source_liveRoot_zero]
  simp [quittingRootCoalitionMass, quittingRootQuitRates,
    Math.PMFProduct.coalitionMass, jointTerminal, mover, observer]

theorem target_joint_mass_eq_one :
    quittingTerminalOutcomeMass reward target (some jointTerminal) = 1 := by
  rw [show target = Function.update source mover
      (quittingPureTimeBehaviorStrategy reward mover (some 0)) by rfl,
    quittingTerminalOutcomeMass_update_pureTime_some_mem_eq_at
      reward source mover 0 jointTerminal (by simp [jointTerminal])]
  rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
    show quittingProfileLiveRoot reward
      (Function.update source mover
        (quittingPureTimeBehaviorStrategy reward mover (some 0))) 0 =
        (fun _ => PMF.pure true) by exact target_liveRoot_zero]
  have hcomplement : ({observer} : Finset Player)ᶜ = {mover} := by decide
  simp [quittingRootCoalitionMass, quittingRootQuitRates,
    Math.PMFProduct.coalitionMass, jointTerminal, mover, observer,
    hcomplement]

theorem terminalPayoff_mover_eq_jointMass
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingTerminalPayoff reward profile mover =
      quittingTerminalOutcomeMass reward profile (some jointTerminal) := by
  rw [← congrFun (quittingTerminalRewardMoment_outcomeMass reward profile)
    mover]
  unfold quittingTerminalRewardMoment
  rw [Finset.sum_eq_single (some jointTerminal)]
  · simp [quittingTerminalOutcomeReward, reward, jointTerminal,
      mover, observer]
  · intro outcome _houtcome hne
    cases outcome with
    | none => simp [quittingTerminalOutcomeReward]
    | some terminal =>
        have hterminal : terminal ≠ jointTerminal := by
          intro heq
          subst terminal
          exact hne rfl
        have hval : terminal.val ≠ {mover, observer} := by
          intro hval
          apply hterminal
          apply Subtype.ext
          exact hval
        simp [quittingTerminalOutcomeReward, reward, hval,
          mover, observer]
  · simp

theorem terminalPayoff_observer_eq_neg_jointMass
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingTerminalPayoff reward profile observer =
      -quittingTerminalOutcomeMass reward profile (some jointTerminal) := by
  rw [← congrFun (quittingTerminalRewardMoment_outcomeMass reward profile)
    observer]
  unfold quittingTerminalRewardMoment
  rw [Finset.sum_eq_single (some jointTerminal)]
  · simp [quittingTerminalOutcomeReward, reward, jointTerminal,
      mover, observer]
  · intro outcome _houtcome hne
    cases outcome with
    | none => simp [quittingTerminalOutcomeReward]
    | some terminal =>
        have hterminal : terminal ≠ jointTerminal := by
          intro heq
          subst terminal
          exact hne rfl
        have hval : terminal.val ≠ {mover, observer} := by
          intro hval
          apply hterminal
          apply Subtype.ext
          exact hval
        simp [quittingTerminalOutcomeReward, reward, hval,
          mover, observer]
  · simp

theorem source_payoff_mover :
    quittingTerminalPayoff reward source mover = 0 := by
  rw [terminalPayoff_mover_eq_jointMass, source_joint_mass_eq_zero]

theorem source_payoff_observer :
    quittingTerminalPayoff reward source observer = 0 := by
  rw [source, quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
    cemetery, quittingProfileLiveRoot_quittingRootSequenceProfile_zero]
  rw [quittingRootSequencePureTimeTerminalValue_some_self_eq_fixedOpponents]
  unfold quittingFixedOpponentsQuitValue quittingRootAbsorbingContribution
    quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_bool]
  simp [expect_eq_sum, reward, mover, observer, quittingRootPayoff,
    quittingQuitters, Finset.ext_iff]

theorem target_payoff_mover :
    quittingTerminalPayoff reward target mover = 1 := by
  rw [terminalPayoff_mover_eq_jointMass, target_joint_mass_eq_one]

theorem target_payoff_observer :
    quittingTerminalPayoff reward target observer = -1 := by
  rw [terminalPayoff_observer_eq_neg_jointMass, target_joint_mass_eq_one]

/-- Every observer deviation at the source still sees either its zero-valued
singleton coalition or Never, because `mover` never quits. -/
theorem source_observer_deviation_payoff_le_zero
    (deviation : (quittingGame reward).BehaviorStrategy observer) :
    quittingTerminalPayoff reward
      (Function.update source observer deviation) observer ≤ 0 :=
  terminalPayoff_observer_nonpos _

theorem source_bestResponse_mover :
    quittingContinuationBestResponseValue reward source mover = 1 := by
  apply le_antisymm
  · exact le_of_abs_le (abs_quittingContinuationBestResponseValue_le
      reward source mover (M := 1) (by norm_num) reward_bound)
  · have hlower := quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward source mover replacement (M := 1) (by norm_num) reward_bound
    change quittingTerminalPayoff reward target mover ≤
      quittingContinuationBestResponseValue reward source mover at hlower
    rw [target_payoff_mover] at hlower
    exact hlower

theorem source_bestResponse_observer :
    quittingContinuationBestResponseValue reward source observer = 0 := by
  apply le_antisymm
  · unfold quittingContinuationBestResponseValue
    apply csSup_le
    · exact Set.range_nonempty _
    · rintro value ⟨deviation, rfl⟩
      simpa only using source_observer_deviation_payoff_le_zero deviation
  · have hlower := quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward source observer (source observer) (M := 1) (by norm_num)
        reward_bound
    rw [Function.update_eq_self, source_payoff_observer] at hlower
    exact hlower

theorem target_bestResponse_mover :
    quittingContinuationBestResponseValue reward target mover = 1 := by
  apply le_antisymm
  · exact le_of_abs_le (abs_quittingContinuationBestResponseValue_le
      reward target mover (M := 1) (by norm_num) reward_bound)
  · have hlower := quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward target mover (target mover) (M := 1) (by norm_num) reward_bound
    rw [Function.update_eq_self, target_payoff_mover] at hlower
    exact hlower

theorem target_observer_continue_payoff :
    quittingTerminalPayoff reward
      (Function.update target observer
        (quittingPureTimeBehaviorStrategy reward observer none)) observer = 0 := by
  rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy]
  unfold quittingRootSequencePureTimeTerminalValue
  rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman]
  have hmass : quittingFixedOpponentsContinueMass
      (quittingProfileLiveRoot reward target) observer 0 = 0 := by
    unfold quittingFixedOpponentsContinueMass
    rw [target_liveRoot_zero]
    simp [quittingStationaryContinueMass, quittingAllContinueAction,
      pmfPi_apply, observer]
  have hcontinue : quittingFixedOpponentsContinueReward reward
      (quittingProfileLiveRoot reward target) observer 0 = 0 := by
    unfold quittingFixedOpponentsContinueReward
    rw [target_liveRoot_zero]
    unfold quittingRootAbsorbingContribution quittingRootExpectedPayoff
    rw [Math.PMFProduct.expect_pmfPi_bool]
    simp [expect_eq_sum, reward, mover, observer, quittingRootPayoff,
      quittingQuitters, Finset.ext_iff]
  rw [hmass, hcontinue]
  simp [target_liveRoot_zero, reward, mover, observer,
    quittingFixedOpponentsQuitValue,
    quittingRootAbsorbingContribution, quittingRootExpectedPayoff,
    quittingRootPayoff, quittingQuitters, expect_eq_sum, Finset.ext_iff]

theorem target_bestResponse_observer :
    quittingContinuationBestResponseValue reward target observer = 0 := by
  apply le_antisymm
  · unfold quittingContinuationBestResponseValue
    apply csSup_le
    · exact Set.range_nonempty _
    · rintro value ⟨deviation, rfl⟩
      exact terminalPayoff_observer_nonpos _
  · have hlower := quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward target observer
        (quittingPureTimeBehaviorStrategy reward observer none)
        (M := 1) (by norm_num) reward_bound
    rw [target_observer_continue_payoff] at hlower
    exact hlower

theorem source_debt_mover :
    quittingTerminalDeviationDebt reward source mover = 1 := by
  rw [quittingTerminalDeviationDebt, source_bestResponse_mover,
    source_payoff_mover]
  norm_num

theorem source_debt_observer :
    quittingTerminalDeviationDebt reward source observer = 0 := by
  rw [quittingTerminalDeviationDebt, source_bestResponse_observer,
    source_payoff_observer]
  norm_num

theorem target_debt_mover :
    quittingTerminalDeviationDebt reward target mover = 0 := by
  rw [quittingTerminalDeviationDebt, target_bestResponse_mover,
    target_payoff_mover]
  norm_num

theorem target_debt_observer :
    quittingTerminalDeviationDebt reward target observer = 1 := by
  rw [quittingTerminalDeviationDebt, target_bestResponse_observer,
    target_payoff_observer]
  norm_num

theorem source_totalDebt : quittingTerminalDebtSum reward source = 1 := by
  unfold quittingTerminalDebtSum
  rw [Fintype.sum_bool, source_debt_mover, source_debt_observer]
  norm_num

theorem target_totalDebt : quittingTerminalDebtSum reward target = 1 := by
  unfold quittingTerminalDebtSum
  rw [Fintype.sum_bool, target_debt_mover, target_debt_observer]
  norm_num

theorem replacement_is_exactBestResponse :
    quittingTerminalPayoff reward target mover -
        quittingTerminalPayoff reward source mover =
      quittingTerminalDeviationDebt reward source mover := by
  rw [target_payoff_mover, source_payoff_mover, source_debt_mover]
  norm_num

theorem singleton_reward_le_source_payoff (who : Player) :
    reward (quittingSingletonTerminal who) who ≤
      quittingTerminalPayoff reward source who := by
  cases who <;>
    simp [reward, quittingSingletonTerminal, mover, observer,
      source_payoff_mover, source_payoff_observer, Finset.ext_iff]

theorem roots_exactStack (depth : ℕ) :
    IsQuittingLiteralExactRootStack reward (roots depth) source := by
  exact isQuittingLiteralExactRootStack_replicate_allContinue reward source
    depth (M := 1) (by norm_num) reward_bound
      singleton_reward_le_source_payoff

theorem prefixed_semanticPair_eq_source (depth : ℕ) :
    quittingTerminalSemanticPair reward
        (quittingLiteralRootStackProfile reward (roots depth) source) =
      quittingTerminalSemanticPair reward source := by
  exact quittingTerminalSemanticPair_literalAllContinueStack_eq_terminal
    reward source depth (M := 1) (by norm_num) reward_bound
      singleton_reward_le_source_payoff

theorem moverDeletedSurvival_eq_one (depth : ℕ) :
    quittingLiteralRootStackOpponentSurvival (roots depth) mover = 1 := by
  have hroot : Function.update
      (quittingAllContinueRoot : Player → PMF Bool) mover (PMF.pure false) =
      quittingAllContinueRoot := by
    funext who
    cases who <;> simp [mover, quittingAllContinueRoot]
  have hmass : quittingStationaryContinueMass
      (quittingAllContinueRoot : Player → PMF Bool) = 1 := by
    simp [quittingStationaryContinueMass, quittingAllContinueRoot,
      quittingAllContinueAction, pmfPi_apply]
  simp [roots, quittingLiteralRootStackOpponentSurvival,
    quittingRootOpponentContinueMass, hroot, hmass]

/-- The prescribed-payoff atom is positive although it is carried by two
counterfactual `mover` deviations, not by an `observer` deviation. -/
theorem counterfactual_observer_atom_eq_one :
    quittingTerminalPayoffDifferenceAtom reward source target observer
      (some jointTerminal) = 1 := by
  unfold quittingTerminalPayoffDifferenceAtom
  rw [source_joint_mass_eq_zero, target_joint_mass_eq_one]
  simp [quittingTerminalOutcomeReward, reward, jointTerminal, mover, observer]

/-- At every depth the original exact-prefix profile has zero observer debt,
while resetting the mover transfers, rather than destroys, the unit total
debt. -/
theorem exactPrefix_positiveAtom_but_no_observerGain (depth : ℕ) :
    IsQuittingLiteralExactRootStack reward (roots depth) source ∧
      quittingLiteralRootStackOpponentSurvival (roots depth) mover = 1 ∧
      quittingTerminalDebtSum reward
          (quittingLiteralRootStackProfile reward (roots depth) source) = 1 ∧
      quittingTerminalPayoffDifferenceAtom reward source target observer
          (some jointTerminal) = 1 ∧
      (∀ deviation : (quittingGame reward).BehaviorStrategy observer,
        quittingTerminalPayoff reward
            (Function.update
              (quittingLiteralRootStackProfile reward (roots depth) source)
              observer deviation) observer -
          quittingTerminalPayoff reward
            (quittingLiteralRootStackProfile reward (roots depth) source)
              observer ≤ 0) ∧
      quittingTerminalDebtSum reward target =
        quittingTerminalDebtSum reward source := by
  refine ⟨roots_exactStack depth, moverDeletedSurvival_eq_one depth, ?_,
    counterfactual_observer_atom_eq_one, ?_, ?_⟩
  · have hpair := prefixed_semanticPair_eq_source depth
    have hsum := congrArg quittingTerminalSemanticDebtSum hpair
    have hdebtEq : quittingTerminalDebtSum reward
        (quittingLiteralRootStackProfile reward (roots depth) source) =
        quittingTerminalDebtSum reward source := by
      simpa [quittingTerminalDebtSum, quittingTerminalSemanticDebtSum,
        quittingTerminalSemanticDebt, quittingTerminalSemanticPair,
        quittingTerminalDeviationDebt] using hsum
    rw [hdebtEq, source_totalDebt]
  · intro deviation
    have hpair := prefixed_semanticPair_eq_source depth
    have hprofilePayoff : quittingTerminalPayoff reward
        (quittingLiteralRootStackProfile reward (roots depth) source) observer = 0 := by
      have := congrFun (congrArg Prod.fst hpair) observer
      change quittingTerminalPayoff reward
          (quittingLiteralRootStackProfile reward (roots depth) source)
            observer = quittingTerminalPayoff reward source observer at this
      rw [source_payoff_observer] at this
      exact this
    have hcap : quittingContinuationBestResponseValue reward
        (quittingLiteralRootStackProfile reward (roots depth) source) observer = 0 := by
      have := congrFun (congrArg Prod.snd hpair) observer
      change quittingContinuationBestResponseValue reward
          (quittingLiteralRootStackProfile reward (roots depth) source)
            observer = quittingContinuationBestResponseValue reward source
              observer at this
      rw [source_bestResponse_observer] at this
      exact this
    have hdeviation := quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward (quittingLiteralRootStackProfile reward (roots depth) source)
        observer deviation (M := 1) (by norm_num) reward_bound
    rw [hcap] at hdeviation
    rw [hprofilePayoff]
    linarith
  · rw [target_totalDebt, source_totalDebt]

end CounterfactualAtomExternalityRegression

end GameTheory
