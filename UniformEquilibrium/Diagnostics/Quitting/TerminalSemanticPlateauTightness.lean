/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticAllContinuePlateau
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime
import UniformEquilibrium.Quitting.Cycles.BehaviorPureTimeExtremality
import UniformEquilibrium.Quitting.Terminal.TailCompression.ElementaryNeverCoupling

/-!
# Terminal-law tightness on a semantic plateau

Experimental proof of the missing compactness statement behind the finite
reward obstruction.  A semantic envelope is not merely bounded by a terminal
atom: along one realizing sequence it is the limit of pure-time deviations,
and the corresponding finite outcome laws have a convergent subsequence.
-/

noncomputable section

namespace GameTheory

open Filter Set
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A player's best-response envelope depends only on the opponents, not on
that player's displayed strategy. -/
theorem quittingContinuationBestResponseValue_update_self
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (strategy : (quittingGame reward).BehaviorStrategy who) :
    quittingContinuationBestResponseValue reward
        (Function.update profile who strategy) who =
      quittingContinuationBestResponseValue reward profile who := by
  unfold quittingContinuationBestResponseValue
  congr 2
  funext deviation
  rw [Function.update_idem]

/-- Replacing one player by an asymptotic best response resets that player's
semantic debt to zero.  This is a same-profile statement: the replacement
payoff and the original envelope use the same opponents. -/
theorem tendsto_terminalSemanticDebt_update_self
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile) (who : ι)
    (strategies : ℕ → (quittingGame reward).BehaviorStrategy who)
    (pair : QuittingTerminalSemanticPair ι)
    (hprofiles : Tendsto
      (fun n => quittingTerminalSemanticPair reward (profiles n))
      atTop (𝓝 pair))
    (hpayoff : Tendsto (fun n => quittingTerminalPayoff reward
      (Function.update (profiles n) who (strategies n)) who)
      atTop (𝓝 (pair.2 who))) :
    Tendsto (fun n => quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (Function.update (profiles n) who (strategies n))) who)
      atTop (𝓝 0) := by
  have henvelope : Tendsto (fun n =>
      quittingContinuationBestResponseValue reward (profiles n) who)
      atTop (𝓝 (pair.2 who)) :=
    ((continuous_apply who).comp (continuous_snd)).tendsto pair |>.comp
      hprofiles
  have hsub := henvelope.sub hpayoff
  simpa only [quittingTerminalSemanticDebt, quittingTerminalSemanticPair,
    quittingContinuationBestResponseValue_update_self, sub_self] using hsub

omit [Fintype ι] [DecidableEq ι] in
/-- If one coordinate tends to zero while every row has some coordinate above
a fixed positive gap, one fixed different coordinate carries that gap
frequently.  Finiteness of the player set is the pigeonhole input. -/
theorem exists_frequently_other_of_coordinate_tendsto_zero_of_uniform_witness
    [Finite ι]
    (debt : ℕ → ι → ℝ) (who : ι) (gap : ℝ)
    (hgap : 0 < gap)
    (hwho : Tendsto (fun n => debt n who) atTop (𝓝 0))
    (hwitness : ∀ n, ∃ player, gap ≤ debt n player) :
    ∃ other, other ≠ who ∧ (∃ᶠ n in atTop, gap ≤ debt n other) := by
  have hwhoSmall : ∀ᶠ n in atTop, debt n who < gap :=
    hwho.eventually (Iio_mem_nhds hgap)
  by_contra hnot
  push Not at hnot
  have hothersSmall : ∀ other, other ≠ who →
      ∀ᶠ n in atTop, debt n other < gap := by
    intro other hne
    simpa only [not_le] using hnot other hne
  have hallSmall : ∀ᶠ n in atTop, ∀ player, debt n player < gap := by
    rw [eventually_all]
    intro player
    by_cases hplayer : player = who
    · simpa [hplayer] using hwhoSmall
    · exact hothersSmall player hplayer
  obtain ⟨n, hn⟩ := hallSmall.exists
  obtain ⟨player, hplayer⟩ := hwitness n
  exact (not_lt_of_ge hplayer) (hn player)

/-- The counterexample terminal gap is attained by some semantic-debt
coordinate of every actual profile. -/
theorem QuittingCounterexampleRegime.exists_terminalGap_le_terminalSemanticDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (regime : QuittingCounterexampleRegime reward)
    (profile : (quittingGame reward).BehaviorProfile)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    ∃ player, regime.terminalGap ≤ quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) player := by
  obtain ⟨player, deviation, hgain⟩ := regime.terminalExploitability profile
  refine ⟨player, ?_⟩
  have hbest := quittingTerminalPayoff_update_le_continuationBestResponseValue
    reward profile player deviation hM hreward
  unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair
  dsimp only
  linarith

/-- **Regret transfer after a best-response reset.**  In a quitting
counterexample, if one player's debt tends to zero along actual profiles,
then one fixed different player carries the full terminal gap along a strict
subsequence.  This is a player-label transfer, not a return of semantic
states or terminal laws. -/
theorem QuittingCounterexampleRegime.exists_other_terminalGap_subsequence_of_semanticDebt_reset
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (regime : QuittingCounterexampleRegime reward)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile) (who : ι)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hreset : Tendsto (fun n => quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward (profiles n)) who)
      atTop (𝓝 0)) :
    ∃ (other : ι) (subseq : ℕ → ℕ),
      other ≠ who ∧ StrictMono subseq ∧
      ∀ n, regime.terminalGap ≤ quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward (profiles (subseq n))) other := by
  obtain ⟨other, hother, hfrequent⟩ :=
    exists_frequently_other_of_coordinate_tendsto_zero_of_uniform_witness
      (fun n player => quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward (profiles n)) player)
      who regime.terminalGap regime.terminalGap_pos hreset
      (fun n => regime.exists_terminalGap_le_terminalSemanticDebt
        reward (profiles n) hM hreward)
  obtain ⟨subseq, hsubseq, hdebt⟩ :=
    extraction_of_frequently_atTop hfrequent
  exact ⟨other, subseq, hother, hsubseq, hdebt⟩

/-- Every coordinate of a semantic envelope is represented by a limiting
terminal law of pure-time best-response approximants along one executable
realizing sequence. -/
theorem exists_pureTimeDeviation_terminalLaw_tendsto_semanticEnvelope
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (who : ι) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    ∃ (profiles : ℕ → (quittingGame reward).BehaviorProfile)
        (quitTime : ℕ → Option ℕ)
        (mass : QuittingTerminalOutcome ι → ℝ)
        (subseq : ℕ → ℕ),
      Tendsto (fun n => quittingTerminalSemanticPair reward (profiles n))
        atTop (𝓝 pair) ∧
      mass ∈ stdSimplex ℝ (QuittingTerminalOutcome ι) ∧
      StrictMono subseq ∧
      Tendsto (fun n => quittingTerminalOutcomeMass reward
          (Function.update (profiles (subseq n)) who
            (quittingPureTimeBehaviorStrategy reward who
              (quitTime (subseq n)))))
        atTop (𝓝 mass) ∧
      quittingTerminalRewardMoment reward mass who = pair.2 who := by
  obtain ⟨profiles, hprofiles⟩ :=
    exists_terminalProfile_sequence_tendsto_semanticPair reward pair hpair
  let error : ℕ → ℝ := fun n => 1 / (n + 1)
  have herrorPositive : ∀ n, 0 < error n := by
    intro n
    exact one_div_pos.mpr (by positivity)
  have hdeviation : ∀ n, ∃ deviation,
      quittingContinuationBestResponseValue reward (profiles n) who -
          error n / 2 ≤
        quittingTerminalPayoff reward
          (Function.update (profiles n) who deviation) who := by
    intro n
    exact exists_quittingContinuation_deviation_ge_sub reward
      (profiles n) who (half_pos (herrorPositive n)) hM hreward
  choose deviation hdeviationPayoff using hdeviation
  have hpureTime : ∀ n, ∃ quitTime : Option ℕ,
      quittingTerminalPayoff reward
          (Function.update (profiles n) who (deviation n)) who ≤
        quittingTerminalPayoff reward
          (Function.update (profiles n) who
            (quittingPureTimeBehaviorStrategy reward who quitTime)) who +
              error n / 2 := by
    intro n
    exact exists_quittingPureTimeBehaviorStrategy_terminalPayoff_ge_sub
      reward (profiles n) who (deviation n) (half_pos (herrorPositive n))
  choose quitTime hpureTimePayoff using hpureTime
  let deviated : ℕ → (quittingGame reward).BehaviorProfile := fun n =>
    Function.update (profiles n) who
      (quittingPureTimeBehaviorStrategy reward who (quitTime n))
  have hlower : ∀ n,
      quittingContinuationBestResponseValue reward (profiles n) who -
          error n ≤
        quittingTerminalPayoff reward (deviated n) who := by
    intro n
    dsimp only [deviated]
    linarith [hdeviationPayoff n, hpureTimePayoff n]
  have hupper : ∀ n,
      quittingTerminalPayoff reward (deviated n) who ≤
        quittingContinuationBestResponseValue reward (profiles n) who := by
    intro n
    exact quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward (profiles n) who
        (quittingPureTimeBehaviorStrategy reward who (quitTime n))
          hM hreward
  have herror : Tendsto error atTop (nhds 0) := by
    simpa [error] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have henvelope : Tendsto (fun n =>
      quittingContinuationBestResponseValue reward (profiles n) who)
      atTop (nhds (pair.2 who)) := by
    have hsemanticEnvelope : Tendsto (fun n =>
        (quittingTerminalSemanticPair reward (profiles n)).2 who)
        atTop (nhds (pair.2 who)) :=
      ((continuous_apply who).comp (continuous_snd)).tendsto pair |>.comp
        hprofiles
    exact hsemanticEnvelope
  have hdeviatedPayoff : Tendsto (fun n =>
      quittingTerminalPayoff reward (deviated n) who)
      atTop (nhds (pair.2 who)) := by
    have henvelope' : Tendsto (fun n =>
        quittingContinuationBestResponseValue reward (profiles n) who)
        atTop (nhds (pair.2 who - 0)) := by
      simpa only [sub_zero] using henvelope
    have htendsto := tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (henvelope.sub herror) henvelope'
      (Eventually.of_forall hlower) (Eventually.of_forall hupper)
    simpa only [sub_zero] using htendsto
  let masses : ℕ → QuittingTerminalOutcome ι → ℝ := fun n =>
    quittingTerminalOutcomeMass reward (deviated n)
  have hmasses : ∀ n,
      masses n ∈ stdSimplex ℝ (QuittingTerminalOutcome ι) := by
    intro n
    exact quittingTerminalOutcomeMass_mem_stdSimplex reward (deviated n)
  obtain ⟨mass, hmass, subseq, hsubseq, hmassLimit⟩ :=
    (isCompact_stdSimplex ℝ (QuittingTerminalOutcome ι)).tendsto_subseq
      hmasses
  refine ⟨profiles, quitTime, mass, subseq, hprofiles, hmass, hsubseq, ?_, ?_⟩
  · change Tendsto (masses ∘ subseq) atTop (𝓝 mass)
    exact hmassLimit
  · have hmomentLimit : Tendsto (fun n =>
        quittingTerminalRewardMoment reward (masses (subseq n)) who)
        atTop
        (nhds (quittingTerminalRewardMoment reward mass who)) :=
      ((continuous_apply who).comp
        (continuous_quittingTerminalRewardMoment reward)).tendsto mass |>.comp
          hmassLimit
    have hpayoffSubseq : Tendsto (fun n =>
        quittingTerminalRewardMoment reward (masses (subseq n)) who)
        atTop (nhds (pair.2 who)) := by
      have hsub := hdeviatedPayoff.comp hsubseq.tendsto_atTop
      have hsub' : Tendsto (fun n =>
          quittingTerminalPayoff reward (deviated (subseq n)) who)
          atTop (nhds (pair.2 who)) := by
        change Tendsto
          ((fun n => quittingTerminalPayoff reward (deviated n) who) ∘ subseq)
          atTop (nhds (pair.2 who))
        exact hsub
      simpa only [masses, quittingTerminalRewardMoment_outcomeMass] using hsub'
    exact tendsto_nhds_unique hmomentLimit hpayoffSubseq

omit [DecidableEq ι] in
/-- A positive semantic debt is carried by a genuinely profitable atom with
positive mass in the limiting pure-time deviation law. -/
theorem exists_positiveMass_profitableTerminalOutcome_of_semanticDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (who : ι) (mass : QuittingTerminalOutcome ι → ℝ)
    (hmass : mass ∈ stdSimplex ℝ (QuittingTerminalOutcome ι))
    (hmoment : quittingTerminalRewardMoment reward mass who = pair.2 who)
    (hpositive : 0 < quittingTerminalSemanticDebt pair who) :
    ∃ outcome : QuittingTerminalOutcome ι,
      0 < mass outcome ∧
        pair.1 who < quittingTerminalOutcomeReward reward outcome who := by
  by_contra hnot
  push Not at hnot
  have hterm : ∀ outcome,
      mass outcome * quittingTerminalOutcomeReward reward outcome who ≤
        mass outcome * pair.1 who := by
    intro outcome
    by_cases hzero : mass outcome = 0
    · simp [hzero]
    · have hmassPositive : 0 < mass outcome :=
        lt_of_le_of_ne (hmass.1 outcome) (Ne.symm hzero)
      exact mul_le_mul_of_nonneg_left
        (hnot outcome hmassPositive) hmassPositive.le
  have hsum : quittingTerminalRewardMoment reward mass who ≤ pair.1 who := by
    unfold quittingTerminalRewardMoment
    calc
      (∑ outcome, mass outcome *
          quittingTerminalOutcomeReward reward outcome who) ≤
          ∑ outcome, mass outcome * pair.1 who :=
        Finset.sum_le_sum fun outcome _ => hterm outcome
      _ = (∑ outcome, mass outcome) * pair.1 who := by
        rw [Finset.sum_mul]
      _ = pair.1 who := by rw [hmass.2, one_mul]
  unfold quittingTerminalSemanticDebt at hpositive
  linarith

/-- **All-Continue terminal-law alternative.**  Positive plateau debt is
witnessed with positive limiting pure-time deviation mass either by genuine
`Never`, or by a terminal coalition other than the deviator's singleton that
strictly improves on the prescribed coordinate. -/
theorem exists_persistent_profitableAtom_of_allContinueSemanticPlateau
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hnash : IsεQuittingRootNash reward pair.1 0
      (quittingAllContinueRoot : ι → PMF Bool))
    (who : ι) (hpositive : 0 < quittingTerminalSemanticDebt pair who)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    ∃ (profiles : ℕ → (quittingGame reward).BehaviorProfile)
        (quitTime : ℕ → Option ℕ)
        (mass : QuittingTerminalOutcome ι → ℝ)
        (subseq : ℕ → ℕ) (outcome : QuittingTerminalOutcome ι),
      Tendsto (fun n => quittingTerminalSemanticPair reward (profiles n))
        atTop (𝓝 pair) ∧
      mass ∈ stdSimplex ℝ (QuittingTerminalOutcome ι) ∧
      StrictMono subseq ∧
      Tendsto (fun n => quittingTerminalOutcomeMass reward
          (Function.update (profiles (subseq n)) who
            (quittingPureTimeBehaviorStrategy reward who
              (quitTime (subseq n)))))
      atTop (𝓝 mass) ∧
      Tendsto (fun n => quittingTerminalPayoff reward
          (Function.update (profiles (subseq n)) who
            (quittingPureTimeBehaviorStrategy reward who
              (quitTime (subseq n)))) who)
        atTop (𝓝 (pair.2 who)) ∧
      Tendsto (fun n => quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update (profiles (subseq n)) who
              (quittingPureTimeBehaviorStrategy reward who
                (quitTime (subseq n))))) who)
        atTop (𝓝 0) ∧
      0 < mass outcome ∧
      (∀ᶠ n : ℕ in atTop,
        mass outcome / 2 <
          quittingTerminalOutcomeMass reward
            (Function.update (profiles (subseq n)) who
              (quittingPureTimeBehaviorStrategy reward who
                (quitTime (subseq n)))) outcome) ∧
      (outcome = none ∧ pair.1 who < 0 ∨
        ∃ terminal : {S : Finset ι // S.Nonempty},
          outcome = some terminal ∧ terminal.val ≠ {who} ∧
            pair.1 who < reward terminal who) := by
  obtain ⟨profiles, quitTime, mass, subseq, hprofiles, hmass, hsubseq,
      hmassLimit, hmoment⟩ :=
    exists_pureTimeDeviation_terminalLaw_tendsto_semanticEnvelope
      reward pair hpair who hM hreward
  obtain ⟨outcome, houtcomeMass, houtcomeGain⟩ :=
    exists_positiveMass_profitableTerminalOutcome_of_semanticDebt
      reward pair who mass hmass hmoment hpositive
  have hpayoff : Tendsto (fun n => quittingTerminalPayoff reward
      (Function.update (profiles (subseq n)) who
        (quittingPureTimeBehaviorStrategy reward who
          (quitTime (subseq n)))) who)
      atTop (𝓝 (pair.2 who)) := by
    have hmomentLimit : Tendsto (fun n =>
        quittingTerminalRewardMoment reward
          (quittingTerminalOutcomeMass reward
            (Function.update (profiles (subseq n)) who
              (quittingPureTimeBehaviorStrategy reward who
                (quitTime (subseq n))))) who)
        atTop (𝓝 (quittingTerminalRewardMoment reward mass who)) :=
      ((continuous_apply who).comp
        (continuous_quittingTerminalRewardMoment reward)).tendsto mass |>.comp
          hmassLimit
    rw [hmoment] at hmomentLimit
    simpa only [quittingTerminalRewardMoment_outcomeMass] using hmomentLimit
  have hreset : Tendsto (fun n => quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (Function.update (profiles (subseq n)) who
          (quittingPureTimeBehaviorStrategy reward who
            (quitTime (subseq n))))) who)
      atTop (𝓝 0) := by
    apply tendsto_terminalSemanticDebt_update_self reward
      (fun n => profiles (subseq n)) who
      (fun n => quittingPureTimeBehaviorStrategy reward who
        (quitTime (subseq n))) pair
    · exact hprofiles.comp hsubseq.tendsto_atTop
    · exact hpayoff
  refine ⟨profiles, quitTime, mass, subseq, outcome, hprofiles, hmass,
    hsubseq, hmassLimit, hpayoff, hreset, houtcomeMass, ?_, ?_⟩
  · have hcoordinate : Tendsto (fun n =>
        quittingTerminalOutcomeMass reward
          (Function.update (profiles (subseq n)) who
            (quittingPureTimeBehaviorStrategy reward who
              (quitTime (subseq n)))) outcome)
        atTop (nhds (mass outcome)) :=
      ((continuous_apply outcome).tendsto mass).comp hmassLimit
    exact hcoordinate.eventually
      (Ioi_mem_nhds (by linarith : mass outcome / 2 < mass outcome))
  cases outcome with
  | none =>
      left
      exact ⟨rfl, by simpa [quittingTerminalOutcomeReward] using houtcomeGain⟩
  | some terminal =>
      right
      refine ⟨terminal, rfl, ?_, by
        simpa [quittingTerminalOutcomeReward] using houtcomeGain⟩
      intro heq
      have hterminal : terminal = quittingSingletonTerminal who :=
        Subtype.ext heq
      have hsingleton :=
        (isZeroQuittingRootNash_allContinue_iff_singleton_le
          reward pair.1).mp hnash who
      apply (not_lt_of_ge hsingleton)
      simpa [hterminal, quittingTerminalOutcomeReward] using houtcomeGain

/-! ## Dynamic support of the selected pure-time atom -/

/-- Updating one player to quit at a deterministic finite time leaves zero
terminal `Never` mass. -/
theorem quittingLiveMassLimit_update_pureTimeBehaviorStrategy_some_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (quitTime : ℕ) :
    quittingLiveMassLimit reward
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who (some quitTime))) = 0 := by
  let deviated := Function.update profile who
    (quittingPureTimeBehaviorStrategy reward who (some quitTime))
  have hcontinue : quittingJointContinueMass reward deviated quitTime = 0 := by
    rw [quittingJointContinueMass_eq_product]
    apply Finset.prod_eq_zero (Finset.mem_univ who)
    have hpure : deviated who quitTime (quittingLiveHist reward quitTime) =
        (PMF.pure true : PMF Bool) := by
      simp only [deviated, Function.update_self,
        quittingPureTimeBehaviorStrategy, quittingPureTimeHazard_some_self]
    rw [hpure]
    change ((PMF.pure true : PMF Bool) false).toReal = 0
    rw [PMF.pure_apply]
    norm_num
  have hliveZero : quittingLiveMass reward deviated (quitTime + 1) = 0 := by
    rw [quittingLiveMass_succ, hcontinue, mul_zero]
  exact le_antisymm
    ((quittingLiveMassLimit_le reward deviated (quitTime + 1)).trans_eq hliveZero)
    (quittingLiveMassLimit_nonneg reward deviated)

/-- Positive `Never` mass along pure-time deviations forces their selected
quit time to be literally `Never`. -/
theorem eventually_quitTime_eq_none_of_persistent_neverMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (who : ι) (quitTime : ℕ → Option ℕ) (lower : ℝ)
    (hlower : 0 < lower)
    (hpersistent : ∀ᶠ n in atTop, lower <
      quittingTerminalOutcomeMass reward
        (Function.update (profiles n) who
          (quittingPureTimeBehaviorStrategy reward who (quitTime n))) none) :
    ∀ᶠ n in atTop, quitTime n = none := by
  filter_upwards [hpersistent] with n hn
  cases hchoice : quitTime n with
  | none => rfl
  | some time =>
      exfalso
      have hzero : quittingTerminalOutcomeMass reward
          (Function.update (profiles n) who
            (quittingPureTimeBehaviorStrategy reward who (quitTime n))) none = 0 := by
        simp only [quittingTerminalOutcomeMass]
        rw [hchoice]
        exact quittingLiveMassLimit_update_pureTimeBehaviorStrategy_some_eq_zero
          reward (profiles n) who time
      rw [hzero] at hn
      linarith

/-- **Executable three-way plateau alternative.**  The persistent profitable
atom retained by a positive all-Continue semantic plateau is exactly one of:

* genuine `Never`, in which case the selected near-best response is literally
  `Never` eventually;
* a coalition containing the debtor and at least one other player, hence a
  collision at the selected deterministic quit date;
* a coalition excluding the debtor, hence opponent absorption while the
  pure-time deviation is still continuing.

The common witness retains convergence of the actual realizing profiles and
positive asymptotic mass on the selected atom.  Its terminal law still
aggregates over dates.  Refining the last two branches into fixed-date
concentration, diffuse time mass, or boundary escape requires an exact
disintegration of `quittingAbsorbedMassLimit` into survival-weighted stage
coalition atoms; that time-local identity is not asserted here. -/
theorem exists_persistent_profitableAtom_trichotomy_of_allContinueSemanticPlateau
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hnash : IsεQuittingRootNash reward pair.1 0
      (quittingAllContinueRoot : ι → PMF Bool))
    (who : ι) (hpositive : 0 < quittingTerminalSemanticDebt pair who)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    ∃ (profiles : ℕ → (quittingGame reward).BehaviorProfile)
        (quitTime : ℕ → Option ℕ)
        (mass : QuittingTerminalOutcome ι → ℝ)
        (subseq : ℕ → ℕ) (outcome : QuittingTerminalOutcome ι),
      Tendsto (fun n => quittingTerminalSemanticPair reward (profiles n))
          atTop (𝓝 pair) ∧
      mass ∈ stdSimplex ℝ (QuittingTerminalOutcome ι) ∧
      StrictMono subseq ∧
      Tendsto (fun n => quittingTerminalOutcomeMass reward
          (Function.update (profiles (subseq n)) who
            (quittingPureTimeBehaviorStrategy reward who
              (quitTime (subseq n)))))
        atTop (𝓝 mass) ∧
      Tendsto (fun n => quittingTerminalPayoff reward
          (Function.update (profiles (subseq n)) who
            (quittingPureTimeBehaviorStrategy reward who
              (quitTime (subseq n)))) who)
        atTop (𝓝 (pair.2 who)) ∧
      Tendsto (fun n => quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update (profiles (subseq n)) who
              (quittingPureTimeBehaviorStrategy reward who
                (quitTime (subseq n))))) who)
        atTop (𝓝 0) ∧
      0 < mass outcome ∧
      (∀ᶠ n : ℕ in atTop,
        mass outcome / 2 <
          quittingTerminalOutcomeMass reward
            (Function.update (profiles (subseq n)) who
              (quittingPureTimeBehaviorStrategy reward who
                (quitTime (subseq n)))) outcome) ∧
      ((outcome = none ∧ pair.1 who < 0 ∧
          ∀ᶠ n in atTop, quitTime (subseq n) = none) ∨
        (∃ terminal : {S : Finset ι // S.Nonempty},
          outcome = some terminal ∧ who ∈ terminal.val ∧
            terminal.val ≠ {who} ∧ pair.1 who < reward terminal who) ∨
        (∃ terminal : {S : Finset ι // S.Nonempty},
          outcome = some terminal ∧ who ∉ terminal.val ∧
            pair.1 who < reward terminal who)) := by
  obtain ⟨profiles, quitTime, mass, subseq, outcome, hprofiles, hmass,
      hsubseq, hmassLimit, hpayoff, hreset, houtcomeMass, hpersistent, halt⟩ :=
    exists_persistent_profitableAtom_of_allContinueSemanticPlateau
      reward pair hpair hnash who hpositive hM hreward
  refine ⟨profiles, quitTime, mass, subseq, outcome, hprofiles, hmass,
    hsubseq, hmassLimit, hpayoff, hreset, houtcomeMass, hpersistent, ?_⟩
  rcases halt with ⟨rfl, hnegative⟩ | ⟨terminal, rfl, hterminalNe, hgain⟩
  · left
    refine ⟨rfl, hnegative, ?_⟩
    exact eventually_quitTime_eq_none_of_persistent_neverMass reward
      (fun n => profiles (subseq n)) who (fun n => quitTime (subseq n))
      (mass none / 2) (half_pos houtcomeMass) hpersistent
  · by_cases hmem : who ∈ terminal.val
    · exact Or.inr (Or.inl
        ⟨terminal, rfl, hmem, hterminalNe, hgain⟩)
    · exact Or.inr (Or.inr
        ⟨terminal, rfl, hmem, hgain⟩)

end GameTheory
