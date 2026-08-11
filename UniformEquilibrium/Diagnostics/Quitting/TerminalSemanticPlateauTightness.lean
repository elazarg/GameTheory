/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticAllContinuePlateau
import UniformEquilibrium.Quitting.Cycles.BehaviorPureTimeExtremality

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
  refine ⟨profiles, quitTime, mass, subseq, outcome, hprofiles, hmass,
    hsubseq, hmassLimit, houtcomeMass, ?_, ?_⟩
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

end GameTheory
