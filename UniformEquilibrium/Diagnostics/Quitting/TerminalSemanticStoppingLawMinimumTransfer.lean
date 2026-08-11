/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStoppingLawDebtConvexity
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauPartialResetTransfer

/-!
# Cutoff-free stopping-law transfer at a minimum-debt profile

A complete stopping-law half reset of any positive debtor has a gain bounded
below by one quarter of that debt and retains half of every selected finite
coalition window.  At a minimum or near-minimum total-debt profile, the exact
decrease of the mover's debt must be transferred to the opposite player face.

The resulting transfer, chronological retention, and coordinatewise debt
chord all belong to the same literal mixed profile.  This removes the cutoff
dilution of a reset chosen from one profitable row.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Near-minimum cutoff-free transfer.**  Half-mix one positive debtor's
complete stopping law with an approximate best response.  The same literal
mixed profile:

* gains at least one quarter of the source debt;
* decreases the mover's debt by exactly that gain;
* transfers the gain, up to the near-minimum error, to the opposite face;
* stays coordinatewise below the debt chord to the best-response endpoint;
* retains half of any prescribed finite coalition window.
-/
theorem exists_halfStoppingLawReset_nearMinimum_transfer_and_windowRetention
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (terminal : {S : Finset ι // S.Nonempty}) (cutoff : ℕ)
    (epsilon : ℝ)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ outcome player, |reward outcome player| ≤ M)
    (hwhoDebt : 0 < quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) who)
    (hnear : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward profile) ≤
        quittingTerminalSemanticDebtSum candidate + epsilon) :
    ∃ bestResponse : (quittingGame reward).BehaviorStrategy who,
      let endpointProfile := Function.update profile who bestResponse
      let mixedStrategy := quittingStoppingLawMixtureBehaviorStrategy
        reward who (profile who) bestResponse (1 / 2) (by norm_num) (by norm_num)
      let mixedProfile := Function.update profile who mixedStrategy
      let source := quittingTerminalSemanticPair reward profile
      let endpoint := quittingTerminalSemanticPair reward endpointProfile
      let target := quittingTerminalSemanticPair reward mixedProfile
      let gain := quittingTerminalPayoff reward mixedProfile who -
        quittingTerminalPayoff reward profile who
      target ∈ quittingTerminalSemanticCarrier reward ∧
      quittingTerminalSemanticDebt source who / 4 ≤ gain ∧
      0 < gain ∧
      quittingTerminalSemanticDebt target who =
        quittingTerminalSemanticDebt source who - gain ∧
      gain ≤ epsilon + ∑ other ∈ Finset.univ.erase who,
        quittingTerminalSemanticDebtChange source target other ∧
      (∀ observer,
        quittingTerminalSemanticDebt target observer ≤
          (1 / 2) * quittingTerminalSemanticDebt source observer +
            (1 / 2) * quittingTerminalSemanticDebt endpoint observer) ∧
      (1 / 2) *
          (∑ time ∈ Finset.range cutoff,
            quittingStageCoalitionMass reward profile time terminal) ≤
        ∑ time ∈ Finset.range cutoff,
          quittingStageCoalitionMass reward mixedProfile time terminal := by
  let source := quittingTerminalSemanticPair reward profile
  let error := quittingTerminalSemanticDebt source who / 2
  have herror : 0 < error := by
    dsimp only [error]
    linarith
  obtain ⟨bestResponse, _hlaw, hgainLower, _hdebtExact, _hdebtUpper,
      hwindow⟩ :=
    exists_stoppingLawMixture_debtContraction_and_windowRetention
      reward profile who terminal cutoff (1 / 2) error
        (by norm_num) (by norm_num) herror hM hreward
  refine ⟨bestResponse, ?_⟩
  dsimp only
  let endpointProfile := Function.update profile who bestResponse
  let mixedStrategy := quittingStoppingLawMixtureBehaviorStrategy
    reward who (profile who) bestResponse (1 / 2) (by norm_num) (by norm_num)
  let mixedProfile := Function.update profile who mixedStrategy
  let endpoint := quittingTerminalSemanticPair reward endpointProfile
  let target := quittingTerminalSemanticPair reward mixedProfile
  let gain := quittingTerminalPayoff reward mixedProfile who -
    quittingTerminalPayoff reward profile who
  have htarget : target ∈ quittingTerminalSemanticCarrier reward := by
    exact quittingTerminalSemanticPair_mem_carrier reward mixedProfile
  have hgainQuarter : quittingTerminalSemanticDebt source who / 4 ≤ gain := by
    dsimp only [source, error, gain, mixedProfile, mixedStrategy] at hgainLower ⊢
    nlinarith
  have hgainPos : 0 < gain := by
    have hquarterPos : 0 < quittingTerminalSemanticDebt source who / 4 := by
      exact div_pos hwhoDebt (by norm_num)
    exact hquarterPos.trans_le hgainQuarter
  have hdecrease : quittingTerminalSemanticDebt target who =
      quittingTerminalSemanticDebt source who - gain := by
    have henvelope : quittingContinuationBestResponseValue reward mixedProfile who =
        quittingContinuationBestResponseValue reward profile who := by
      dsimp only [mixedProfile]
      exact quittingContinuationBestResponseValue_update_self _ _ _ _
    dsimp only [quittingTerminalSemanticDebt, quittingTerminalSemanticPair,
      target, source, gain] at henvelope ⊢
    linarith
  have htransfer : gain ≤ epsilon + ∑ other ∈ Finset.univ.erase who,
      quittingTerminalSemanticDebtChange source target other :=
    nearMinimumDebt_opponentTransfer_of_coordinateDecrease
      reward source target who gain epsilon hnear htarget hdecrease
  have hchord : ∀ observer,
      quittingTerminalSemanticDebt target observer ≤
        (1 / 2) * quittingTerminalSemanticDebt source observer +
          (1 / 2) * quittingTerminalSemanticDebt endpoint observer := by
    intro observer
    dsimp only [target, source, endpoint, mixedProfile, mixedStrategy,
      endpointProfile]
    have hbound := quittingTerminalSemanticDebt_stoppingLawMixture_le
      reward profile who observer (profile who) bestResponse
        (1 / 2) (by norm_num) (by norm_num) hM hreward
    norm_num at hbound ⊢
    simpa only [Function.update_eq_self] using hbound
  refine ⟨htarget, hgainQuarter, hgainPos, hdecrease, htransfer, hchord, ?_⟩
  norm_num at hwindow ⊢
  exact hwindow

/-- Exact-minimum specialization: a positive debtor produces a strictly
positive aggregate transfer to the opposite face, in the same profile which
retains the selected chronological window. -/
theorem exists_halfStoppingLawReset_minimum_positiveTransfer
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (terminal : {S : Finset ι // S.Nonempty}) (cutoff : ℕ)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ outcome player, |reward outcome player| ≤ M)
    (hwhoDebt : 0 < quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) who)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward profile) ≤
        quittingTerminalSemanticDebtSum candidate) :
    ∃ bestResponse : (quittingGame reward).BehaviorStrategy who,
      let mixedStrategy := quittingStoppingLawMixtureBehaviorStrategy
        reward who (profile who) bestResponse (1 / 2) (by norm_num) (by norm_num)
      let mixedProfile := Function.update profile who mixedStrategy
      let source := quittingTerminalSemanticPair reward profile
      let target := quittingTerminalSemanticPair reward mixedProfile
      (∃ recipient ∈ Finset.univ.erase who,
        0 < quittingTerminalSemanticDebtChange source target recipient) ∧
      0 < ∑ other ∈ Finset.univ.erase who,
          quittingTerminalSemanticDebtChange source target other ∧
      (1 / 2) *
          (∑ time ∈ Finset.range cutoff,
            quittingStageCoalitionMass reward profile time terminal) ≤
        ∑ time ∈ Finset.range cutoff,
          quittingStageCoalitionMass reward mixedProfile time terminal := by
  have hnear : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward profile) ≤
        quittingTerminalSemanticDebtSum candidate + 0 := by
    intro candidate hcandidate
    simpa using hminimum candidate hcandidate
  obtain ⟨bestResponse, _htarget, _hquarter, hgainPos, _hdecrease,
      htransfer, _hchord, hwindow⟩ :=
    exists_halfStoppingLawReset_nearMinimum_transfer_and_windowRetention
      reward profile who terminal cutoff 0 hM hreward hwhoDebt hnear
  refine ⟨bestResponse, ?_⟩
  dsimp only
  have hpositive : 0 < ∑ other ∈ Finset.univ.erase who,
      quittingTerminalSemanticDebtChange
        (quittingTerminalSemanticPair reward profile)
        (quittingTerminalSemanticPair reward
          (Function.update profile who
            (quittingStoppingLawMixtureBehaviorStrategy reward who (profile who)
              bestResponse (1 / 2) (by norm_num) (by norm_num)))) other := by
    linarith
  have hexists : ∃ recipient ∈ Finset.univ.erase who,
      0 < quittingTerminalSemanticDebtChange
        (quittingTerminalSemanticPair reward profile)
        (quittingTerminalSemanticPair reward
          (Function.update profile who
            (quittingStoppingLawMixtureBehaviorStrategy reward who (profile who)
              bestResponse (1 / 2) (by norm_num) (by norm_num)))) recipient := by
    by_contra hnot
    push Not at hnot
    have hnonpos := Finset.sum_nonpos fun recipient hrecipient =>
      hnot recipient hrecipient
    exact (not_le_of_gt hpositive) hnonpos
  exact ⟨hexists, hpositive, hwindow⟩

end GameTheory
