/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPositiveSlopeRectangle
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStoppingLawMinimumTangent

/-!
# A source-active actual-deviation rectangle on a near-minimum reset

This file packages the genuinely new part of the answer to Question 182.  A
near-minimum complete-law reset does not merely create an unlabelled debt
recipient.  One recipient and one actual behavioral deviation can be selected
so that the same deviation is approximately optimal at the mixed point, its
gain is exactly affine between the source and full endpoint, and its endpoint
rectangle retains the quantitative transferred charge.  The deviation is
also approximately active already at the source.

This removes the separately supplied observer, positive-slope, and
approximate-response hypotheses from the input of the positive-slope
rectangle interface.  It does not solve the remaining zero-source-gain seam:
the source activity estimate is relative to the recipient's source debt.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A near-minimum reset selects one opponent and one actual behavioral
deviation carrying the reset charge on both faces.

`endpointMoverGain` is the mover's payoff gain under the full reset.  The
strict scale assumption says that this gain, at the chosen reset weight,
dominates the source's near-minimum error.  The selected deviation is
`eta`-optimal at the mixed profile.  Its gain is exactly affine on the reset
edge; its full-endpoint minus source gain satisfies the quantitative
rectangle estimate from Question 182; and at the source it loses at most
`8 * M * lambda + eta` relative to the recipient's full behavioral debt.

No best response is assumed to be attained. -/
theorem exists_nearMinimumReset_actualDeviation_affineRectangle_sourceActive
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover : ι) (target : (quittingGame reward).BehaviorStrategy mover)
    (lambda epsilon eta : ℝ)
    (hlambda0 : 0 < lambda) (hlambda1 : lambda ≤ 1) (heta : 0 < eta)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hnear : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward profile) ≤
        quittingTerminalSemanticDebtSum candidate + epsilon)
    (hscale : epsilon < lambda *
      (quittingTerminalPayoff reward (Function.update profile mover target) mover -
        quittingTerminalPayoff reward profile mover)) :
    ∃ recipient ∈ Finset.univ.erase mover,
      ∃ deviation : (quittingGame reward).BehaviorStrategy recipient,
        let endpointProfile := Function.update profile mover target
        let mixedStrategy := quittingStoppingLawMixtureBehaviorStrategy reward
          mover (profile mover) target lambda hlambda0.le hlambda1
        let mixedProfile := Function.update profile mover mixedStrategy
        let endpointMoverGain := quittingTerminalPayoff reward endpointProfile mover -
          quittingTerminalPayoff reward profile mover
        let sourceGain := quittingTerminalPayoff reward
            (Function.update profile recipient deviation) recipient -
          quittingTerminalPayoff reward profile recipient
        let mixedGain := quittingTerminalPayoff reward
            (Function.update mixedProfile recipient deviation) recipient -
          quittingTerminalPayoff reward mixedProfile recipient
        let endpointGain := quittingTerminalPayoff reward
            (Function.update endpointProfile recipient deviation) recipient -
          quittingTerminalPayoff reward endpointProfile recipient
        let opponentCount : ℝ := (Finset.univ.erase mover).card
        quittingContinuationBestResponseValue reward mixedProfile recipient - eta ≤
            quittingTerminalPayoff reward
              (Function.update mixedProfile recipient deviation) recipient ∧
          mixedGain = (1 - lambda) * sourceGain + lambda * endpointGain ∧
          endpointMoverGain / opponentCount -
                epsilon / (lambda * opponentCount) - eta / lambda ≤
            endpointGain - sourceGain ∧
          quittingTerminalSemanticDebt
                (quittingTerminalSemanticPair reward profile) recipient -
              8 * M * lambda - eta ≤ sourceGain := by
  let endpointProfile := Function.update profile mover target
  let mixedStrategy := quittingStoppingLawMixtureBehaviorStrategy reward mover
    (profile mover) target lambda hlambda0.le hlambda1
  let mixedProfile := Function.update profile mover mixedStrategy
  let source := quittingTerminalSemanticPair reward profile
  let mixed := quittingTerminalSemanticPair reward mixedProfile
  let endpointMoverGain := quittingTerminalPayoff reward endpointProfile mover -
    quittingTerminalPayoff reward profile mover
  let debtChange : ι → ℝ := fun recipient =>
    quittingTerminalSemanticDebtChange source mixed recipient
  let opponents := Finset.univ.erase mover
  have htarget : mixed ∈ quittingTerminalSemanticCarrier reward :=
    quittingTerminalSemanticPair_mem_carrier reward mixedProfile
  have hendpointDebt : quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward endpointProfile) mover =
      quittingTerminalSemanticDebt source mover - endpointMoverGain := by
    dsimp only [endpointProfile, endpointMoverGain, source,
      quittingTerminalSemanticDebt, quittingTerminalSemanticPair]
    rw [quittingContinuationBestResponseValue_update_self]
    ring
  have hmoverDecrease : quittingTerminalSemanticDebt mixed mover =
      quittingTerminalSemanticDebt source mover - lambda * endpointMoverGain := by
    have haffine := quittingTerminalSemanticDebt_stoppingLawMixture_eq_self
      reward profile mover (profile mover) target lambda hlambda0.le hlambda1
    rw [Function.update_eq_self] at haffine
    change quittingTerminalSemanticDebt mixed mover =
        (1 - lambda) * quittingTerminalSemanticDebt source mover +
          lambda * quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward endpointProfile) mover at haffine
    rw [hendpointDebt] at haffine
    linarith
  have htransfer : lambda * endpointMoverGain ≤ epsilon +
      ∑ recipient ∈ opponents, debtChange recipient := by
    exact nearMinimumDebt_opponentTransfer_of_coordinateDecrease reward source
      mixed mover (lambda * endpointMoverGain) epsilon hnear htarget
        hmoverDecrease
  have haggregatePositive : 0 < lambda * endpointMoverGain - epsilon := by
    dsimp only [endpointMoverGain] at hscale ⊢
    linarith
  have hopponents : opponents.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at htransfer
    simp at htransfer
    linarith
  obtain ⟨recipient, hrecipient, hrecipientMax⟩ :=
    Finset.exists_max_image opponents debtChange hopponents
  have hsumLe : (∑ other ∈ opponents, debtChange other) ≤
      (opponents.card : ℝ) * debtChange recipient := by
    have hbound := opponents.sum_le_card_nsmul debtChange
      (debtChange recipient) (fun other hother => hrecipientMax other hother)
    simpa [nsmul_eq_mul, mul_comm] using hbound
  have hcardPositive : 0 < (opponents.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hopponents
  have hrise :
      (lambda * endpointMoverGain - epsilon) / (opponents.card : ℝ) ≤
        debtChange recipient := by
    apply (div_le_iff₀ hcardPositive).2
    linarith
  have hne : recipient ≠ mover := by
    simpa only [opponents, Finset.mem_erase, Finset.mem_univ, and_true] using
      hrecipient
  obtain ⟨deviation, hdeviation⟩ :=
    exists_quittingContinuation_deviation_ge_sub reward mixedProfile recipient
      heta hM hreward
  refine ⟨recipient, ?_, deviation, ?_⟩
  · simpa only [opponents] using hrecipient
  dsimp only
  let sourceGain := quittingTerminalPayoff reward
      (Function.update profile recipient deviation) recipient -
    quittingTerminalPayoff reward profile recipient
  let mixedGain := quittingTerminalPayoff reward
      (Function.update mixedProfile recipient deviation) recipient -
    quittingTerminalPayoff reward mixedProfile recipient
  let endpointGain := quittingTerminalPayoff reward
      (Function.update endpointProfile recipient deviation) recipient -
    quittingTerminalPayoff reward endpointProfile recipient
  have hsourceAffine := quittingTerminalPayoff_stoppingLawMixture_eq reward
    profile mover recipient (profile mover) target lambda hlambda0.le hlambda1
  rw [Function.update_eq_self] at hsourceAffine
  have hdeviationAffine := quittingTerminalPayoff_stoppingLawMixture_eq reward
    (Function.update profile recipient deviation) mover recipient (profile mover)
      target lambda hlambda0.le hlambda1
  have hsourceMover :
      Function.update profile recipient deviation mover = profile mover := by
    rw [Function.update_of_ne (Ne.symm hne)]
  have hsourceUpdate :
      Function.update (Function.update profile recipient deviation) mover
          (profile mover) = Function.update profile recipient deviation := by
    rw [← hsourceMover, Function.update_eq_self]
  have hcommuteMixed :
      Function.update (Function.update profile recipient deviation) mover
          mixedStrategy = Function.update mixedProfile recipient deviation :=
    Function.update_comm hne deviation mixedStrategy profile
  have hcommuteEndpoint :
      Function.update (Function.update profile recipient deviation) mover target =
        Function.update endpointProfile recipient deviation :=
    Function.update_comm hne deviation target profile
  rw [hcommuteMixed, hsourceUpdate, hcommuteEndpoint] at hdeviationAffine
  have hgainAffine : mixedGain =
      (1 - lambda) * sourceGain + lambda * endpointGain := by
    dsimp only [sourceGain, mixedGain, endpointGain, mixedProfile, mixedStrategy,
      endpointProfile] at hsourceAffine hdeviationAffine ⊢
    linarith
  have hsourceCap :=
    quittingTerminalPayoff_update_le_continuationBestResponseValue reward
      profile recipient deviation hM hreward
  have hmixedDebtLower :
      quittingTerminalSemanticDebt mixed recipient - eta ≤ mixedGain := by
    dsimp only [mixed, mixedGain, quittingTerminalSemanticDebt,
      quittingTerminalSemanticPair]
    linarith
  have hsourceGainUpper : sourceGain ≤
      quittingTerminalSemanticDebt source recipient := by
    dsimp only [sourceGain, source, quittingTerminalSemanticDebt,
      quittingTerminalSemanticPair]
    linarith
  have hscaledRectangle :
      (lambda * endpointMoverGain - epsilon) / (opponents.card : ℝ) - eta ≤
        lambda * (endpointGain - sourceGain) := by
    have hdebtRise :
        (lambda * endpointMoverGain - epsilon) / (opponents.card : ℝ) ≤
          quittingTerminalSemanticDebt mixed recipient -
            quittingTerminalSemanticDebt source recipient := by
      simpa only [debtChange, quittingTerminalSemanticDebtChange] using hrise
    rw [hgainAffine] at hmixedDebtLower
    linarith
  have hrectangle : endpointMoverGain / (opponents.card : ℝ) -
          epsilon / (lambda * (opponents.card : ℝ)) - eta / lambda ≤
        endpointGain - sourceGain := by
    have hdivided :
        ((lambda * endpointMoverGain - epsilon) /
              (opponents.card : ℝ) - eta) / lambda ≤
            endpointGain - sourceGain :=
      (div_le_iff₀ hlambda0).2 (by
        simpa only [mul_comm] using hscaledRectangle)
    calc
      endpointMoverGain / (opponents.card : ℝ) -
            epsilon / (lambda * (opponents.card : ℝ)) - eta / lambda =
          ((lambda * endpointMoverGain - epsilon) /
              (opponents.card : ℝ) - eta) / lambda := by
            field_simp
      _ ≤ endpointGain - sourceGain := hdivided
  have hdebtVariation :=
    abs_quittingTerminalSemanticDebt_stoppingLawMixture_sub_le reward profile
      mover recipient target lambda hlambda0.le hlambda1 hM hreward
  have hmixedDebtSourceLower :
      quittingTerminalSemanticDebt source recipient - 4 * M * lambda ≤
        quittingTerminalSemanticDebt mixed recipient := by
    dsimp only [source, mixed, mixedProfile, mixedStrategy] at hdebtVariation ⊢
    rw [abs_le] at hdebtVariation
    linarith
  have hsourcePrescribedAbs :=
    abs_quittingTerminalPayoff_le reward profile recipient hM hreward
  have hsourceDeviationAbs := abs_quittingTerminalPayoff_le reward
    (Function.update profile recipient deviation) recipient hM hreward
  have hendpointPrescribedAbs := abs_quittingTerminalPayoff_le reward
    endpointProfile recipient hM hreward
  have hendpointDeviationAbs := abs_quittingTerminalPayoff_le reward
    (Function.update endpointProfile recipient deviation) recipient hM hreward
  rw [abs_le] at hsourcePrescribedAbs hsourceDeviationAbs
  rw [abs_le] at hendpointPrescribedAbs hendpointDeviationAbs
  have hgainDifferenceUpper : endpointGain - sourceGain ≤ 4 * M := by
    dsimp only [endpointGain, sourceGain]
    linarith
  have hmixed_sub_source_le : mixedGain - sourceGain ≤ 4 * M * lambda := by
    rw [hgainAffine]
    have hscaled := mul_le_mul_of_nonneg_left hgainDifferenceUpper hlambda0.le
    linarith
  have hsourceActive :
      quittingTerminalSemanticDebt source recipient - 8 * M * lambda - eta ≤
        sourceGain := by
    linarith
  refine ⟨?_, hgainAffine, ?_, ?_⟩
  · simpa only [mixedProfile] using hdeviation
  · simpa only [endpointMoverGain, endpointGain, sourceGain, opponents] using
      hrectangle
  · simpa only [source, sourceGain] using hsourceActive

end GameTheory
