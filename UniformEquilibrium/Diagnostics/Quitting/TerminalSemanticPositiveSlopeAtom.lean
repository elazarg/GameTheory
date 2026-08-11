/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticEndpointDefectPolarity
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStoppingLawDebtConvexity

/-!
# Terminal atoms exposed by a positive stopping-law debt slope

A positive debt slope along one complete stopping-law mixture is not itself
an incidence label: another player's debt may rise because its prescribed
payoff falls or because its behavioral best-response envelope rises.  This
file keeps that distinction exact.

For a fixed observer, debt convexity first transports a positive slope from
the mixed profile to the full endpoint chord.  Splitting `debt = cap - payoff`
then gives two alternatives.

* In the payoff branch, one terminal outcome carries a positive signed
  contribution to the prescribed-law change.
* In the cap branch, choose one approximate best response at the endpoint
  and use that same deviation at the source.  One terminal outcome then
  carries a positive signed contribution to this two-deviation rectangle.

Both atoms use literal terminal laws of the displayed profiles.  The cap
branch is deliberately not called a coalition insertion toggle: turning its
four-profile terminal-law cross-effect into one state-matched root toggle is
a further chronological theorem.
-/

noncomputable section

namespace GameTheory

open Set StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Signed contribution of one terminal outcome to the payoff difference
between two literal profiles. -/
def quittingTerminalPayoffDifferenceAtom
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : (quittingGame reward).BehaviorProfile)
    (observer : ι) (outcome : QuittingTerminalOutcome ι) : ℝ :=
  (quittingTerminalOutcomeMass reward first outcome -
      quittingTerminalOutcomeMass reward second outcome) *
    quittingTerminalOutcomeReward reward outcome observer

omit [DecidableEq ι] in
/-- The signed terminal atoms sum exactly to the corresponding payoff
difference. -/
theorem sum_quittingTerminalPayoffDifferenceAtom
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : (quittingGame reward).BehaviorProfile)
    (observer : ι) :
    (∑ outcome : QuittingTerminalOutcome ι,
        quittingTerminalPayoffDifferenceAtom reward first second observer
          outcome) =
      quittingTerminalPayoff reward first observer -
        quittingTerminalPayoff reward second observer := by
  rw [← quittingTerminalRewardMoment_outcomeMass reward first,
    ← quittingTerminalRewardMoment_outcomeMass reward second]
  unfold quittingTerminalRewardMoment quittingTerminalPayoffDifferenceAtom
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro outcome _
  ring

omit [DecidableEq ι] in
/-- A positive literal payoff difference exposes one signed terminal outcome
atom, with only the finite outcome-cardinality loss. -/
theorem exists_terminalPayoffDifferenceAtom
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : (quittingGame reward).BehaviorProfile)
    (observer : ι) (charge : ℝ)
    (hcharge : charge ≤ quittingTerminalPayoff reward first observer -
      quittingTerminalPayoff reward second observer) :
    ∃ outcome : QuittingTerminalOutcome ι,
      charge ≤ (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
        quittingTerminalPayoffDifferenceAtom reward first second observer
          outcome := by
  let outcomes := (Finset.univ : Finset (QuittingTerminalOutcome ι))
  have houtcomes : outcomes.Nonempty := Finset.univ_nonempty
  obtain ⟨outcome, _houtcome, houtcomeMax⟩ :=
    Finset.exists_max_image outcomes
      (quittingTerminalPayoffDifferenceAtom reward first second observer)
      houtcomes
  refine ⟨outcome, hcharge.trans ?_⟩
  rw [← sum_quittingTerminalPayoffDifferenceAtom reward first second observer]
  have hsum := outcomes.sum_le_card_nsmul
    (quittingTerminalPayoffDifferenceAtom reward first second observer)
    (quittingTerminalPayoffDifferenceAtom reward first second observer outcome)
    (fun other hother ↦ houtcomeMax other hother)
  simpa [outcomes, nsmul_eq_mul, mul_comm] using hsum

omit [DecidableEq ι] in
/-- A strictly positive payoff difference is carried by an absorbing
coalition, never by the zero-reward `Never` outcome. -/
theorem exists_absorbingTerminalPayoffDifferenceAtom
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : (quittingGame reward).BehaviorProfile)
    (observer : ι) (charge : ℝ) (hchargePositive : 0 < charge)
    (hcharge : charge ≤ quittingTerminalPayoff reward first observer -
      quittingTerminalPayoff reward second observer) :
    ∃ terminal : {S : Finset ι // S.Nonempty},
      charge ≤ (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
        quittingTerminalPayoffDifferenceAtom reward first second observer
          (some terminal) := by
  obtain ⟨outcome, houtcome⟩ := exists_terminalPayoffDifferenceAtom
    reward first second observer charge hcharge
  cases outcome with
  | none =>
      simp [quittingTerminalPayoffDifferenceAtom,
        quittingTerminalOutcomeReward] at houtcome
      linarith
  | some terminal => exact ⟨terminal, houtcome⟩

/-- **Coordinate positive-slope decoder.**

Suppose one observer's debt rises at normalized rate at least `charge` along
one complete stopping-law mixture.  Then either a prescribed terminal-law
atom carries half that charge, or one fixed approximate endpoint best
response produces a two-deviation terminal-law atom carrying one quarter.

The same source, endpoint, mixture, observer, and (in the second branch) the
same literal deviation occur throughout. -/
theorem exists_prescribedAtom_or_deviationRectangleAtom_of_stoppingLawDebtSlope
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι)
    (target : (quittingGame reward).BehaviorStrategy mover)
    (lambda charge : ℝ) (hlambda0 : 0 < lambda) (hlambda1 : lambda ≤ 1)
    (hcharge : 0 < charge)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hslope : lambda * charge ≤
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update profile mover
              (quittingStoppingLawMixtureBehaviorStrategy reward mover
                (profile mover) target lambda hlambda0.le hlambda1))) observer -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) observer) :
    (∃ terminal : {S : Finset ι // S.Nonempty},
      charge / 2 ≤
        (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
          quittingTerminalPayoffDifferenceAtom reward profile
            (Function.update profile mover target) observer (some terminal)) ∨
    ∃ deviation : (quittingGame reward).BehaviorStrategy observer,
      ∃ terminal : {S : Finset ι // S.Nonempty},
        charge / 4 ≤
          (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
            quittingTerminalPayoffDifferenceAtom reward
              (Function.update (Function.update profile mover target)
                observer deviation)
              (Function.update profile observer deviation) observer
                (some terminal) := by
  let endpoint := Function.update profile mover target
  let mixed := Function.update profile mover
    (quittingStoppingLawMixtureBehaviorStrategy reward mover
      (profile mover) target lambda hlambda0.le hlambda1)
  let sourcePair := quittingTerminalSemanticPair reward profile
  let endpointPair := quittingTerminalSemanticPair reward endpoint
  let mixedPair := quittingTerminalSemanticPair reward mixed
  have hchord := quittingTerminalSemanticDebt_stoppingLawMixture_le
    reward profile mover observer (profile mover) target lambda hlambda0.le
      hlambda1 hM hreward
  rw [Function.update_eq_self] at hchord
  change quittingTerminalSemanticDebt mixedPair observer ≤
      (1 - lambda) * quittingTerminalSemanticDebt sourcePair observer +
        lambda * quittingTerminalSemanticDebt endpointPair observer at hchord
  have hendpointSlope : charge ≤
      quittingTerminalSemanticDebt endpointPair observer -
        quittingTerminalSemanticDebt sourcePair observer := by
    change lambda * charge ≤
      quittingTerminalSemanticDebt mixedPair observer -
        quittingTerminalSemanticDebt sourcePair observer at hslope
    have hscaled : lambda * charge ≤ lambda *
        (quittingTerminalSemanticDebt endpointPair observer -
          quittingTerminalSemanticDebt sourcePair observer) := by
      nlinarith
    nlinarith
  let sourceCap := quittingContinuationBestResponseValue reward profile observer
  let endpointCap := quittingContinuationBestResponseValue reward endpoint observer
  let sourcePayoff := quittingTerminalPayoff reward profile observer
  let endpointPayoff := quittingTerminalPayoff reward endpoint observer
  have hsplit : charge ≤
      (endpointCap - sourceCap) + (sourcePayoff - endpointPayoff) := by
    dsimp only [sourcePair, endpointPair, quittingTerminalSemanticDebt,
      quittingTerminalSemanticPair] at hendpointSlope
    dsimp only [sourceCap, endpointCap, sourcePayoff, endpointPayoff]
    linarith
  by_cases hpayoff : charge / 2 ≤ sourcePayoff - endpointPayoff
  · exact Or.inl (exists_absorbingTerminalPayoffDifferenceAtom reward profile
      endpoint observer (charge / 2) (by positivity) hpayoff)
  · right
    have hcap : charge / 2 < endpointCap - sourceCap := by
      linarith
    have herror : 0 < charge / 4 := by positivity
    obtain ⟨deviation, hdeviation⟩ :=
      exists_quittingContinuation_deviation_ge_sub reward endpoint observer
        herror hM hreward
    have hsourceBound :=
      quittingTerminalPayoff_update_le_continuationBestResponseValue
        reward profile observer deviation hM hreward
    have hrectangle : charge / 4 ≤
        quittingTerminalPayoff reward
            (Function.update endpoint observer deviation) observer -
          quittingTerminalPayoff reward
            (Function.update profile observer deviation) observer := by
      dsimp only [endpointCap, sourceCap] at hcap
      dsimp only [endpoint] at hdeviation ⊢
      linarith
    refine ⟨deviation, exists_absorbingTerminalPayoffDifferenceAtom reward
      (Function.update endpoint observer deviation)
      (Function.update profile observer deviation) observer (charge / 4)
      herror hrectangle⟩

/-- **Total positive-slope decoder.**

If the total debt rises at rate `sigma` while the mover's own coordinate is
consumed at rate `gain`, one fixed opponent receives at least the average
rate `(sigma + gain) / card (univ.erase mover)`.  The coordinate decoder then
exposes either a prescribed-law terminal atom or a same-deviation terminal
rectangle atom at that quantitative scale.

In particular, the selected atom is not obtained from an independently
chosen semantic or law point.  Every profile in the conclusion is one of the
literal source/endpoint profiles of the reset, possibly updated by the one
displayed opponent deviation. -/
theorem exists_opponent_prescribedAtom_or_deviationRectangleAtom_of_totalSlope
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover : ι) (target : (quittingGame reward).BehaviorStrategy mover)
    (lambda sigma gain : ℝ) (hlambda0 : 0 < lambda) (hlambda1 : lambda ≤ 1)
    (hsigma : 0 < sigma) (hgain : 0 ≤ gain)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (htotalSlope : lambda * sigma ≤
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (Function.update profile mover
              (quittingStoppingLawMixtureBehaviorStrategy reward mover
                (profile mover) target lambda hlambda0.le hlambda1))) -
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward profile))
    (hmover : quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update profile mover
              (quittingStoppingLawMixtureBehaviorStrategy reward mover
                (profile mover) target lambda hlambda0.le hlambda1))) mover =
        quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward profile) mover -
          lambda * gain) :
    ∃ observer ∈ Finset.univ.erase mover,
      let charge :=
        (sigma + gain) / ((Finset.univ.erase mover).card : ℝ)
      (∃ terminal : {S : Finset ι // S.Nonempty},
        charge / 2 ≤
          (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
            quittingTerminalPayoffDifferenceAtom reward profile
              (Function.update profile mover target) observer
                (some terminal)) ∨
      ∃ deviation : (quittingGame reward).BehaviorStrategy observer,
        ∃ terminal : {S : Finset ι // S.Nonempty},
          charge / 4 ≤
            (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
              quittingTerminalPayoffDifferenceAtom reward
                (Function.update (Function.update profile mover target)
                  observer deviation)
                (Function.update profile observer deviation) observer
                  (some terminal) := by
  let mixed := Function.update profile mover
    (quittingStoppingLawMixtureBehaviorStrategy reward mover
      (profile mover) target lambda hlambda0.le hlambda1)
  let sourcePair := quittingTerminalSemanticPair reward profile
  let mixedPair := quittingTerminalSemanticPair reward mixed
  let debtChange : ι → ℝ := fun observer =>
    quittingTerminalSemanticDebt mixedPair observer -
      quittingTerminalSemanticDebt sourcePair observer
  have htotalChange : (∑ observer, debtChange observer) =
      quittingTerminalSemanticDebtSum mixedPair -
        quittingTerminalSemanticDebtSum sourcePair := by
    unfold debtChange quittingTerminalSemanticDebtSum
    rw [Finset.sum_sub_distrib]
  have hmoverChange : debtChange mover = -(lambda * gain) := by
    dsimp only [debtChange, mixedPair, sourcePair, mixed] at hmover ⊢
    rw [hmover]
    ring
  have hsplit := Finset.sum_erase_add Finset.univ debtChange
    (Finset.mem_univ mover)
  have hopponentLower : lambda * (sigma + gain) ≤
      ∑ observer ∈ Finset.univ.erase mover, debtChange observer := by
    change lambda * sigma ≤
      quittingTerminalSemanticDebtSum mixedPair -
        quittingTerminalSemanticDebtSum sourcePair at htotalSlope
    rw [← htotalChange, ← hsplit, hmoverChange] at htotalSlope
    linarith
  have hpositiveScale : 0 < lambda * (sigma + gain) := by
    exact mul_pos hlambda0 (by linarith)
  have hopponents : (Finset.univ.erase mover).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at hopponentLower
    simp at hopponentLower
    linarith
  obtain ⟨observer, hobserver, hobserverMax⟩ :=
    Finset.exists_max_image (Finset.univ.erase mover) debtChange hopponents
  have hsumLe : (∑ other ∈ Finset.univ.erase mover, debtChange other) ≤
      ((Finset.univ.erase mover).card : ℝ) * debtChange observer := by
    have hbound := (Finset.univ.erase mover).sum_le_card_nsmul debtChange
      (debtChange observer) (fun other hother => hobserverMax other hother)
    simpa [nsmul_eq_mul, mul_comm] using hbound
  have hcardPositive : 0 < ((Finset.univ.erase mover).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hopponents
  let charge := (sigma + gain) /
    ((Finset.univ.erase mover).card : ℝ)
  have hchargePositive : 0 < charge := by
    exact div_pos (by linarith) hcardPositive
  have hobserverSlope : lambda * charge ≤ debtChange observer := by
    dsimp only [charge]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hcardPositive).2
    nlinarith
  have hdecoded :=
    exists_prescribedAtom_or_deviationRectangleAtom_of_stoppingLawDebtSlope
      reward profile mover observer target lambda charge hlambda0 hlambda1
        hchargePositive hM hreward (by
          dsimp only [debtChange, mixedPair, sourcePair, mixed] at hobserverSlope
          exact hobserverSlope)
  exact ⟨observer, hobserver, hdecoded⟩

end GameTheory
