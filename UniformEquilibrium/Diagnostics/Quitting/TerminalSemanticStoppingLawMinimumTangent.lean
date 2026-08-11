/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStoppingLawMinimumTransfer

/-!
# Exact stopping-law reset rays at a minimum-debt profile

At an exact minimum of total best-response debt, a positive debtor has a
single approximate-best-response endpoint whose complete stopping-law chord
is strategic at every scale.  Along that common-base ray:

* the mover's payoff gain and debt loss are exactly linear in the scale;
* global minimality transfers at least the same amount to the other debt
  coordinates;
* every debt coordinate lies below its endpoint chord;
* every finite chronological coalition window retains its old
  `1 - lambda` fraction.

This is stronger than selecting unrelated half resets: the same endpoint
works for arbitrarily small scales and all rays start at the same literal
profile.  It is consequently an honest tangent-family input.  No recurrence
claim is made here.  In particular, a cycle among selected player labels is
not by itself a cycle of semantic states.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The behavioral best-response envelope is one-sided Lipschitz under a
complete stopping-law mixture of one opponent.  The estimate is also valid
when mover and observer coincide, in which case the envelope is constant. -/
theorem quittingContinuationBestResponseValue_source_sub_stoppingLawMixture_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι)
    (target : (quittingGame reward).BehaviorStrategy mover)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    quittingContinuationBestResponseValue reward profile observer -
        quittingContinuationBestResponseValue reward
          (Function.update profile mover
            (quittingStoppingLawMixtureBehaviorStrategy reward mover
              (profile mover) target lambda hlambda0 hlambda1)) observer ≤
      2 * M * lambda := by
  by_cases hsame : observer = mover
  · subst observer
    rw [quittingContinuationBestResponseValue_update_self]
    nlinarith
  · let mixedStrategy := quittingStoppingLawMixtureBehaviorStrategy
      reward mover (profile mover) target lambda hlambda0 hlambda1
    let mixedProfile := Function.update profile mover mixedStrategy
    have henvelope : quittingContinuationBestResponseValue reward profile observer ≤
        quittingContinuationBestResponseValue reward mixedProfile observer +
          2 * M * lambda := by
      unfold quittingContinuationBestResponseValue
      apply csSup_le
      · exact Set.range_nonempty _
      rintro payoff ⟨deviation, rfl⟩
      let deviatedSource := Function.update profile observer deviation
      have haffine := quittingTerminalPayoff_stoppingLawMixture_eq
        reward deviatedSource mover observer (profile mover) target
          lambda hlambda0 hlambda1
      have hsourceUpdate :
          Function.update deviatedSource mover (profile mover) =
            Function.update profile observer deviation := by
        have hdeviatedMover : deviatedSource mover = profile mover := by
          dsimp only [deviatedSource]
          rw [Function.update_of_ne (Ne.symm hsame)]
        rw [← hdeviatedMover, Function.update_eq_self]
      have htargetUpdate :
          Function.update deviatedSource mover target =
            Function.update (Function.update profile mover target)
              observer deviation :=
        Function.update_comm hsame deviation target profile
      have hmixedUpdate :
          Function.update deviatedSource mover mixedStrategy =
            Function.update mixedProfile observer deviation := by
        dsimp only [deviatedSource, mixedProfile]
        exact Function.update_comm hsame deviation mixedStrategy profile
      change quittingTerminalPayoff reward
          (Function.update deviatedSource mover mixedStrategy) observer = _
        at haffine
      rw [hmixedUpdate, hsourceUpdate, htargetUpdate] at haffine
      have hsourceAbs := abs_quittingTerminalPayoff_le reward
        (Function.update profile observer deviation) observer hM hreward
      have htargetAbs := abs_quittingTerminalPayoff_le reward
        (Function.update (Function.update profile mover target)
          observer deviation) observer hM hreward
      have hdifference : quittingTerminalPayoff reward
            (Function.update profile observer deviation) observer -
          quittingTerminalPayoff reward
            (Function.update (Function.update profile mover target)
              observer deviation) observer ≤ 2 * M := by
        rw [abs_le] at hsourceAbs htargetAbs
        linarith
      have hscaled := mul_le_mul_of_nonneg_left hdifference hlambda0
      have hmixedLe :=
        quittingTerminalPayoff_update_le_continuationBestResponseValue
          reward mixedProfile observer deviation hM hreward
      have hscaled' : lambda *
            (quittingTerminalPayoff reward
                (Function.update profile observer deviation) observer -
              quittingTerminalPayoff reward
                (Function.update (Function.update profile mover target)
                  observer deviation) observer) ≤
          2 * M * lambda := by
        calc
          _ ≤ lambda * (2 * M) := hscaled
          _ = 2 * M * lambda := by ring
      calc
        quittingTerminalPayoff reward
            (Function.update profile observer deviation) observer =
          quittingTerminalPayoff reward
              (Function.update mixedProfile observer deviation) observer +
            lambda *
              (quittingTerminalPayoff reward
                  (Function.update profile observer deviation) observer -
                quittingTerminalPayoff reward
                  (Function.update (Function.update profile mover target)
                    observer deviation) observer) := by
              rw [haffine]
              ring
        _ ≤ quittingTerminalPayoff reward
              (Function.update mixedProfile observer deviation) observer +
            2 * M * lambda := by
              simpa only [add_comm] using
                add_le_add_left hscaled'
                  (quittingTerminalPayoff reward
                    (Function.update mixedProfile observer deviation) observer)
        _ ≤ quittingContinuationBestResponseValue reward mixedProfile observer +
            2 * M * lambda := by
              simpa only [add_comm] using
                add_le_add_left hmixedLe (2 * M * lambda)
    dsimp only [mixedProfile, mixedStrategy] at henvelope ⊢
    linarith

/-- Every semantic-debt coordinate changes by at most `4 * M * lambda` along
a complete stopping-law ray from its source profile.  This two-sided bound is
the normalization control needed when the source is only an approximate
minimum and `lambda` tends to zero. -/
theorem abs_quittingTerminalSemanticDebt_stoppingLawMixture_sub_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι)
    (target : (quittingGame reward).BehaviorStrategy mover)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    |quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update profile mover
              (quittingStoppingLawMixtureBehaviorStrategy reward mover
                (profile mover) target lambda hlambda0 hlambda1))) observer -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) observer| ≤
      4 * M * lambda := by
  let mixedStrategy := quittingStoppingLawMixtureBehaviorStrategy
    reward mover (profile mover) target lambda hlambda0 hlambda1
  let mixedProfile := Function.update profile mover mixedStrategy
  let endpointProfile := Function.update profile mover target
  let source := quittingTerminalSemanticPair reward profile
  let mixed := quittingTerminalSemanticPair reward mixedProfile
  let endpoint := quittingTerminalSemanticPair reward endpointProfile
  have henvelope :=
    quittingContinuationBestResponseValue_source_sub_stoppingLawMixture_le
      reward profile mover observer target lambda hlambda0 hlambda1 hM hreward
  have hpayoff := quittingTerminalPayoff_stoppingLawMixture_eq
    reward profile mover observer (profile mover) target lambda
      hlambda0 hlambda1
  rw [Function.update_eq_self] at hpayoff
  have hsourcePayoffAbs := abs_quittingTerminalPayoff_le
    reward profile observer hM hreward
  have hendpointPayoffAbs := abs_quittingTerminalPayoff_le
    reward endpointProfile observer hM hreward
  have hpayoffDifference : quittingTerminalPayoff reward endpointProfile observer -
      quittingTerminalPayoff reward profile observer ≤ 2 * M := by
    rw [abs_le] at hsourcePayoffAbs hendpointPayoffAbs
    linarith
  have hpayoffScaled :=
    mul_le_mul_of_nonneg_left hpayoffDifference hlambda0
  have hlower : -(4 * M * lambda) ≤
      quittingTerminalSemanticDebt mixed observer -
        quittingTerminalSemanticDebt source observer := by
    dsimp only [mixed, source, mixedProfile, mixedStrategy,
      quittingTerminalSemanticDebt, quittingTerminalSemanticPair] at henvelope hpayoff ⊢
    ring_nf at hpayoff hpayoffScaled
    linarith
  have hchord := quittingTerminalSemanticDebt_stoppingLawMixture_le
    reward profile mover observer (profile mover) target lambda
      hlambda0 hlambda1 hM hreward
  rw [Function.update_eq_self] at hchord
  have hsourceDebtNonneg : 0 ≤ quittingTerminalSemanticDebt source observer :=
    quittingTerminalDeviationDebt_nonneg reward profile observer hM hreward
  have hendpointEnvelopeAbs := abs_quittingContinuationBestResponseValue_le
    reward endpointProfile observer hM hreward
  have hendpointDebtLe : quittingTerminalSemanticDebt endpoint observer ≤
      2 * M := by
    dsimp only [endpoint, endpointProfile, quittingTerminalSemanticDebt,
      quittingTerminalSemanticPair]
    rw [abs_le] at hendpointEnvelopeAbs hendpointPayoffAbs
    linarith
  have hupper : quittingTerminalSemanticDebt mixed observer -
        quittingTerminalSemanticDebt source observer ≤ 2 * M * lambda := by
    dsimp only [mixed, source, endpoint, mixedProfile, mixedStrategy,
      endpointProfile] at hchord ⊢
    have hscaledSource := mul_nonneg hlambda0 hsourceDebtNonneg
    have hscaledEndpoint :=
      mul_le_mul_of_nonneg_left hendpointDebtLe hlambda0
    nlinarith
  rw [abs_le]
  constructor
  · exact hlower
  · have htwoLeFour : 2 * M * lambda ≤ 4 * M * lambda := by
      have hproduct := mul_nonneg hM hlambda0
      nlinarith
    exact hupper.trans htwoLeFour

/-- **Normalized reset rays from literal near-minimizers.**

One approximate best-response endpoint works at every positive scale.  The
normalized debt-change vector stays in a fixed box, while the transfer carried
by the endpoint's fixed positive support loses only `epsilon / lambda` to
near-minimality.  Thus a sequence with `epsilon / lambda → 0` has the exact
compactness and nonvanishing estimates required for tangent extraction,
without assuming that a literal global minimizer exists. -/
theorem exists_stoppingLawResetRay_nearMinimum_normalizedFixedSupport
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
      let source := quittingTerminalSemanticPair reward profile
      let endpoint := quittingTerminalSemanticPair reward endpointProfile
      let endpointGain := quittingTerminalPayoff reward endpointProfile who -
        quittingTerminalPayoff reward profile who
      let endpointSupport := (Finset.univ.erase who).filter fun recipient ↦
        0 < quittingTerminalSemanticDebtChange source endpoint recipient
      quittingTerminalSemanticDebt source who / 2 ≤ endpointGain ∧
      0 < endpointGain ∧
      ∀ (lambda : ℝ) (hlambdaPos : 0 < lambda) (hlambda1 : lambda ≤ 1),
        let mixedStrategy := quittingStoppingLawMixtureBehaviorStrategy
          reward who (profile who) bestResponse lambda hlambdaPos.le hlambda1
        let mixedProfile := Function.update profile who mixedStrategy
        let target := quittingTerminalSemanticPair reward mixedProfile
        target ∈ quittingTerminalSemanticCarrier reward ∧
        quittingTerminalPayoff reward mixedProfile who -
            quittingTerminalPayoff reward profile who =
          lambda * endpointGain ∧
        quittingTerminalSemanticDebtChange source target who / lambda =
          -endpointGain ∧
        (∀ observer,
          |quittingTerminalSemanticDebtChange source target observer / lambda| ≤
            4 * M) ∧
        endpointGain ≤ epsilon / lambda +
          ∑ recipient ∈ endpointSupport,
            quittingTerminalSemanticDebtChange source target recipient / lambda ∧
        (1 - lambda) *
            (∑ time ∈ Finset.range cutoff,
              quittingStageCoalitionMass reward profile time terminal) ≤
          ∑ time ∈ Finset.range cutoff,
            quittingStageCoalitionMass reward mixedProfile time terminal := by
  let source := quittingTerminalSemanticPair reward profile
  let error := quittingTerminalSemanticDebt source who / 2
  have herror : 0 < error := by
    dsimp only [error]
    linarith
  obtain ⟨bestResponse, hbestResponse⟩ :=
    exists_quittingContinuation_deviation_ge_sub
      reward profile who herror hM hreward
  refine ⟨bestResponse, ?_⟩
  dsimp only
  let endpointProfile := Function.update profile who bestResponse
  let endpoint := quittingTerminalSemanticPair reward endpointProfile
  let endpointGain := quittingTerminalPayoff reward endpointProfile who -
    quittingTerminalPayoff reward profile who
  let endpointSupport := (Finset.univ.erase who).filter fun recipient ↦
    0 < quittingTerminalSemanticDebtChange source endpoint recipient
  have hendpointGain : quittingTerminalSemanticDebt source who / 2 ≤
      endpointGain := by
    dsimp only [source, error, endpointGain, endpointProfile,
      quittingTerminalSemanticDebt, quittingTerminalSemanticPair] at hbestResponse ⊢
    linarith
  have hendpointGainPos : 0 < endpointGain := by
    have hhalfPos : 0 < quittingTerminalSemanticDebt source who / 2 :=
      div_pos hwhoDebt (by norm_num)
    exact hhalfPos.trans_le hendpointGain
  refine ⟨?_, ?_, ?_⟩
  · simpa only [source, endpointGain, endpointProfile] using hendpointGain
  · simpa only [endpointGain, endpointProfile] using hendpointGainPos
  intro lambda hlambdaPos hlambda1
  let mixedStrategy := quittingStoppingLawMixtureBehaviorStrategy
    reward who (profile who) bestResponse lambda hlambdaPos.le hlambda1
  let mixedProfile := Function.update profile who mixedStrategy
  let target := quittingTerminalSemanticPair reward mixedProfile
  have htarget : target ∈ quittingTerminalSemanticCarrier reward :=
    quittingTerminalSemanticPair_mem_carrier reward mixedProfile
  have hgain : quittingTerminalPayoff reward mixedProfile who -
        quittingTerminalPayoff reward profile who = lambda * endpointGain := by
    dsimp only [mixedProfile, mixedStrategy, endpointGain, endpointProfile]
    exact quittingTerminalPayoff_stoppingLawMixture_sub_eq
      reward profile who bestResponse lambda hlambdaPos.le hlambda1 hM hreward
  have hendpointDebt : quittingTerminalSemanticDebt endpoint who =
      quittingTerminalSemanticDebt source who - endpointGain := by
    dsimp only [endpoint, source, endpointGain, endpointProfile,
      quittingTerminalSemanticDebt, quittingTerminalSemanticPair]
    rw [quittingContinuationBestResponseValue_update_self]
    ring
  have hdecrease : quittingTerminalSemanticDebt target who =
      quittingTerminalSemanticDebt source who - lambda * endpointGain := by
    have haffine := quittingTerminalSemanticDebt_stoppingLawMixture_eq_self
      reward profile who (profile who) bestResponse lambda hlambdaPos.le hlambda1
    dsimp only [target, source, endpoint, mixedProfile, mixedStrategy,
      endpointProfile] at haffine ⊢
    rw [Function.update_eq_self] at haffine
    rw [hendpointDebt] at haffine
    dsimp only [endpointGain, endpointProfile] at haffine ⊢
    linarith
  have hwhoNormalized :
      quittingTerminalSemanticDebtChange source target who / lambda =
        -endpointGain := by
    unfold quittingTerminalSemanticDebtChange
    rw [hdecrease]
    field_simp
    ring
  have hnormalizedBound : ∀ observer,
      |quittingTerminalSemanticDebtChange source target observer / lambda| ≤
        4 * M := by
    intro observer
    have hraw := abs_quittingTerminalSemanticDebt_stoppingLawMixture_sub_le
      reward profile who observer bestResponse lambda hlambdaPos.le hlambda1
        hM hreward
    dsimp only [target, source, mixedProfile, mixedStrategy,
      quittingTerminalSemanticDebtChange] at hraw ⊢
    rw [abs_div, abs_of_pos hlambdaPos, div_le_iff₀ hlambdaPos]
    simpa only [mul_assoc] using hraw
  have hchord : ∀ observer,
      quittingTerminalSemanticDebt target observer ≤
        (1 - lambda) * quittingTerminalSemanticDebt source observer +
          lambda * quittingTerminalSemanticDebt endpoint observer := by
    intro observer
    dsimp only [target, source, endpoint, mixedProfile, mixedStrategy,
      endpointProfile]
    have hbound := quittingTerminalSemanticDebt_stoppingLawMixture_le
      reward profile who observer (profile who) bestResponse lambda
        hlambdaPos.le hlambda1 hM hreward
    simpa only [Function.update_eq_self] using hbound
  have htransfer : lambda * endpointGain ≤ epsilon +
      ∑ other ∈ Finset.univ.erase who,
        quittingTerminalSemanticDebtChange source target other :=
    nearMinimumDebt_opponentTransfer_of_coordinateDecrease
      reward source target who (lambda * endpointGain) epsilon
        hnear htarget hdecrease
  have houtside : ∑ recipient ∈
        (Finset.univ.erase who).filter (fun recipient ↦
          ¬ 0 < quittingTerminalSemanticDebtChange source endpoint recipient),
        quittingTerminalSemanticDebtChange source target recipient ≤ 0 := by
    apply Finset.sum_nonpos
    intro recipient hrecipient
    simp only [Finset.mem_filter] at hrecipient
    have hendpointNonpos :
        quittingTerminalSemanticDebtChange source endpoint recipient ≤ 0 :=
      le_of_not_gt hrecipient.2
    have hrecipientChord := hchord recipient
    unfold quittingTerminalSemanticDebtChange at hendpointNonpos ⊢
    nlinarith
  have hpartition := Finset.sum_filter_add_sum_filter_not
    (Finset.univ.erase who)
    (fun recipient ↦
      0 < quittingTerminalSemanticDebtChange source endpoint recipient)
    (fun recipient ↦
      quittingTerminalSemanticDebtChange source target recipient)
  have hsupportTransfer : lambda * endpointGain ≤ epsilon +
      ∑ recipient ∈ endpointSupport,
        quittingTerminalSemanticDebtChange source target recipient := by
    dsimp only [endpointSupport]
    linarith
  have hnormalizedTransfer : endpointGain ≤ epsilon / lambda +
      ∑ recipient ∈ endpointSupport,
        quittingTerminalSemanticDebtChange source target recipient / lambda := by
    rw [← Finset.sum_div, ← add_div]
    exact (le_div_iff₀ hlambdaPos).2 (by
      simpa only [mul_comm] using hsupportTransfer)
  have hwindow : (1 - lambda) *
        (∑ time ∈ Finset.range cutoff,
          quittingStageCoalitionMass reward profile time terminal) ≤
      ∑ time ∈ Finset.range cutoff,
        quittingStageCoalitionMass reward mixedProfile time terminal := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro time _htime
    dsimp only [mixedProfile, mixedStrategy]
    simpa only [Function.update_eq_self] using
      one_sub_mul_stageCoalitionMass_le_stoppingLawMixture
        reward profile who (profile who) bestResponse lambda
          hlambdaPos.le hlambda1 time terminal
  exact ⟨htarget, hgain, hwhoNormalized, hnormalizedBound,
    hnormalizedTransfer, hwindow⟩

/-- **Exact common-base minimum reset ray.**

One approximate best response works simultaneously for every mixture scale.
The endpoint gain is at least half the source debt.  At each scale the same
literal mixed profile co-realizes exact own-coordinate debt consumption,
opposite-face transfer, the full coordinatewise debt chord, and marked-window
retention. -/
theorem exists_stoppingLawResetRay_minimum_transfer_and_windowRetention
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
      let endpointProfile := Function.update profile who bestResponse
      let source := quittingTerminalSemanticPair reward profile
      let endpoint := quittingTerminalSemanticPair reward endpointProfile
      let endpointGain := quittingTerminalPayoff reward endpointProfile who -
        quittingTerminalPayoff reward profile who
      quittingTerminalSemanticDebt source who / 2 ≤ endpointGain ∧
      0 < endpointGain ∧
      ∀ (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1),
        let mixedStrategy := quittingStoppingLawMixtureBehaviorStrategy
          reward who (profile who) bestResponse lambda hlambda0 hlambda1
        let mixedProfile := Function.update profile who mixedStrategy
        let target := quittingTerminalSemanticPair reward mixedProfile
        target ∈ quittingTerminalSemanticCarrier reward ∧
        quittingTerminalPayoff reward mixedProfile who -
            quittingTerminalPayoff reward profile who =
          lambda * endpointGain ∧
        quittingTerminalSemanticDebt target who =
          quittingTerminalSemanticDebt source who - lambda * endpointGain ∧
        lambda * endpointGain ≤
          ∑ other ∈ Finset.univ.erase who,
            quittingTerminalSemanticDebtChange source target other ∧
        (∀ observer,
          quittingTerminalSemanticDebt target observer ≤
            (1 - lambda) * quittingTerminalSemanticDebt source observer +
              lambda * quittingTerminalSemanticDebt endpoint observer) ∧
        (1 - lambda) *
            (∑ time ∈ Finset.range cutoff,
              quittingStageCoalitionMass reward profile time terminal) ≤
          ∑ time ∈ Finset.range cutoff,
            quittingStageCoalitionMass reward mixedProfile time terminal := by
  let source := quittingTerminalSemanticPair reward profile
  let error := quittingTerminalSemanticDebt source who / 2
  have herror : 0 < error := by
    dsimp only [error]
    linarith
  obtain ⟨bestResponse, hbestResponse⟩ :=
    exists_quittingContinuation_deviation_ge_sub
      reward profile who herror hM hreward
  refine ⟨bestResponse, ?_⟩
  dsimp only
  let endpointProfile := Function.update profile who bestResponse
  let endpoint := quittingTerminalSemanticPair reward endpointProfile
  let endpointGain := quittingTerminalPayoff reward endpointProfile who -
    quittingTerminalPayoff reward profile who
  have hendpointGain : quittingTerminalSemanticDebt source who / 2 ≤
      endpointGain := by
    dsimp only [source, error, endpointGain, endpointProfile,
      quittingTerminalSemanticDebt, quittingTerminalSemanticPair] at hbestResponse ⊢
    linarith
  have hendpointGainPos : 0 < endpointGain := by
    have hhalfPos : 0 < quittingTerminalSemanticDebt source who / 2 := by
      exact div_pos hwhoDebt (by norm_num)
    exact hhalfPos.trans_le hendpointGain
  refine ⟨?_, ?_, ?_⟩
  · simpa only [source, endpointGain, endpointProfile] using hendpointGain
  · simpa only [endpointGain, endpointProfile] using hendpointGainPos
  intro lambda hlambda0 hlambda1
  let mixedStrategy := quittingStoppingLawMixtureBehaviorStrategy
    reward who (profile who) bestResponse lambda hlambda0 hlambda1
  let mixedProfile := Function.update profile who mixedStrategy
  let target := quittingTerminalSemanticPair reward mixedProfile
  have htarget : target ∈ quittingTerminalSemanticCarrier reward :=
    quittingTerminalSemanticPair_mem_carrier reward mixedProfile
  have hgain : quittingTerminalPayoff reward mixedProfile who -
        quittingTerminalPayoff reward profile who = lambda * endpointGain := by
    dsimp only [mixedProfile, mixedStrategy, endpointGain, endpointProfile]
    exact quittingTerminalPayoff_stoppingLawMixture_sub_eq
      reward profile who bestResponse lambda hlambda0 hlambda1 hM hreward
  have hendpointDebt : quittingTerminalSemanticDebt endpoint who =
      quittingTerminalSemanticDebt source who - endpointGain := by
    dsimp only [endpoint, source, endpointGain, endpointProfile,
      quittingTerminalSemanticDebt, quittingTerminalSemanticPair]
    rw [quittingContinuationBestResponseValue_update_self]
    ring
  have hdecrease : quittingTerminalSemanticDebt target who =
      quittingTerminalSemanticDebt source who - lambda * endpointGain := by
    have haffine := quittingTerminalSemanticDebt_stoppingLawMixture_eq_self
      reward profile who (profile who) bestResponse lambda hlambda0 hlambda1
    dsimp only [target, source, endpoint, mixedProfile, mixedStrategy,
      endpointProfile] at haffine ⊢
    rw [Function.update_eq_self] at haffine
    rw [hendpointDebt] at haffine
    dsimp only [endpointGain, endpointProfile] at haffine ⊢
    linarith
  have htransfer : lambda * endpointGain ≤
      ∑ other ∈ Finset.univ.erase who,
        quittingTerminalSemanticDebtChange source target other :=
    minimumDebt_opponentTransfer_of_coordinateDecrease
      reward source target who (lambda * endpointGain)
        hminimum htarget hdecrease
  have hchord : ∀ observer,
      quittingTerminalSemanticDebt target observer ≤
        (1 - lambda) * quittingTerminalSemanticDebt source observer +
          lambda * quittingTerminalSemanticDebt endpoint observer := by
    intro observer
    dsimp only [target, source, endpoint, mixedProfile, mixedStrategy,
      endpointProfile]
    have hbound := quittingTerminalSemanticDebt_stoppingLawMixture_le
      reward profile who observer (profile who) bestResponse lambda
        hlambda0 hlambda1 hM hreward
    simpa only [Function.update_eq_self] using hbound
  have hwindow : (1 - lambda) *
        (∑ time ∈ Finset.range cutoff,
          quittingStageCoalitionMass reward profile time terminal) ≤
      ∑ time ∈ Finset.range cutoff,
        quittingStageCoalitionMass reward mixedProfile time terminal := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro time _htime
    dsimp only [mixedProfile, mixedStrategy]
    simpa only [Function.update_eq_self] using
      one_sub_mul_stageCoalitionMass_le_stoppingLawMixture
        reward profile who (profile who) bestResponse lambda
          hlambda0 hlambda1 time terminal
  exact ⟨htarget, hgain, hdecrease, htransfer, hchord, hwindow⟩

/-- Every positive scale on the common-base reset ray has an actual positive
recipient.  Moreover, each such recipient lies in the fixed positive-transfer
support of the full endpoint chord.  The selected recipient may still depend
on the scale; this theorem does not assert state recurrence. -/
theorem exists_stoppingLawResetRay_minimum_endpointSupportedRecipient
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
      let endpointProfile := Function.update profile who bestResponse
      let source := quittingTerminalSemanticPair reward profile
      let endpoint := quittingTerminalSemanticPair reward endpointProfile
      ∀ (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1),
        0 < lambda →
        let mixedStrategy := quittingStoppingLawMixtureBehaviorStrategy
          reward who (profile who) bestResponse lambda hlambda0 hlambda1
        let mixedProfile := Function.update profile who mixedStrategy
        let target := quittingTerminalSemanticPair reward mixedProfile
        let endpointSupport := (Finset.univ.erase who).filter fun recipient ↦
          0 < quittingTerminalSemanticDebtChange source endpoint recipient
        let endpointGain := quittingTerminalPayoff reward endpointProfile who -
          quittingTerminalPayoff reward profile who
        lambda * endpointGain ≤
            ∑ recipient ∈ endpointSupport,
              quittingTerminalSemanticDebtChange source target recipient ∧
          ∃ recipient ∈ endpointSupport,
            0 < quittingTerminalSemanticDebtChange source target recipient := by
  obtain ⟨bestResponse, _hgainLower, hgainPos, hray⟩ :=
    exists_stoppingLawResetRay_minimum_transfer_and_windowRetention
      reward profile who terminal cutoff hM hreward hwhoDebt hminimum
  refine ⟨bestResponse, ?_⟩
  dsimp only
  intro lambda hlambda0 hlambda1 hlambdaPos
  obtain ⟨_htarget, _hgain, _hdecrease, htransfer, hchord, _hwindow⟩ :=
    hray lambda hlambda0 hlambda1
  let endpointProfile := Function.update profile who bestResponse
  let source := quittingTerminalSemanticPair reward profile
  let endpoint := quittingTerminalSemanticPair reward endpointProfile
  let mixedStrategy := quittingStoppingLawMixtureBehaviorStrategy
    reward who (profile who) bestResponse lambda hlambda0 hlambda1
  let mixedProfile := Function.update profile who mixedStrategy
  let target := quittingTerminalSemanticPair reward mixedProfile
  let endpointGain := quittingTerminalPayoff reward endpointProfile who -
    quittingTerminalPayoff reward profile who
  let endpointSupport := (Finset.univ.erase who).filter fun recipient ↦
    0 < quittingTerminalSemanticDebtChange source endpoint recipient
  have hscaledGain : 0 < lambda * endpointGain :=
    mul_pos hlambdaPos hgainPos
  have houtside : ∑ recipient ∈
        (Finset.univ.erase who).filter (fun recipient ↦
          ¬ 0 < quittingTerminalSemanticDebtChange source endpoint recipient),
        quittingTerminalSemanticDebtChange source target recipient ≤ 0 := by
    apply Finset.sum_nonpos
    intro recipient hrecipient
    simp only [Finset.mem_filter] at hrecipient
    have hendpointNonpos :
        quittingTerminalSemanticDebtChange source endpoint recipient ≤ 0 :=
      le_of_not_gt hrecipient.2
    have hrecipientChord := hchord recipient
    dsimp only [target, source, endpoint, mixedProfile, mixedStrategy,
      endpointProfile] at hrecipientChord hendpointNonpos ⊢
    unfold quittingTerminalSemanticDebtChange at hendpointNonpos ⊢
    nlinarith
  have hpartition := Finset.sum_filter_add_sum_filter_not
    (Finset.univ.erase who)
    (fun recipient ↦
      0 < quittingTerminalSemanticDebtChange source endpoint recipient)
    (fun recipient ↦
      quittingTerminalSemanticDebtChange source target recipient)
  have hsupportTransfer : lambda * endpointGain ≤
      ∑ recipient ∈ endpointSupport,
        quittingTerminalSemanticDebtChange source target recipient := by
    dsimp only [endpointSupport]
    linarith
  have hsupportSumPos : 0 < ∑ recipient ∈ endpointSupport,
      quittingTerminalSemanticDebtChange source target recipient :=
    hscaledGain.trans_le hsupportTransfer
  have hexists : ∃ recipient ∈ endpointSupport,
      0 < quittingTerminalSemanticDebtChange source target recipient := by
    by_contra hnot
    push Not at hnot
    have hnonpos := Finset.sum_nonpos fun recipient hrecipient ↦
      hnot recipient hrecipient
    exact (not_le_of_gt hsupportSumPos) hnonpos
  exact ⟨hsupportTransfer, hexists⟩

end GameTheory
