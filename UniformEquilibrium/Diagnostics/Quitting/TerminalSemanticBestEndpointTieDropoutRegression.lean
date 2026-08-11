/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticSignedPairDropoutConsumer

/-!
# A best-endpoint pair dropout can be an exact tie

Endpoint provenance gives a weak sign, but does not by itself give a strict
one.  This literal two-player word consists entirely of full recomputed
best-endpoint moves.  It routes sure mass through

`{false,true} -> {true} -> empty`

and ends at an exact Nash root.  At the first dropout, Continue is the
tie-broken best endpoint, yet its local defect and payoff gain are both zero.
The surviving singleton owner has reward `-1` against continuation `0`, so
the usual negative-singleton punishment geometry is present as well.

This is not an instance of the counterexample regime, but the obstruction
lifts exactly to the global terminal-semantic carrier.  The pair profile is a
global minimum with total debt zero.  Deleting the indifferent player
preserves that player's debt while raising the survivor's debt by one, so the
singleton profile leaves the minimum face.  Thus any theorem eliminating or
merging the tie branch needs cross-player debt preservation, a state-matched
return, or another genuinely global counterexample hypothesis; incidence,
negative singleton payoff, endpoint provenance, and zero final Nash defect
do not suffice.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

namespace QuittingBestEndpointTieDropoutRegression

def reward (quitters : {S : Finset Bool // S.Nonempty}) : Payoff Bool :=
  fun who =>
    if false ∈ quitters.1 ∧ true ∈ quitters.1 then 0
    else if who ∈ quitters.1 then -1 else 0

def tail : Payoff Bool := fun _ => 0

def pairRoot : Bool → PMF Bool := fun _ => PMF.pure true

def singletonRoot : Bool → PMF Bool :=
  Function.update pairRoot false (PMF.pure false)

def finalRoot : Bool → PMF Bool :=
  Function.update singletonRoot true (PMF.pure false)

/-- A literal zero continuation used to lift the row calculation to the
terminal-semantic carrier. -/
def continuation : (quittingGame reward).BehaviorProfile :=
  quittingAlwaysContinueProfile reward

def pairProfile : (quittingGame reward).BehaviorProfile :=
  quittingRootThenContinuationProfile reward pairRoot continuation

def singletonProfile : (quittingGame reward).BehaviorProfile :=
  quittingRootThenContinuationProfile reward singletonRoot continuation

def firstMove : QuittingFractionalEndpointMove Bool where
  who := false
  action := false
  weight := 1
  weight_nonneg := by norm_num
  weight_le_one := by norm_num

def secondMove : QuittingFractionalEndpointMove Bool where
  who := true
  action := false
  weight := 1
  weight_nonneg := by norm_num
  weight_le_one := by norm_num

theorem firstMove_apply : firstMove.apply pairRoot = singletonRoot := by
  rw [firstMove.apply_eq_update_pure_of_weight_eq_one pairRoot (by rfl)]
  rfl

theorem secondMove_apply : secondMove.apply singletonRoot = finalRoot := by
  rw [secondMove.apply_eq_update_pure_of_weight_eq_one singletonRoot (by rfl)]
  rfl

theorem finalRoot_eq_allContinue :
    finalRoot = (quittingAllContinueRoot : Bool → PMF Bool) := by
  funext who
  cases who <;>
    simp [finalRoot, singletonRoot, quittingAllContinueRoot]

theorem pairRoot_pairMass :
    quittingRootCoalitionMass pairRoot (Finset.univ : Finset Bool) = 1 := by
  unfold quittingRootCoalitionMass
  have hcomplement : (Finset.univ : Finset Bool)ᶜ = ∅ := by
    ext who
    simp
  rw [coalitionMass, hcomplement]
  simp [quittingRootQuitRates, pairRoot]

theorem singletonRoot_singletonMass :
    quittingRootCoalitionMass singletonRoot ({true} : Finset Bool) = 1 := by
  unfold quittingRootCoalitionMass
  have hcomplement : ({true} : Finset Bool)ᶜ = {false} := by decide
  rw [coalitionMass, hcomplement]
  simp [quittingRootQuitRates, singletonRoot, pairRoot]

theorem pairRoot_quitPayoff_false :
    quittingRootQuitPayoff reward tail pairRoot false = 0 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [QuittingExactDynamicDebtVanishingCounterexample.expect_pmfPi_bool]
  simp [expect_eq_sum, quittingRootPayoff, reward, tail, pairRoot]

theorem pairRoot_continuePayoff_false :
    quittingRootContinuePayoff reward tail pairRoot false = 0 := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [QuittingExactDynamicDebtVanishingCounterexample.expect_pmfPi_bool]
  simp [expect_eq_sum, quittingRootPayoff, reward, tail, pairRoot]

theorem pairRoot_quitPayoff (who : Bool) :
    quittingRootQuitPayoff reward tail pairRoot who = 0 := by
  cases who
  · exact pairRoot_quitPayoff_false
  · unfold quittingRootQuitPayoff quittingRootExpectedPayoff
    rw [QuittingExactDynamicDebtVanishingCounterexample.expect_pmfPi_bool]
    simp [expect_eq_sum, quittingRootPayoff, reward, tail, pairRoot]

theorem pairRoot_continuePayoff (who : Bool) :
    quittingRootContinuePayoff reward tail pairRoot who = 0 := by
  cases who
  · exact pairRoot_continuePayoff_false
  · unfold quittingRootContinuePayoff quittingRootExpectedPayoff
    rw [QuittingExactDynamicDebtVanishingCounterexample.expect_pmfPi_bool]
    simp [expect_eq_sum, quittingRootPayoff, reward, tail, pairRoot]

theorem pairRoot_successorPayoff (who : Bool) :
    quittingRootSuccessorPayoff reward tail pairRoot who = 0 := by
  rw [quittingRootSuccessorPayoff_eq_endpointMix,
    pairRoot_quitPayoff, pairRoot_continuePayoff]
  ring

theorem pairRoot_endpointDifference_false :
    quittingRootEndpointDifference reward tail pairRoot false = 0 := by
  rw [quittingRootEndpointDifference, pairRoot_quitPayoff_false,
    pairRoot_continuePayoff_false]
  norm_num

theorem pairRoot_bestEndpoint_false :
    quittingRootBestEndpointAction reward tail pairRoot false = false := by
  simp [quittingRootBestEndpointAction, pairRoot_quitPayoff_false,
    pairRoot_continuePayoff_false]

theorem pairRoot_defect_false :
    quittingRootCoordinateNashDefect reward tail pairRoot false = 0 := by
  rw [quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart,
    pairRoot_endpointDifference_false]
  norm_num

theorem pairRoot_dropoutGain_false :
    quittingRootSuccessorPayoff reward tail singletonRoot false -
        quittingRootSuccessorPayoff reward tail pairRoot false = 0 := by
  have hgain :=
    quittingRootSuccessorPayoff_bestEndpoint_sub_eq_coordinateNashDefect
      reward tail pairRoot false
  rw [pairRoot_bestEndpoint_false, ← singletonRoot] at hgain
  simpa [pairRoot_defect_false] using hgain

theorem singletonRoot_quitPayoff_true :
    quittingRootQuitPayoff reward tail singletonRoot true = -1 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [QuittingExactDynamicDebtVanishingCounterexample.expect_pmfPi_bool]
  simp [expect_eq_sum, quittingRootPayoff, reward, tail,
    singletonRoot]

theorem singletonRoot_continuePayoff_true :
    quittingRootContinuePayoff reward tail singletonRoot true = 0 := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [QuittingExactDynamicDebtVanishingCounterexample.expect_pmfPi_bool]
  simp [expect_eq_sum, quittingRootPayoff, reward, tail,
    singletonRoot]

theorem singletonRoot_quitPayoff_false :
    quittingRootQuitPayoff reward tail singletonRoot false = 0 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [QuittingExactDynamicDebtVanishingCounterexample.expect_pmfPi_bool]
  simp [expect_eq_sum, quittingRootPayoff, reward, tail,
    singletonRoot, pairRoot]

theorem singletonRoot_continuePayoff_false :
    quittingRootContinuePayoff reward tail singletonRoot false = 0 := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [QuittingExactDynamicDebtVanishingCounterexample.expect_pmfPi_bool]
  simp [expect_eq_sum, quittingRootPayoff, reward, tail,
    singletonRoot]

theorem singletonRoot_successorPayoff (who : Bool) :
    quittingRootSuccessorPayoff reward tail singletonRoot who =
      if who then -1 else 0 := by
  rw [quittingRootSuccessorPayoff_eq_endpointMix]
  cases who
  · rw [singletonRoot_quitPayoff_false,
      singletonRoot_continuePayoff_false]
    norm_num
  · rw [singletonRoot_quitPayoff_true,
      singletonRoot_continuePayoff_true]
    simp [singletonRoot, pairRoot]

theorem singletonRoot_bestEndpoint_true :
    quittingRootBestEndpointAction reward tail singletonRoot true = false := by
  simp [quittingRootBestEndpointAction, singletonRoot_quitPayoff_true,
    singletonRoot_continuePayoff_true]

theorem finalRoot_isZeroNash :
    IsεQuittingRootNash reward tail 0 finalRoot := by
  rw [finalRoot_eq_allContinue,
    isZeroQuittingRootNash_allContinue_iff_singleton_le]
  intro who
  cases who <;>
    simp [reward, tail, quittingSingletonTerminal]

theorem finalRoot_totalNashDefect :
    quittingRootTotalNashDefect reward tail finalRoot = 0 := by
  unfold quittingRootTotalNashDefect
  simp_rw [(isZeroQuittingRootNash_iff_coordinateNashDefect_eq_zero
    reward tail finalRoot).mp finalRoot_isZeroNash]
  simp

theorem pairRoot_positiveIncidence :
    0 < quittingRootOpponentIncidenceMass false true pairRoot := by
  have hle :=
    quittingRootCoalitionMass_le_opponentIncidenceMass_of_other_mem
      pairRoot (Finset.univ : Finset Bool) false true (by simp) (by simp)
        (by decide)
  rw [pairRoot_pairMass] at hle
  linarith

theorem singletonRoot_positiveIncidence :
    0 < quittingRootOpponentIncidenceMass false true singletonRoot := by
  have hle :=
    quittingRootCoalitionMass_le_opponentIncidenceMass_of_other_mem
      singletonRoot ({true} : Finset Bool) false true (by simp) (by simp)
        (by decide)
  rw [singletonRoot_singletonMass] at hle
  linarith

theorem singletonOwner_negativeReward :
    quittingSoloReward reward true true = -1 := by
  simp [quittingSoloReward, reward]

/-! ## The neutral deletion leaves the minimum face -/

theorem abs_reward_le_one
    (terminal : {S : Finset Bool // S.Nonempty}) (who : Bool) :
    |reward terminal who| ≤ 1 := by
  unfold reward
  split_ifs <;> norm_num

theorem terminalOutcomeReward_nonpos
    (outcome : QuittingTerminalOutcome Bool) (who : Bool) :
    quittingTerminalOutcomeReward reward outcome who ≤ 0 := by
  cases outcome with
  | none => simp [quittingTerminalOutcomeReward]
  | some terminal =>
      change reward terminal who ≤ 0
      unfold reward
      split_ifs <;> norm_num

theorem continuation_semanticPair :
    quittingTerminalSemanticPair reward continuation = (tail, tail) := by
  apply Prod.ext
  · funext who
    exact quittingTerminalPayoff_quittingAlwaysContinue reward who
  · funext who
    apply le_antisymm
    · exact quittingContinuationBestResponseValue_le_of_terminalOutcomeReward_le
        continuation who 0 (fun outcome => terminalOutcomeReward_nonpos outcome who)
    · have hlower := quittingTerminalPayoff_update_le_continuationBestResponseValue
        reward continuation who (continuation who) (M := 1) (by norm_num)
          abs_reward_le_one
      have hupdate : Function.update continuation who (continuation who) =
          continuation := Function.update_eq_self _ _
      rw [hupdate] at hlower
      change 0 ≤ quittingContinuationBestResponseValue reward continuation who
      simpa [continuation] using hlower

theorem pairProfile_semanticPair :
    quittingTerminalSemanticPair reward pairProfile = (tail, tail) := by
  rw [show pairProfile = quittingRootThenContinuationProfile reward
      pairRoot continuation by rfl,
    quittingTerminalSemanticPair_rootThenContinuation reward pairRoot
      continuation (M := 1) (by norm_num) abs_reward_le_one,
    continuation_semanticPair]
  apply Prod.ext
  · funext who
    exact pairRoot_successorPayoff who
  · funext who
    change max (quittingRootQuitPayoff reward tail pairRoot who)
      (quittingRootContinuePayoff reward
        (Function.update tail who (tail who)) pairRoot who) = tail who
    rw [Function.update_eq_self]
    simp [pairRoot_quitPayoff, pairRoot_continuePayoff, tail]

theorem singletonProfile_semanticPair :
    quittingTerminalSemanticPair reward singletonProfile =
      ((fun who => if who then -1 else 0), tail) := by
  rw [show singletonProfile = quittingRootThenContinuationProfile reward
      singletonRoot continuation by rfl,
    quittingTerminalSemanticPair_rootThenContinuation reward singletonRoot
      continuation (M := 1) (by norm_num) abs_reward_le_one,
    continuation_semanticPair]
  apply Prod.ext
  · funext who
    exact singletonRoot_successorPayoff who
  · funext who
    change max (quittingRootQuitPayoff reward tail singletonRoot who)
      (quittingRootContinuePayoff reward
        (Function.update tail who (tail who)) singletonRoot who) = tail who
    rw [Function.update_eq_self]
    cases who <;>
      simp [singletonRoot_quitPayoff_false,
        singletonRoot_continuePayoff_false, singletonRoot_quitPayoff_true,
        singletonRoot_continuePayoff_true, tail]

theorem pairProfile_totalDebt :
    quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward pairProfile) = 0 := by
  rw [pairProfile_semanticPair]
  simp [quittingTerminalSemanticDebtSum, quittingTerminalSemanticDebt, tail]

theorem singletonProfile_totalDebt :
    quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward singletonProfile) = 1 := by
  rw [singletonProfile_semanticPair]
  simp [quittingTerminalSemanticDebtSum, quittingTerminalSemanticDebt, tail]

theorem neutralDropout_moverDebt_preserved :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward pairProfile) false =
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward singletonProfile) false := by
  rw [pairProfile_semanticPair, singletonProfile_semanticPair]
  simp [quittingTerminalSemanticDebt, tail]

theorem neutralDropout_survivorDebt_increases :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward singletonProfile) true =
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward pairProfile) true + 1 := by
  rw [pairProfile_semanticPair, singletonProfile_semanticPair]
  simp [quittingTerminalSemanticDebt, tail]

theorem pairProfile_is_globalMinimum :
    ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward pairProfile) ≤
        quittingTerminalSemanticDebtSum candidate := by
  intro candidate hcandidate
  rw [pairProfile_totalDebt]
  unfold quittingTerminalSemanticDebtSum
  exact Finset.sum_nonneg fun who _ =>
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward (by norm_num) abs_reward_le_one hcandidate who

/-- **Regression headline.**  Full recomputed best-endpoint routing, positive
pair and singleton incidence, a negative singleton owner reward, and zero
final Nash defect still permit an exactly indifferent pair dropout. -/
theorem bestEndpoint_pair_dropout_can_be_exact_tie :
    firstMove.weight = 1 ∧
      firstMove.action =
        quittingRootBestEndpointAction reward tail pairRoot firstMove.who ∧
      firstMove.apply pairRoot = singletonRoot ∧
      secondMove.weight = 1 ∧
      secondMove.action =
        quittingRootBestEndpointAction reward tail singletonRoot secondMove.who ∧
      secondMove.apply singletonRoot = finalRoot ∧
      quittingRootCoalitionMass pairRoot
          (Finset.univ : Finset Bool) = 1 ∧
      quittingRootCoalitionMass singletonRoot ({true} : Finset Bool) = 1 ∧
      0 < quittingRootOpponentIncidenceMass false true pairRoot ∧
      0 < quittingRootOpponentIncidenceMass false true singletonRoot ∧
      quittingRootEndpointDifference reward tail pairRoot false = 0 ∧
      quittingRootCoordinateNashDefect reward tail pairRoot false = 0 ∧
      quittingRootSuccessorPayoff reward tail singletonRoot false -
          quittingRootSuccessorPayoff reward tail pairRoot false = 0 ∧
      quittingSoloReward reward true true = -1 ∧
      tail true = 0 ∧
      quittingRootTotalNashDefect reward tail finalRoot = 0 ∧
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward pairProfile) = 0 ∧
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward singletonProfile) = 1 ∧
      (∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward pairProfile) ≤
          quittingTerminalSemanticDebtSum candidate) := by
  exact ⟨rfl, pairRoot_bestEndpoint_false.symm, firstMove_apply,
    rfl, singletonRoot_bestEndpoint_true.symm, secondMove_apply,
    pairRoot_pairMass, singletonRoot_singletonMass,
    pairRoot_positiveIncidence, singletonRoot_positiveIncidence,
    pairRoot_endpointDifference_false, pairRoot_defect_false,
    pairRoot_dropoutGain_false, singletonOwner_negativeReward, rfl,
    finalRoot_totalNashDefect, pairProfile_totalDebt,
    singletonProfile_totalDebt, pairProfile_is_globalMinimum⟩

end QuittingBestEndpointTieDropoutRegression

end GameTheory
