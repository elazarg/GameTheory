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

This is a local sharpness regression, not an instance of the global
counterexample regime.  It shows that any theorem eliminating the tie branch
must use an additional positive-defect, strict-endpoint, or genuinely global
counterexample hypothesis; incidence, negative singleton payoff, endpoint
provenance, and zero final Nash defect do not suffice locally.
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
      quittingRootTotalNashDefect reward tail finalRoot = 0 := by
  exact ⟨rfl, pairRoot_bestEndpoint_false.symm, firstMove_apply,
    rfl, singletonRoot_bestEndpoint_true.symm, secondMove_apply,
    pairRoot_pairMass, singletonRoot_singletonMass,
    pairRoot_positiveIncidence, singletonRoot_positiveIncidence,
    pairRoot_endpointDifference_false, pairRoot_defect_false,
    pairRoot_dropoutGain_false, singletonOwner_negativeReward, rfl,
    finalRoot_totalNashDefect⟩

end QuittingBestEndpointTieDropoutRegression

end GameTheory
