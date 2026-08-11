/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauIncidence
import UniformEquilibrium.Quitting.Debt.Marked.TimeAdvance

/-!
# Nash-defect charge at an actual semantic prefix row

An actual live row need not be a Nash row, and its shifted tail need not lie
on the minimum-debt fiber.  This module gives the exact quantitative
replacement for either missing assertion.

For one player, let `delta` be the gap between the better pure root endpoint
and the prescribed root mixture.  Then an arbitrary semantic prefix obeys

`(opponent absorption) * (tail debt)
  <= tail debt - prefix debt + delta`.

After summing coordinates at a minimum carrier point, every observed
opponent-containing coalition is therefore charged by the shifted tail's
excess total debt or by the actual root's total Nash defect.  This is a
profile-owned estimate: it does not silently replace an actual live root by
an exact Nash selection.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The least nonnegative one-coordinate error needed to make the prescribed
root mixture dominate both pure endpoints. -/
def quittingRootCoordinateNashDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) : ℝ :=
  max (quittingRootQuitPayoff reward tail root who)
      (quittingRootContinuePayoff reward tail root who) -
    quittingRootSuccessorPayoff reward tail root who

/-- Total one-stage Nash defect of a product root. -/
def quittingRootTotalNashDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) : ℝ :=
  ∑ who, quittingRootCoordinateNashDefect reward tail root who

/-- A root-coordinate Nash defect is nonnegative because the prescribed
payoff is a convex combination of the two pure endpoint payoffs. -/
theorem quittingRootCoordinateNashDefect_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    0 ≤ quittingRootCoordinateNashDefect reward tail root who := by
  rw [quittingRootCoordinateNashDefect,
    quittingRootSuccessorPayoff_eq_endpointMix]
  have hsum := quittingRoot_continueProbability_add_quitProbability root who
  have hquit := le_max_left
    (quittingRootQuitPayoff reward tail root who)
    (quittingRootContinuePayoff reward tail root who)
  have hcontinue := le_max_right
    (quittingRootQuitPayoff reward tail root who)
    (quittingRootContinuePayoff reward tail root who)
  have hquitProbability : 0 ≤ (root who true).toReal := ENNReal.toReal_nonneg
  have hcontinueProbability : 0 ≤ (root who false).toReal :=
    ENNReal.toReal_nonneg
  have hweighted :
      (root who true).toReal * quittingRootQuitPayoff reward tail root who +
          (root who false).toReal *
            quittingRootContinuePayoff reward tail root who ≤
        max (quittingRootQuitPayoff reward tail root who)
          (quittingRootContinuePayoff reward tail root who) := by
    calc
      (root who true).toReal * quittingRootQuitPayoff reward tail root who +
          (root who false).toReal *
            quittingRootContinuePayoff reward tail root who ≤
        (root who true).toReal *
            max (quittingRootQuitPayoff reward tail root who)
              (quittingRootContinuePayoff reward tail root who) +
          (root who false).toReal *
            max (quittingRootQuitPayoff reward tail root who)
              (quittingRootContinuePayoff reward tail root who) :=
        add_le_add
          (mul_le_mul_of_nonneg_left hquit hquitProbability)
          (mul_le_mul_of_nonneg_left hcontinue hcontinueProbability)
      _ = max (quittingRootQuitPayoff reward tail root who)
            (quittingRootContinuePayoff reward tail root who) := by
        rw [← add_mul]
        have hsum' : (root who true).toReal +
            (root who false).toReal = 1 := by linarith
        rw [hsum', one_mul]
  linarith

/-- The total root Nash defect is nonnegative. -/
theorem quittingRootTotalNashDefect_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) :
    0 ≤ quittingRootTotalNashDefect reward tail root := by
  exact Finset.sum_nonneg fun who _ =>
    quittingRootCoordinateNashDefect_nonneg reward tail root who

/-- Exact Nash is precisely zero coordinate defect. -/
theorem isZeroQuittingRootNash_iff_coordinateNashDefect_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) :
    IsεQuittingRootNash reward tail 0 root ↔
      ∀ who, quittingRootCoordinateNashDefect reward tail root who = 0 := by
  constructor
  · intro hnash who
    rw [quittingRootCoordinateNashDefect,
      ← quittingRootSuccessorPayoff_eq_max_of_isZeroNash
        reward tail root who hnash, sub_self]
  · intro hzero
    apply (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward tail root).mp
    intro who
    have hdefect := hzero who
    unfold quittingRootCoordinateNashDefect at hdefect
    have hquit : quittingRootQuitPayoff reward tail root who ≤
        quittingRootSuccessorPayoff reward tail root who := by
      linarith [le_max_left
        (quittingRootQuitPayoff reward tail root who)
        (quittingRootContinuePayoff reward tail root who)]
    have hcontinue : quittingRootContinuePayoff reward tail root who ≤
        quittingRootSuccessorPayoff reward tail root who := by
      linarith [le_max_right
        (quittingRootQuitPayoff reward tail root who)
        (quittingRootContinuePayoff reward tail root who)]
    have hmix := quittingRootSuccessorPayoff_eq_endpointMix
      reward tail root who
    have hsum := quittingRoot_continueProbability_add_quitProbability root who
    have hcontinueProbability : 0 ≤ (root who false).toReal :=
      ENNReal.toReal_nonneg
    have hquitProbability : 0 ≤ (root who true).toReal := ENNReal.toReal_nonneg
    have hquitRegret :
        quittingRootQuitPayoff reward tail root who -
            quittingRootSuccessorPayoff reward tail root who =
          (root who false).toReal *
            (quittingRootQuitPayoff reward tail root who -
              quittingRootContinuePayoff reward tail root who) := by
      rw [hmix]
      have hquitMass : (root who true).toReal =
          1 - (root who false).toReal := by linarith
      rw [hquitMass]
      ring
    have hcontinueRegret :
        quittingRootContinuePayoff reward tail root who -
            quittingRootSuccessorPayoff reward tail root who =
          -(root who true).toReal *
            (quittingRootQuitPayoff reward tail root who -
              quittingRootContinuePayoff reward tail root who) := by
      rw [hmix]
      have hcontinueMass : (root who false).toReal =
          1 - (root who true).toReal := by linarith
      rw [hcontinueMass]
      ring
    unfold quittingRootEndpointDifference
    constructor
    · linarith
    · linarith

/-- Arbitrary-root semantic debt is bounded by transported tail debt plus
the local one-stage Nash defect. -/
theorem quittingTerminalSemanticDebt_prefix_le_nashDefect_add_transport
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (who : ι)
    (hdebt : 0 ≤ quittingTerminalSemanticDebt pair who) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPrefix reward root pair) who ≤
      quittingRootCoordinateNashDefect reward pair.1 root who +
        quittingRootOpponentContinueMass root who *
          quittingTerminalSemanticDebt pair who := by
  let debt := quittingTerminalSemanticDebt pair who
  let quitValue := quittingRootQuitPayoff reward pair.1 root who
  let continueValue := quittingRootContinuePayoff reward pair.1 root who
  let successor := quittingRootSuccessorPayoff reward pair.1 root who
  let survived := quittingRootOpponentContinueMass root who * debt
  have hsurvived : 0 ≤ survived :=
    mul_nonneg (quittingRootOpponentContinueMass_nonneg root who) hdebt
  have henvelope : pair.2 who = pair.1 who + debt := by
    dsimp [debt, quittingTerminalSemanticDebt]
    ring
  have hcontinueEnvelope :
      quittingRootContinuePayoff reward
          (Function.update pair.1 who (pair.2 who)) root who =
        continueValue + survived := by
    rw [henvelope, quittingRootContinuePayoff_update_add]
  unfold quittingTerminalSemanticDebt quittingTerminalSemanticPrefix
  dsimp only
  rw [hcontinueEnvelope]
  change max quitValue (continueValue + survived) - successor ≤
    (max quitValue continueValue - successor) + survived
  have hmax : max quitValue (continueValue + survived) ≤
      max quitValue continueValue + survived := by
    apply max_le
    · exact (le_max_left _ _).trans (le_add_of_nonneg_right hsurvived)
    · linarith [le_max_right quitValue continueValue]
  linarith

/-- The local root defect is already part of the prefixed semantic debt. -/
theorem quittingRootCoordinateNashDefect_le_terminalSemanticDebt_prefix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (who : ι)
    (hdebt : 0 ≤ quittingTerminalSemanticDebt pair who) :
    quittingRootCoordinateNashDefect reward pair.1 root who ≤
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPrefix reward root pair) who := by
  let debt := quittingTerminalSemanticDebt pair who
  let quitValue := quittingRootQuitPayoff reward pair.1 root who
  let continueValue := quittingRootContinuePayoff reward pair.1 root who
  let successor := quittingRootSuccessorPayoff reward pair.1 root who
  let survived := quittingRootOpponentContinueMass root who * debt
  have hsurvived : 0 ≤ survived :=
    mul_nonneg (quittingRootOpponentContinueMass_nonneg root who) hdebt
  have henvelope : pair.2 who = pair.1 who + debt := by
    dsimp [debt, quittingTerminalSemanticDebt]
    ring
  have hcontinueEnvelope :
      quittingRootContinuePayoff reward
          (Function.update pair.1 who (pair.2 who)) root who =
        continueValue + survived := by
    rw [henvelope, quittingRootContinuePayoff_update_add]
  unfold quittingRootCoordinateNashDefect quittingTerminalSemanticDebt
    quittingTerminalSemanticPrefix
  dsimp only
  rw [hcontinueEnvelope]
  change max quitValue continueValue - successor ≤
    max quitValue (continueValue + survived) - successor
  have hmax : max quitValue continueValue ≤
      max quitValue (continueValue + survived) := by
    apply max_le
    · exact le_max_left _ _
    · exact (le_add_of_nonneg_right hsurvived).trans (le_max_right _ _)
  exact sub_le_sub_right hmax successor

/-- If the displayed player Continues purely, the prefix transports at least
the joint-survival share of that player's tail debt. -/
theorem stationaryContinueMass_mul_debt_le_terminalSemanticDebt_prefix_of_pureContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (who : ι)
    (hroot : root who = PMF.pure false) :
    quittingStationaryContinueMass root *
        quittingTerminalSemanticDebt pair who ≤
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPrefix reward root pair) who := by
  let debt := quittingTerminalSemanticDebt pair who
  let quitValue := quittingRootQuitPayoff reward pair.1 root who
  let continueValue := quittingRootContinuePayoff reward pair.1 root who
  let survived := quittingStationaryContinueMass root * debt
  have hupdate : Function.update root who (PMF.pure false) = root := by
    rw [← hroot]
    exact Function.update_eq_self who root
  have hopponent : quittingRootOpponentContinueMass root who =
      quittingStationaryContinueMass root := by
    unfold quittingRootOpponentContinueMass
    rw [hupdate]
  have henvelope : pair.2 who = pair.1 who + debt := by
    dsimp [debt, quittingTerminalSemanticDebt]
    ring
  have hcontinueEnvelope :
      quittingRootContinuePayoff reward
          (Function.update pair.1 who (pair.2 who)) root who =
        continueValue + survived := by
    rw [henvelope, quittingRootContinuePayoff_update_add, hopponent]
  have hsuccessor : quittingRootSuccessorPayoff reward pair.1 root who =
      continueValue := by
    dsimp only [continueValue]
    rw [quittingRootSuccessorPayoff_eq_endpointMix, hroot]
    simp
  unfold quittingTerminalSemanticDebt quittingTerminalSemanticPrefix
  dsimp only
  rw [hcontinueEnvelope, hsuccessor]
  change survived ≤ max quitValue (continueValue + survived) - continueValue
  linarith [le_max_right quitValue (continueValue + survived)]

/-- The drift term is genuinely necessary.  If `who` purely Continues and
Quit is not locally better, its local Nash defect is zero while semantic debt
is transported by joint survival exactly. -/
theorem terminalSemanticDebt_prefix_eq_stationaryContinueMass_mul_of_pureContinue_of_quit_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (who : ι)
    (hdebt : 0 ≤ quittingTerminalSemanticDebt pair who)
    (hroot : root who = PMF.pure false)
    (hquit : quittingRootQuitPayoff reward pair.1 root who ≤
      quittingRootContinuePayoff reward pair.1 root who) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPrefix reward root pair) who =
      quittingStationaryContinueMass root *
        quittingTerminalSemanticDebt pair who ∧
    quittingRootCoordinateNashDefect reward pair.1 root who = 0 ∧
    quittingRootOpponentAbsorptionMass root who *
        quittingTerminalSemanticDebt pair who =
      quittingTerminalSemanticDebt pair who -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPrefix reward root pair) who := by
  let debt := quittingTerminalSemanticDebt pair who
  let quitValue := quittingRootQuitPayoff reward pair.1 root who
  let continueValue := quittingRootContinuePayoff reward pair.1 root who
  let survived := quittingStationaryContinueMass root * debt
  have hsurvived : 0 ≤ survived :=
    mul_nonneg (quittingStationaryContinueMass_nonneg root) hdebt
  have hupdate : Function.update root who (PMF.pure false) = root := by
    rw [← hroot]
    exact Function.update_eq_self who root
  have hopponent : quittingRootOpponentContinueMass root who =
      quittingStationaryContinueMass root := by
    unfold quittingRootOpponentContinueMass
    rw [hupdate]
  have henvelope : pair.2 who = pair.1 who + debt := by
    dsimp [debt, quittingTerminalSemanticDebt]
    ring
  have hcontinueEnvelope :
      quittingRootContinuePayoff reward
          (Function.update pair.1 who (pair.2 who)) root who =
        continueValue + survived := by
    rw [henvelope, quittingRootContinuePayoff_update_add, hopponent]
  have hsuccessor : quittingRootSuccessorPayoff reward pair.1 root who =
      continueValue := by
    dsimp only [continueValue]
    rw [quittingRootSuccessorPayoff_eq_endpointMix, hroot]
    simp
  have hprefixDebt : quittingTerminalSemanticDebt
      (quittingTerminalSemanticPrefix reward root pair) who = survived := by
    unfold quittingTerminalSemanticDebt quittingTerminalSemanticPrefix
    dsimp only
    rw [hcontinueEnvelope, hsuccessor]
    change max quitValue (continueValue + survived) - continueValue = survived
    rw [max_eq_right]
    · ring
    · exact hquit.trans (le_add_of_nonneg_right hsurvived)
  have hdefect : quittingRootCoordinateNashDefect reward pair.1 root who = 0 := by
    unfold quittingRootCoordinateNashDefect
    rw [hsuccessor, max_eq_right hquit, sub_self]
  refine ⟨hprefixDebt, hdefect, ?_⟩
  rw [hprefixDebt]
  have habsorption : quittingRootOpponentAbsorptionMass root who =
      1 - quittingStationaryContinueMass root := by
    have hcomplement :=
      quittingRootOpponentContinueMass_eq_one_sub_absorptionMass root who
    rw [hopponent] at hcomplement
    linarith
  rw [habsorption]
  dsimp only [survived, debt]
  ring

/-- Pure continuation by one player identifies joint continuation with its
opponent-continuation coefficient. -/
theorem quittingJointContinueMass_eq_opponentContinueMass_of_liveRoot_pureContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (time : ℕ) (who : ι)
    (hroot : quittingProfileLiveRoot reward profile time who = PMF.pure false) :
    quittingJointContinueMass reward profile time =
      quittingRootOpponentContinueMass
        (quittingProfileLiveRoot reward profile time) who := by
  rw [quittingJointContinueMass_eq_product,
    quittingRootOpponentContinueMass,
    quittingStationaryContinueMass_eq_prod_continueProbability]
  let root := quittingProfileLiveRoot reward profile time
  have hupdate : Function.update root who (PMF.pure false) = root := by
    rw [← hroot]
    exact Function.update_eq_self who root
  rw [hupdate]
  rfl

/-- Along a literal profile, if `who` has Continued purely before `time`, its
current semantic debt, weighted by the probability of reaching that row, is
bounded by its initial semantic debt.  This is the dynamic-programming
reason a near-best pure-time deviation has small survival-weighted local
defect at every selected row. -/
theorem quittingLiveMass_mul_spineDebt_le_initialDebt_of_prior_pureContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    ∀ time,
      (∀ stage < time,
        quittingProfileLiveRoot reward profile stage who = PMF.pure false) →
      quittingLiveMass reward profile time *
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (quittingAllContinueProfileSpine reward profile time)) who ≤
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) who := by
  intro time
  induction time with
  | zero =>
      intro _hprior
      simp [quittingAllContinueProfileSpine]
  | succ time ih =>
      intro hprior
      let current := quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward profile time)
      let tail := quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward profile (time + 1))
      let root := quittingProfileLiveRoot reward profile time
      have hroot : root who = PMF.pure false := hprior time (by omega)
      have honeStep : quittingStationaryContinueMass root *
          quittingTerminalSemanticDebt tail who ≤
        quittingTerminalSemanticDebt current who := by
        have htransport :=
          stationaryContinueMass_mul_debt_le_terminalSemanticDebt_prefix_of_pureContinue
            reward tail root who hroot
        have hprefix : current =
            quittingTerminalSemanticPrefix reward root tail := by
          dsimp only [current, root, tail]
          exact quittingTerminalSemanticPair_spine_eq_prefix
            reward profile time hM hreward
        rw [hprefix]
        exact htransport
      have hjoint : quittingJointContinueMass reward profile time =
          quittingStationaryContinueMass root := by
        rw [quittingJointContinueMass_eq_opponentContinueMass_of_liveRoot_pureContinue
          reward profile time who hroot]
        unfold quittingRootOpponentContinueMass
        have hupdate : Function.update root who (PMF.pure false) = root := by
          rw [← hroot]
          exact Function.update_eq_self who root
        rw [hupdate]
      have hliveNonneg := quittingLiveMass_nonneg reward profile time
      have hweighted : quittingLiveMass reward profile (time + 1) *
          quittingTerminalSemanticDebt tail who ≤
        quittingLiveMass reward profile time *
          quittingTerminalSemanticDebt current who := by
        rw [quittingLiveMass_succ, hjoint]
        calc
          (quittingLiveMass reward profile time *
              quittingStationaryContinueMass root) *
                quittingTerminalSemanticDebt tail who =
            quittingLiveMass reward profile time *
              (quittingStationaryContinueMass root *
                quittingTerminalSemanticDebt tail who) := by ring
          _ ≤ quittingLiveMass reward profile time *
              quittingTerminalSemanticDebt current who :=
            mul_le_mul_of_nonneg_left honeStep hliveNonneg
      exact hweighted.trans (ih (fun stage hstage =>
        hprior stage (Nat.lt_succ_of_lt hstage)))

/-- Consequently every local root defect exposed after a pure-Continue
prefix is bounded, after weighting by actual survival, by the initial
semantic debt of that player. -/
theorem quittingLiveMass_mul_coordinateNashDefect_le_initialDebt_of_prior_pureContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (time : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hprior : ∀ stage < time,
      quittingProfileLiveRoot reward profile stage who = PMF.pure false) :
    quittingLiveMass reward profile time *
        quittingRootCoordinateNashDefect reward
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward profile (time + 1))).1
          (quittingProfileLiveRoot reward profile time) who ≤
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) who := by
  let tail := quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward profile (time + 1))
  let root := quittingProfileLiveRoot reward profile time
  let current := quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward profile time)
  have htailCarrier : tail ∈ quittingTerminalSemanticCarrier reward :=
    quittingTerminalSemanticPair_mem_carrier reward _
  have htailDebt : 0 ≤ quittingTerminalSemanticDebt tail who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hM hreward htailCarrier who
  have hlocal :=
    quittingRootCoordinateNashDefect_le_terminalSemanticDebt_prefix
      reward tail root who htailDebt
  rw [← quittingTerminalSemanticPair_spine_eq_prefix
    reward profile time hM hreward] at hlocal
  have hscaled := mul_le_mul_of_nonneg_left hlocal
    (quittingLiveMass_nonneg reward profile time)
  exact hscaled.trans
    (quittingLiveMass_mul_spineDebt_le_initialDebt_of_prior_pureContinue
      reward profile who hM hreward time hprior)

/-- The selected player's live root in a pure-time deviation is exactly its
displayed deterministic pure-time hazard. -/
@[simp] theorem quittingProfileLiveRoot_update_pureTime_self
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (choice : Option ℕ) (time : ℕ) :
    quittingProfileLiveRoot reward
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who choice)) time who =
      quittingPureTimeHazard choice time := by
  unfold quittingProfileLiveRoot quittingPureTimeBehaviorStrategy
  simp

/-- Before a selected finite pure quit time, the deviator Continues purely. -/
theorem quittingProfileLiveRoot_update_pureTime_some_eq_pureContinue_of_lt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) {stage stop : ℕ} (hstage : stage < stop) :
    quittingProfileLiveRoot reward
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who (some stop)))
        stage who = PMF.pure false := by
  rw [quittingProfileLiveRoot_update_pureTime_self]
  exact quittingPureTimeHazard_some_of_ne (ne_of_lt hstage)

/-- A finite pure-time deviation has small survival-weighted local root
defect at every row up to and including its selected stop. -/
theorem quittingLiveMass_mul_coordinateNashDefect_update_pureTime_some_le_initialDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (stop time : ℕ) (htime : time ≤ stop)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    let deviated := Function.update profile who
      (quittingPureTimeBehaviorStrategy reward who (some stop))
    quittingLiveMass reward deviated time *
        quittingRootCoordinateNashDefect reward
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward deviated (time + 1))).1
          (quittingProfileLiveRoot reward deviated time) who ≤
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward deviated) who := by
  dsimp only
  apply quittingLiveMass_mul_coordinateNashDefect_le_initialDebt_of_prior_pureContinue
    reward _ who time hM hreward
  intro stage hstage
  exact
    quittingProfileLiveRoot_update_pureTime_some_eq_pureContinue_of_lt
      reward profile who (lt_of_lt_of_le hstage htime)

/-- A Never pure-time deviation has small survival-weighted local root defect
at every finite row. -/
theorem quittingLiveMass_mul_coordinateNashDefect_update_pureTime_none_le_initialDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (time : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    let deviated := Function.update profile who
      (quittingPureTimeBehaviorStrategy reward who none)
    quittingLiveMass reward deviated time *
        quittingRootCoordinateNashDefect reward
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward deviated (time + 1))).1
          (quittingProfileLiveRoot reward deviated time) who ≤
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward deviated) who := by
  dsimp only
  apply quittingLiveMass_mul_coordinateNashDefect_le_initialDebt_of_prior_pureContinue
    reward _ who time hM hreward
  intro stage _hstage
  rw [quittingProfileLiveRoot_update_pureTime_self,
    quittingPureTimeHazard_none]

/-- Coordinate defect-or-drift charge.  Opponent absorption can destroy tail
debt only to the extent paid for by a fall in that debt coordinate or by the
actual root's Nash defect. -/
theorem quittingRootOpponentAbsorptionMass_mul_debt_le_drift_add_nashDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (who : ι)
    (hdebt : 0 ≤ quittingTerminalSemanticDebt pair who) :
    quittingRootOpponentAbsorptionMass root who *
        quittingTerminalSemanticDebt pair who ≤
      quittingTerminalSemanticDebt pair who -
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPrefix reward root pair) who +
        quittingRootCoordinateNashDefect reward pair.1 root who := by
  have htransport :=
    quittingTerminalSemanticDebt_prefix_le_nashDefect_add_transport
      reward pair root who hdebt
  rw [quittingRootOpponentContinueMass_eq_one_sub_absorptionMass]
    at htransport
  nlinarith

/-- Summed defect-or-drift charge for an arbitrary semantic prefix. -/
theorem sum_opponentAbsorptionMass_mul_debt_le_sumDebt_drift_add_totalNashDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool)
    (hdebt : ∀ who, 0 ≤ quittingTerminalSemanticDebt pair who) :
    (∑ who, quittingRootOpponentAbsorptionMass root who *
        quittingTerminalSemanticDebt pair who) ≤
      quittingTerminalSemanticDebtSum pair -
          quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPrefix reward root pair) +
        quittingRootTotalNashDefect reward pair.1 root := by
  have hsum := Finset.sum_le_sum fun who (_hwho : who ∈ Finset.univ) =>
    quittingRootOpponentAbsorptionMass_mul_debt_le_drift_add_nashDefect
      reward pair root who (hdebt who)
  unfold quittingTerminalSemanticDebtSum quittingRootTotalNashDefect
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hsum
  exact hsum

/-- At a fixed minimum carrier point, the summed opponent-absorption charge
of any executable semantic prefix is paid by shifted-tail excess debt or by
the actual root's total Nash defect. -/
theorem minimumTerminalSemantic_sum_opponentAbsorption_charge_le_excess_add_defect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum tail : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (_hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (htail : tail ∈ quittingTerminalSemanticCarrier reward) :
    (∑ who, quittingRootOpponentAbsorptionMass root who *
        quittingTerminalSemanticDebt tail who) ≤
      (quittingTerminalSemanticDebtSum tail -
          quittingTerminalSemanticDebtSum minimum) +
        quittingRootTotalNashDefect reward tail.1 root := by
  have htailDebt : ∀ who, 0 ≤ quittingTerminalSemanticDebt tail who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hM hreward htail
  let current := quittingTerminalSemanticPrefix reward root tail
  have hcurrent : current ∈ quittingTerminalSemanticCarrier reward :=
    quittingTerminalSemanticPrefix_mem_carrier
      reward root tail hM hreward htail
  have hcharge :=
    sum_opponentAbsorptionMass_mul_debt_le_sumDebt_drift_add_totalNashDefect
      reward tail root htailDebt
  have hminCurrent : quittingTerminalSemanticDebtSum minimum ≤
      quittingTerminalSemanticDebtSum current :=
    hminimum current hcurrent
  dsimp only [current] at hminCurrent
  linarith

/-- The mass of an exact coalition is bounded by any displayed member's Quit
probability. -/
theorem quittingRootCoalitionMass_le_quitProbability_of_mem
    (root : ι → PMF Bool) (coalition : Finset ι) (marked : ι)
    (hmarked : marked ∈ coalition) :
    quittingRootCoalitionMass root coalition ≤
      (root marked true).toReal := by
  let rate : ι → ℝ := fun who => (root who true).toReal
  have hrateNonneg : ∀ who, 0 ≤ rate who := fun who => ENNReal.toReal_nonneg
  have hrateLeOne : ∀ who, rate who ≤ 1 := fun who =>
    ENNReal.toReal_mono ENNReal.one_ne_top ((root who).coe_le_one true)
  have hinsideNonneg : 0 ≤ ∏ who ∈ coalition, rate who :=
    Finset.prod_nonneg fun who _ => hrateNonneg who
  have houtsideNonneg : 0 ≤ ∏ who ∈ coalitionᶜ, (1 - rate who) :=
    Finset.prod_nonneg fun who _ => sub_nonneg.mpr (hrateLeOne who)
  have houtsideLeOne : (∏ who ∈ coalitionᶜ, (1 - rate who)) ≤ 1 :=
    Finset.prod_le_one
      (fun who _ => sub_nonneg.mpr (hrateLeOne who))
      (fun who _ => by linarith [hrateNonneg who])
  have hrestNonneg : 0 ≤ ∏ who ∈ coalition.erase marked, rate who :=
    Finset.prod_nonneg fun who _ => hrateNonneg who
  have hrestLeOne : (∏ who ∈ coalition.erase marked, rate who) ≤ 1 :=
    Finset.prod_le_one
      (fun who _ => hrateNonneg who)
      (fun who _ => hrateLeOne who)
  have hinside : (∏ who ∈ coalition, rate who) =
      (∏ who ∈ coalition.erase marked, rate who) * rate marked := by
    simpa using (Finset.prod_erase_mul coalition rate hmarked).symm
  unfold quittingRootCoalitionMass Math.PMFProduct.coalitionMass
    quittingRootQuitRates
  change (∏ who ∈ coalition, rate who) *
      (∏ who ∈ coalitionᶜ, (1 - rate who)) ≤ rate marked
  have hinsideLe : (∏ who ∈ coalition, rate who) ≤ rate marked := by
    rw [hinside]
    exact mul_le_of_le_one_left (hrateNonneg marked) hrestLeOne
  exact (mul_le_of_le_one_right hinsideNonneg houtsideLeOne).trans hinsideLe

/-- If the coalition contains an opponent of `who`, its exact mass is bounded
by `who`'s opponent-absorption hazard. -/
theorem quittingRootCoalitionMass_le_opponentAbsorptionMass_of_other_mem
    (root : ι → PMF Bool) (coalition : Finset ι) (who other : ι)
    (hother : other ∈ coalition) (hne : other ≠ who) :
    quittingRootCoalitionMass root coalition ≤
      quittingRootOpponentAbsorptionMass root who := by
  exact (quittingRootCoalitionMass_le_quitProbability_of_mem
    root coalition other hother).trans
      (quittingProbability_le_opponentAbsorptionMass root hne)

/-- A charged exact coalition at an arbitrary semantic prefix is paid by
coordinate debt drift or local Nash defect. -/
theorem quittingRootCoalitionMass_mul_debt_le_drift_add_nashDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (coalition : Finset ι) (who other : ι)
    (hdebt : 0 ≤ quittingTerminalSemanticDebt pair who)
    (hother : other ∈ coalition) (hne : other ≠ who) :
    quittingRootCoalitionMass root coalition *
        quittingTerminalSemanticDebt pair who ≤
      quittingTerminalSemanticDebt pair who -
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPrefix reward root pair) who +
        quittingRootCoordinateNashDefect reward pair.1 root who := by
  have hmass :=
    quittingRootCoalitionMass_le_opponentAbsorptionMass_of_other_mem
      root coalition who other hother hne
  have hscaled := mul_le_mul_of_nonneg_right hmass hdebt
  exact hscaled.trans
    (quittingRootOpponentAbsorptionMass_mul_debt_le_drift_add_nashDefect
      reward pair root who hdebt)

/-- Actual chronological version of the coalition charge.  Survival can only
decrease the charged coalition mass. -/
theorem quittingStageCoalitionMass_mul_tailDebt_le_drift_add_nashDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) (who other : ι)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hother : other ∈ terminal.val) (hne : other ≠ who) :
    let tail := quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (time + 1))
    let current := quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile time)
    quittingStageCoalitionMass reward profile time terminal *
        quittingTerminalSemanticDebt tail who ≤
      quittingTerminalSemanticDebt tail who -
          quittingTerminalSemanticDebt current who +
        quittingRootCoordinateNashDefect reward tail.1
          (quittingProfileLiveRoot reward profile time) who := by
  dsimp only
  let tail := quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward profile (time + 1))
  let root := quittingProfileLiveRoot reward profile time
  have htailCarrier : tail ∈ quittingTerminalSemanticCarrier reward :=
    quittingTerminalSemanticPair_mem_carrier reward _
  have htailDebt : 0 ≤ quittingTerminalSemanticDebt tail who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hM hreward htailCarrier who
  have hrootCharge :=
    quittingRootCoalitionMass_mul_debt_le_drift_add_nashDefect
      reward tail root terminal.val who other htailDebt hother hne
  have hliveLeOne : quittingLiveMass reward profile time ≤ 1 :=
    quittingLiveMass_le_one reward profile time
  have hcoalitionNonneg :=
    MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg root terminal.val
  have hstageLe : quittingStageCoalitionMass reward profile time terminal ≤
      quittingRootCoalitionMass root terminal.val := by
    rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass]
    nlinarith [quittingLiveMass_nonneg reward profile time]
  have hscaled := mul_le_mul_of_nonneg_right hstageLe htailDebt
  rw [quittingTerminalSemanticPair_spine_eq_prefix
    reward profile time hM hreward]
  exact hscaled.trans hrootCharge

/-- Survival-weighted live-row charge with the local Nash defect discharged
against the initial semantic debt.  For a near-best pure-time profile the
only remaining local term is the survival-weighted tail-debt drift. -/
theorem quittingStageCoalitionMass_mul_tailDebt_le_liveMass_mul_drift_add_initialDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) (who other : ι)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hprior : ∀ stage < time,
      quittingProfileLiveRoot reward profile stage who = PMF.pure false)
    (hother : other ∈ terminal.val) (hne : other ≠ who) :
    let tail := quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (time + 1))
    let current := quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile time)
    quittingStageCoalitionMass reward profile time terminal *
        quittingTerminalSemanticDebt tail who ≤
      quittingLiveMass reward profile time *
          (quittingTerminalSemanticDebt tail who -
            quittingTerminalSemanticDebt current who) +
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) who := by
  dsimp only
  let tail := quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward profile (time + 1))
  let current := quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward profile time)
  let root := quittingProfileLiveRoot reward profile time
  have htailCarrier : tail ∈ quittingTerminalSemanticCarrier reward :=
    quittingTerminalSemanticPair_mem_carrier reward _
  have htailDebt : 0 ≤ quittingTerminalSemanticDebt tail who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hM hreward htailCarrier who
  have hrootCharge :=
    quittingRootCoalitionMass_mul_debt_le_drift_add_nashDefect
      reward tail root terminal.val who other htailDebt hother hne
  have hliveNonneg := quittingLiveMass_nonneg reward profile time
  have hweightedCharge := mul_le_mul_of_nonneg_left hrootCharge hliveNonneg
  have hdefect :=
    quittingLiveMass_mul_coordinateNashDefect_le_initialDebt_of_prior_pureContinue
      reward profile who time hM hreward hprior
  have hprefix : current = quittingTerminalSemanticPrefix reward root tail := by
    dsimp only [current, root, tail]
    exact quittingTerminalSemanticPair_spine_eq_prefix
      reward profile time hM hreward
  rw [← hprefix] at hweightedCharge
  rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass]
  change (quittingLiveMass reward profile time *
      quittingRootCoalitionMass root terminal.val) *
        quittingTerminalSemanticDebt tail who ≤ _
  calc
    (quittingLiveMass reward profile time *
        quittingRootCoalitionMass root terminal.val) *
          quittingTerminalSemanticDebt tail who =
      quittingLiveMass reward profile time *
        (quittingRootCoalitionMass root terminal.val *
          quittingTerminalSemanticDebt tail who) := by ring
    _ ≤ quittingLiveMass reward profile time *
        (quittingTerminalSemanticDebt tail who -
            quittingTerminalSemanticDebt current who +
          quittingRootCoordinateNashDefect reward tail.1 root who) :=
      hweightedCharge
    _ = quittingLiveMass reward profile time *
          (quittingTerminalSemanticDebt tail who -
            quittingTerminalSemanticDebt current who) +
        quittingLiveMass reward profile time *
          quittingRootCoordinateNashDefect reward tail.1 root who := by ring
    _ ≤ quittingLiveMass reward profile time *
          (quittingTerminalSemanticDebt tail who -
            quittingTerminalSemanticDebt current who) +
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) who :=
      by linarith

/-- With no positive tail-debt drift, the entire charged stage atom is paid
by the profile's initial debt.  Thus a near-best pure-time profile can retain
a nontrivial charged atom only by entering a strictly higher-debt suffix. -/
theorem quittingStageCoalitionMass_mul_tailDebt_le_initialDebt_of_no_positive_drift
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) (who other : ι)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hprior : ∀ stage < time,
      quittingProfileLiveRoot reward profile stage who = PMF.pure false)
    (hother : other ∈ terminal.val) (hne : other ≠ who)
    (hdrift : quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward profile (time + 1))) who ≤
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward profile time)) who) :
    quittingStageCoalitionMass reward profile time terminal *
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward profile (time + 1))) who ≤
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) who := by
  have hcharge :=
    quittingStageCoalitionMass_mul_tailDebt_le_liveMass_mul_drift_add_initialDebt
      reward profile time terminal who other hM hreward hprior hother hne
  have hliveNonneg := quittingLiveMass_nonneg reward profile time
  have hweightedDrift : quittingLiveMass reward profile time *
      (quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward profile (time + 1))) who -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward profile time)) who) ≤ 0 := by
    exact mul_nonpos_of_nonneg_of_nonpos hliveNonneg (sub_nonpos.mpr hdrift)
  linarith

/-- Contrapositive form: if a charged stage atom exceeds the initial debt,
the selected player's semantic debt must strictly increase across that live
row. -/
theorem terminalSemanticDebt_spine_lt_succ_of_initialDebt_lt_stageCharge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) (who other : ι)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hprior : ∀ stage < time,
      quittingProfileLiveRoot reward profile stage who = PMF.pure false)
    (hother : other ∈ terminal.val) (hne : other ≠ who)
    (hlarge : quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) who <
      quittingStageCoalitionMass reward profile time terminal *
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward profile (time + 1))) who) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward profile time)) who <
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward profile (time + 1))) who := by
  by_contra hnot
  have hdrift := le_of_not_gt hnot
  have hcharge :=
    quittingStageCoalitionMass_mul_tailDebt_le_initialDebt_of_no_positive_drift
      reward profile time terminal who other hM hreward hprior hother hne hdrift
  exact (not_lt_of_ge hcharge) hlarge

end GameTheory
