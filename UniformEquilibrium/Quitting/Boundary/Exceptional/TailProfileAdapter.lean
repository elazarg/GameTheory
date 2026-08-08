/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Exceptional.TailFallback
import UniformEquilibrium.Quitting.Cycles.BehaviorPureTimeExtremality
import UniformEquilibrium.Quitting.Boundary.Exceptional.TailLimits

/-!
# Canonical profile adapter for the exceptional stationary fallback

The all-continue spine of one behavior profile supplies the roots and tail
profiles consumed by the exceptional fallback.  Positive global survival of
the exceptional player's opponents identifies every conditional tail survival
limit as a quotient.  Consequently the probability that an opponent quits in
the conditional tail tends to zero, and it dominates the current one-stage
opponent hazard.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Live roots of a shifted all-continue spine are the corresponding suffix
of the original live-root sequence. -/
theorem quittingProfileLiveRoot_allContinueSpine
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (start time : ℕ) :
    quittingProfileLiveRoot reward
        (quittingAllContinueProfileSpine reward profile start) time =
      quittingProfileLiveRoot reward profile (start + time) := by
  funext player
  unfold quittingProfileLiveRoot
  exact quittingAllContinueProfileSpine_apply_liveHist
    reward profile start player time

/-- Opponent survival from an original live cutoff is the opponent-only live
mass of the corresponding shifted profile. -/
theorem quittingOpponentSurvivalWeight_eq_liveMass_allContinueSpine
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (owner : ι) (start : ℕ) :
    ∀ fuel,
      quittingOpponentSurvivalWeight
          (quittingProfileLiveRoot reward profile) owner start fuel =
        quittingLiveMass reward
          (quittingOpponentOnlyProfile reward
            (quittingAllContinueProfileSpine reward profile start) owner)
          fuel := by
  intro fuel
  let tail := quittingAllContinueProfileSpine reward profile start
  have htailRoots : quittingProfileLiveRoot reward tail =
      fun time => quittingProfileLiveRoot reward profile (start + time) := by
    funext time
    exact quittingProfileLiveRoot_allContinueSpine
      reward profile start time
  have hweights :=
    quittingOpponentSurvivalWeight_profileLiveRoot_eq_liveMass
      reward tail owner fuel
  rw [htailRoots] at hweights
  calc
    quittingOpponentSurvivalWeight
          (quittingProfileLiveRoot reward profile) owner start fuel =
        quittingOpponentSurvivalWeight
          (fun time => quittingProfileLiveRoot reward profile (start + time))
          owner 0 fuel := by
      unfold quittingOpponentSurvivalWeight
      apply Finset.prod_congr rfl
      intro offset _
      unfold quittingFixedOpponentsContinueMass
      simp only [Nat.zero_add]
    _ = quittingLiveMass reward
          (quittingOpponentOnlyProfile reward tail owner) fuel := hweights

/-- Positive global opponent survival gives the exact conditional tail
survival quotient at every live cutoff. -/
theorem quittingOpponentLiveMassLimit_allContinueSpine_eq_ratio
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (owner : ι)
    (hpositive : 0 < quittingLiveMassLimit reward
      (quittingOpponentOnlyProfile reward profile owner))
    (start : ℕ) :
    quittingLiveMassLimit reward
        (quittingOpponentOnlyProfile reward
          (quittingAllContinueProfileSpine reward profile start) owner) =
      quittingLiveMassLimit reward
          (quittingOpponentOnlyProfile reward profile owner) /
        quittingLiveMass reward
          (quittingOpponentOnlyProfile reward profile owner) start := by
  let roots := quittingProfileLiveRoot reward profile
  let opponentProfile := quittingOpponentOnlyProfile reward profile owner
  let limit := quittingLiveMassLimit reward opponentProfile
  let tailOpponentProfile := quittingOpponentOnlyProfile reward
    (quittingAllContinueProfileSpine reward profile start) owner
  have hglobal : Tendsto
      (quittingOpponentSurvivalWeight roots owner 0) atTop (nhds limit) := by
    have hweights : quittingOpponentSurvivalWeight roots owner 0 =
        quittingLiveMass reward opponentProfile := by
      funext fuel
      exact quittingOpponentSurvivalWeight_profileLiveRoot_eq_liveMass
        reward profile owner fuel
    rw [hweights]
    exact tendsto_quittingLiveMass reward opponentProfile
  have htail := tendsto_quittingOpponentSurvivalWeight_tail
    roots owner limit hglobal hpositive start
  have htailLive : Tendsto
      (quittingLiveMass reward tailOpponentProfile) atTop
      (nhds (limit /
        quittingOpponentSurvivalWeight roots owner 0 start)) := by
    apply htail.congr'
    exact Filter.Eventually.of_forall fun fuel =>
      (by
        simpa [roots, tailOpponentProfile] using
          (quittingOpponentSurvivalWeight_eq_liveMass_allContinueSpine
            reward profile owner start fuel))
  have heq := tendsto_nhds_unique
    (tendsto_quittingLiveMass reward tailOpponentProfile) htailLive
  simpa only [roots, opponentProfile, limit, tailOpponentProfile,
    quittingOpponentSurvivalWeight_profileLiveRoot_eq_liveMass] using heq

/-- Conditional probability that some opponent of `owner` eventually quits
after the selected live cutoff. -/
def quittingExceptionalTailError
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (owner : ι) (start : ℕ) : ℝ :=
  1 - quittingLiveMassLimit reward
    (quittingOpponentOnlyProfile reward
      (quittingAllContinueProfileSpine reward profile start) owner)

/-- Exceptional tail errors are nonnegative. -/
theorem quittingExceptionalTailError_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (owner : ι) (start : ℕ) :
    0 ≤ quittingExceptionalTailError reward profile owner start := by
  unfold quittingExceptionalTailError
  apply sub_nonneg.mpr
  have hle := quittingLiveMassLimit_le reward
    (quittingOpponentOnlyProfile reward
      (quittingAllContinueProfileSpine reward profile start) owner) 0
  simpa using hle

/-- Positive global opponent survival makes the conditional opponent-quit
probability tend to zero along the live spine. -/
theorem tendsto_quittingExceptionalTailError_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (owner : ι)
    (hpositive : 0 < quittingLiveMassLimit reward
      (quittingOpponentOnlyProfile reward profile owner)) :
    Tendsto (quittingExceptionalTailError reward profile owner)
      atTop (nhds 0) := by
  let roots := quittingProfileLiveRoot reward profile
  let opponentProfile := quittingOpponentOnlyProfile reward profile owner
  let limit := quittingLiveMassLimit reward opponentProfile
  have hglobal : Tendsto
      (quittingOpponentSurvivalWeight roots owner 0) atTop (nhds limit) := by
    have hweights : quittingOpponentSurvivalWeight roots owner 0 =
        quittingLiveMass reward opponentProfile := by
      funext fuel
      exact quittingOpponentSurvivalWeight_profileLiveRoot_eq_liveMass
        reward profile owner fuel
    rw [hweights]
    exact tendsto_quittingLiveMass reward opponentProfile
  have hratio := tendsto_quittingOpponentSurvivalLimitRatio_one
    roots owner limit hglobal hpositive
  have hratioLive : Tendsto (fun start =>
      limit / quittingLiveMass reward opponentProfile start)
      atTop (nhds 1) := by
    simpa only [roots, opponentProfile,
      quittingOpponentSurvivalWeight_profileLiveRoot_eq_liveMass] using hratio
  have hsub : Tendsto (fun start : ℕ =>
      (1 : ℝ) - limit / quittingLiveMass reward opponentProfile start)
      atTop (nhds 0) := by
    simpa using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ))
        atTop (nhds 1)).sub hratioLive)
  apply hsub.congr'
  filter_upwards [] with start
  rw [quittingExceptionalTailError,
    quittingOpponentLiveMassLimit_allContinueSpine_eq_ratio
      reward profile owner hpositive]

/-- The current one-stage opponent hazard is no larger than the probability
that an opponent eventually quits in the corresponding conditional tail. -/
theorem one_sub_fixedOpponentsContinueMass_le_exceptionalTailError
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (owner : ι) (start : ℕ) :
    1 - quittingStationaryFixedOpponentsContinueMass
        (quittingProfileLiveRoot reward profile start) owner ≤
      quittingExceptionalTailError reward profile owner start := by
  let tail := quittingAllContinueProfileSpine reward profile start
  let tailOpponentProfile :=
    quittingOpponentOnlyProfile reward tail owner
  have hlimit := quittingLiveMassLimit_le reward tailOpponentProfile 1
  have hone : quittingLiveMass reward tailOpponentProfile 1 =
      quittingStationaryFixedOpponentsContinueMass
        (quittingProfileLiveRoot reward profile start) owner := by
    rw [show (1 : ℕ) = 0 + 1 by omega, quittingLiveMass_succ,
      quittingLiveMass_zero, one_mul,
      ← quittingFixedOpponentsContinueMass_profileLiveRoot
        reward tail owner 0]
    dsimp only [tail]
    unfold quittingStationaryFixedOpponentsContinueMass
      quittingFixedOpponentsContinueMass
    rw [quittingProfileLiveRoot_allContinueSpine reward profile start 0]
    rfl
  unfold quittingExceptionalTailError
  dsimp only [tailOpponentProfile, tail] at hlimit hone ⊢
  rw [hone] at hlimit
  linarith

/-! ## Tail-Nash endpoint adapters -/

omit [DecidableEq ι] in
/-- A reward bound scales with the total limiting absorption mass, rather
than merely giving the coarser uniform bound `M`. -/
theorem abs_quittingTerminalPayoff_le_absorbedMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    {M : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    |quittingTerminalPayoff reward profile who| ≤
      M * (1 - quittingLiveMassLimit reward profile) := by
  classical
  have hconservation :=
    quittingLiveMassLimit_add_sum_absorbedMassLimit reward profile
  unfold quittingTerminalPayoff
  calc
    |∑ terminal,
        quittingAbsorbedMassLimit reward profile terminal *
          reward terminal who| ≤
      ∑ terminal,
        |quittingAbsorbedMassLimit reward profile terminal *
          reward terminal who| := by
      simpa using Finset.abs_sum_le_sum_abs
        (fun terminal =>
          quittingAbsorbedMassLimit reward profile terminal *
            reward terminal who)
        Finset.univ
    _ = ∑ terminal,
        quittingAbsorbedMassLimit reward profile terminal *
          |reward terminal who| := by
      apply Finset.sum_congr rfl
      intro terminal _
      rw [abs_mul, abs_of_nonneg]
      exact quittingAbsorbedMassLimit_nonneg reward profile terminal
    _ ≤ ∑ terminal,
        quittingAbsorbedMassLimit reward profile terminal * M := by
      apply Finset.sum_le_sum
      intro terminal _
      exact mul_le_mul_of_nonneg_left (hreward terminal who)
        (quittingAbsorbedMassLimit_nonneg reward profile terminal)
    _ = M * (∑ terminal,
        quittingAbsorbedMassLimit reward profile terminal) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro terminal _
      ring
    _ = M * (1 - quittingLiveMassLimit reward profile) := by
      congr 1
      linarith

omit [DecidableEq ι] in
/-- The pure-time `Never` behavior strategy is the standard always-continue
strategy. -/
theorem quittingPureTimeBehaviorStrategy_none_eq_alwaysContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    quittingPureTimeBehaviorStrategy reward who none =
      quittingAlwaysContinueStrategy reward who := by
  funext time history
  rfl

/-- `Never` receives payoff of magnitude at most `M` times the probability
that an opponent eventually absorbs the game. -/
theorem abs_quittingTerminalPayoff_update_never_le_opponentTail
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    {M : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    |quittingTerminalPayoff reward
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who none)) who| ≤
      M * (1 - quittingLiveMassLimit reward
        (quittingOpponentOnlyProfile reward profile who)) := by
  have hprofile :
      Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who none) =
        quittingOpponentOnlyProfile reward profile who := by
    rw [quittingOpponentOnlyProfile,
      quittingPureTimeBehaviorStrategy_none_eq_alwaysContinue]
  rw [hprofile]
  exact abs_quittingTerminalPayoff_le_absorbedMass
    reward _ who hreward

/-- Quitting at the current live stage realizes exactly the stationary
fixed-opponents Quit value of the current live root. -/
theorem quittingTerminalPayoff_update_quitNow_eq_fixedOpponentsQuitValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingTerminalPayoff reward
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who (some 0))) who =
      quittingStationaryFixedOpponentsQuitValue reward
        (quittingProfileLiveRoot reward profile 0) who := by
  rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy]
  unfold quittingRootSequencePureTimeTerminalValue
  rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman]
  simp only [quittingPureTimeHazard_some_self, PMF.pure_apply, ↓reduceIte,
    ENNReal.toReal_one, one_mul, Bool.false_eq_true, ENNReal.toReal_zero,
    zero_add, zero_mul, add_zero]
  unfold quittingFixedOpponentsQuitValue
  rfl

/-- Terminal `β`-Nash at a tail implies the immediate-Quit inequality used
by the exceptional fallback. -/
theorem quittingFixedOpponentsQuitValue_le_terminal_add_of_isεNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) {β : ℝ}
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) β profile) :
    quittingStationaryFixedOpponentsQuitValue reward
        (quittingProfileLiveRoot reward profile 0) who ≤
      quittingTerminalPayoff reward profile who + β := by
  rw [← quittingTerminalPayoff_update_quitNow_eq_fixedOpponentsQuitValue]
  exact hnash who
    (quittingPureTimeBehaviorStrategy reward who (some 0))

/-- Terminal `β`-Nash at a tail, tested against `Never`, gives the lower
inequality used for the exceptional owner's singleton reward. -/
theorem neg_opponentTail_le_terminal_add_of_isεNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) {β M : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) β profile) :
    -M * (1 - quittingLiveMassLimit reward
        (quittingOpponentOnlyProfile reward profile who)) ≤
      quittingTerminalPayoff reward profile who + β := by
  have hneverLower :
      -(M * (1 - quittingLiveMassLimit reward
          (quittingOpponentOnlyProfile reward profile who))) ≤
        quittingTerminalPayoff reward
          (Function.update profile who
            (quittingPureTimeBehaviorStrategy reward who none)) who :=
    neg_le_of_abs_le
      (abs_quittingTerminalPayoff_update_never_le_opponentTail
        reward profile who hreward)
  have hneverNash := hnash who
    (quittingPureTimeBehaviorStrategy reward who none)
  calc
    -M * (1 - quittingLiveMassLimit reward
          (quittingOpponentOnlyProfile reward profile who)) =
        -(M * (1 - quittingLiveMassLimit reward
          (quittingOpponentOnlyProfile reward profile who))) := by ring
    _ ≤ quittingTerminalPayoff reward
          (Function.update profile who
            (quittingPureTimeBehaviorStrategy reward who none)) who :=
      hneverLower
    _ ≤ quittingTerminalPayoff reward profile who + β := hneverNash

/-- A genuinely negative terminal target forces a quantitatively visible
opponent fence under the owner's deletion.  More precisely, if terminal
beta-Nash leaves the player at least delta below zero, then the probability
that some opponent eventually absorbs is at least delta divided by the reward
bound, stated here in division-free form.

This is the first marked-boundary estimate: an ordinary time occupation may
lose a zero-density fence, but the owner-deletion law must retain enough of
that fence to finance the negative terminal payoff. -/
theorem delta_le_mul_opponentTail_of_terminal_add_le_neg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) {β M δ : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) β profile)
    (hnegative :
      quittingTerminalPayoff reward profile who + β ≤ -δ) :
    δ ≤ M * (1 - quittingLiveMassLimit reward
      (quittingOpponentOnlyProfile reward profile who)) := by
  have hfence := neg_opponentTail_le_terminal_add_of_isεNash
    reward profile who hreward hnash
  linarith

/-! ## End-to-end exceptional profile adapter -/

/-- If every live tail absorbs almost surely while `owner`'s opponents have
positive global survival probability, then `owner` has a positive quit hazard
arbitrarily late on the live path. -/
theorem exists_late_positive_owner_hazard_of_absorbing_tails
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (owner : ι)
    (habsorbs : ∀ start,
      quittingLiveMassLimit reward
        (quittingAllContinueProfileSpine reward profile start) = 0)
    (hpositive : 0 < quittingLiveMassLimit reward
      (quittingOpponentOnlyProfile reward profile owner)) :
    ∀ threshold, ∃ time ≥ threshold,
      0 < (quittingProfileLiveRoot reward profile time owner true).toReal := by
  intro threshold
  by_contra hlate
  let tail := quittingAllContinueProfileSpine reward profile threshold
  let tailOpponentProfile := quittingOpponentOnlyProfile reward tail owner
  have hownerFalse : ∀ time,
      ((tail owner time (quittingLiveHist reward time)) false).toReal = 1 := by
    intro time
    have hroot := quittingAllContinueProfileSpine_apply_liveHist
      reward profile threshold owner time
    have hnotpos : ¬0 <
        (quittingProfileLiveRoot reward profile
          (threshold + time) owner true).toReal := by
      intro hpos
      apply hlate
      exact ⟨threshold + time, Nat.le_add_right threshold time, hpos⟩
    have htrue :
        (quittingProfileLiveRoot reward profile
          (threshold + time) owner true).toReal = 0 :=
      le_antisymm (le_of_not_gt hnotpos) ENNReal.toReal_nonneg
    have hsum := pmf_toReal_sum_one
      (quittingProfileLiveRoot reward profile (threshold + time) owner)
    rw [Fintype.sum_bool] at hsum
    have htailRoot :
        tail owner time (quittingLiveHist reward time) =
          profile owner (threshold + time)
            (quittingLiveHist reward (threshold + time)) := by
      simpa [tail] using hroot
    rw [htailRoot]
    unfold quittingProfileLiveRoot at htrue hsum
    rw [htrue, zero_add] at hsum
    exact hsum
  have hstage : ∀ time,
      quittingJointContinueMass reward tail time =
        quittingJointContinueMass reward tailOpponentProfile time := by
    intro time
    rw [quittingJointContinueMass_eq_product,
      quittingJointContinueMass_opponentOnly_eq_product]
    apply Finset.prod_congr rfl
    intro player _
    by_cases hp : player = owner
    · subst player
      simp [hownerFalse time]
    · simp [hp]
  have hlive : ∀ time,
      quittingLiveMass reward tail time =
        quittingLiveMass reward tailOpponentProfile time := by
    intro time
    induction time with
    | zero => simp
    | succ time ih =>
        rw [quittingLiveMass_succ, quittingLiveMass_succ, ih, hstage]
  have hlimitEq : quittingLiveMassLimit reward tail =
      quittingLiveMassLimit reward tailOpponentProfile := by
    unfold quittingLiveMassLimit
    congr 1
    funext time
    exact hlive time
  have hprefixPos : 0 < quittingLiveMass reward
      (quittingOpponentOnlyProfile reward profile owner) threshold :=
    hpositive.trans_le
      (quittingLiveMassLimit_le reward
        (quittingOpponentOnlyProfile reward profile owner) threshold)
  have htailOpponentPos :
      0 < quittingLiveMassLimit reward tailOpponentProfile := by
    rw [show quittingLiveMassLimit reward tailOpponentProfile =
      quittingLiveMassLimit reward
          (quittingOpponentOnlyProfile reward profile owner) /
        quittingLiveMass reward
          (quittingOpponentOnlyProfile reward profile owner) threshold by
      simpa [tailOpponentProfile, tail] using
        quittingOpponentLiveMassLimit_allContinueSpine_eq_ratio
          reward profile owner hpositive threshold]
    exact div_pos hpositive hprefixPos
  have htailZero : quittingLiveMassLimit reward tail = 0 := by
    simpa [tail] using habsorbs threshold
  rw [← hlimitEq, htailZero] at htailOpponentPos
  exact lt_irrefl 0 htailOpponentPos

/-- A single behavior profile closes the exceptional stationary fallback when
every canonical live tail is an absorbing terminal `β`-Nash profile and the
exceptional player's opponents survive forever with positive probability.
All roots, tails, tail errors, endpoint inequalities, and late positive owner
hazards are derived canonically from that profile. -/
theorem exists_isεAsymptoticNash_soloStationary_of_exceptional_profile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (owner : ι) {β M : ℝ}
    (hβ : 0 ≤ β) (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (habsorbs : ∀ start,
      quittingLiveMassLimit reward
        (quittingAllContinueProfileSpine reward profile start) = 0)
    (htailNash : ∀ start,
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) β
        (quittingAllContinueProfileSpine reward profile start))
    (hpositive : 0 < quittingLiveMassLimit reward
      (quittingOpponentOnlyProfile reward profile owner)) :
    ∀ ζ > 0, ∃ time,
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) (β + ζ)
        (quittingStationaryProfile reward
          (quittingSoloStationaryRoot owner
            (quittingProfileLiveRoot reward profile time owner))) := by
  let roots := quittingProfileLiveRoot reward profile
  let tails := quittingAllContinueProfileSpine reward profile
  let η := quittingExceptionalTailError reward profile owner
  apply exists_isεAsymptoticNash_soloStationary_of_absorbing_tails
    reward roots tails owner η hβ hM hreward
  · exact quittingExceptionalTailError_nonneg reward profile owner
  · exact tendsto_quittingExceptionalTailError_zero
      reward profile owner hpositive
  · exact habsorbs
  · intro time
    exact le_rfl
  · exact one_sub_fixedOpponentsContinueMass_le_exceptionalTailError
      reward profile owner
  · exact exists_late_positive_owner_hazard_of_absorbing_tails
      reward profile owner habsorbs hpositive
  · intro time
    simpa [η, tails, quittingExceptionalTailError] using
      (neg_opponentTail_le_terminal_add_of_isεNash
        reward (quittingAllContinueProfileSpine reward profile time) owner
          hreward (htailNash time))
  · intro time who _hne
    have hquit :=
      quittingFixedOpponentsQuitValue_le_terminal_add_of_isεNash
        reward (quittingAllContinueProfileSpine reward profile time) who
          (htailNash time)
    rw [quittingProfileLiveRoot_allContinueSpine
      reward profile time 0] at hquit
    simpa [roots, tails] using hquit

end GameTheory
