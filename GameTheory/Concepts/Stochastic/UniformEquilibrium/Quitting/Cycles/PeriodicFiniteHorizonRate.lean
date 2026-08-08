/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Cycles.PeriodicClosing
import Math.SqrtRate
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Paths.AlmostSureOpponentUniformization

/-!
# Finite-horizon rates for periodic quitting certificates

The periodic closing machinery produces a player-specific terminal deviation
charge.  This file first packages those charges as a terminal behavioral
approximate Nash equilibrium.  It then combines that terminal error with
explicit finite-horizon delivery and deviation-boundary estimates.

For an accuracy-indexed mesh, a terminal charge of order `A / m` and a
finite-horizon boundary charge of order `B * m / N` give the game-facing
`(A + 2 * B) / sqrt N` Nash bound.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math Math.Probability Math.PMFProduct

variable {K : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Explicit opponent-survival boundary -/

/-- Cesàro average of the probability that all opponents of `player` have
continued under a profile. -/
def quittingOpponentLiveCesaro
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (player : ι) (horizon : ℕ) : ℝ :=
  (horizon : ℝ)⁻¹ * ∑ time ∈ Finset.range horizon,
    quittingLiveMass reward
      (quittingOpponentOnlyProfile reward profile player) time

/-- The profile's own live mass is bounded by every player's opponent-only
live mass. -/
theorem quittingLiveMass_le_opponentOnly
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (player : ι) (time : ℕ) :
    quittingLiveMass reward profile time ≤
      quittingLiveMass reward
        (quittingOpponentOnlyProfile reward profile player) time := by
  have hupdate : Function.update profile player (profile player) = profile := by
    funext other
    by_cases hother : other = player
    · subst other
      simp
    · simp [hother]
  have hlive := quittingLiveMass_update_le_opponentOnly
    reward profile player (profile player) time
  rw [hupdate] at hlive
  exact hlive

/-- Quantitative prescribed-play delivery: its finite average differs from
its terminal payoff by at most the reward bound times the opponent-live
Cesàro clock. -/
theorem abs_finiteAveragePayoff_sub_terminal_le_opponentLiveCesaro
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (player : ι) (horizon : ℕ) (hhorizon : 0 < horizon)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hreward : ∀ S, |reward S player| ≤ bound) :
    |(quittingGame reward).finiteAveragePayoff none horizon profile player -
        quittingTerminalPayoff reward profile player| ≤
      bound * quittingOpponentLiveCesaro reward profile player horizon := by
  letI : Finite (quittingGame reward).State :=
    inferInstanceAs (Finite (Option {S : Finset ι // S.Nonempty}))
  letI : ∀ who : ι, Finite ((quittingGame reward).Act who) :=
    fun _ ↦ inferInstanceAs (Finite Bool)
  rw [(quittingGame reward).finiteAveragePayoff_eq_sum_expectedStagePayoff]
  have hhorizonReal : (horizon : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hhorizon)
  have hrewrite :
      (horizon : ℝ)⁻¹ * ∑ time ∈ Finset.range horizon,
          (quittingGame reward).expectedStagePayoff
            profile none time player -
        quittingTerminalPayoff reward profile player =
      (horizon : ℝ)⁻¹ * ∑ time ∈ Finset.range horizon,
        ((quittingGame reward).expectedStagePayoff
            profile none time player -
          quittingTerminalPayoff reward profile player) := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  rw [hrewrite, abs_mul, abs_of_nonneg (by positivity)]
  calc
    (horizon : ℝ)⁻¹ *
          |∑ time ∈ Finset.range horizon,
            ((quittingGame reward).expectedStagePayoff
                profile none time player -
              quittingTerminalPayoff reward profile player)| ≤
        (horizon : ℝ)⁻¹ *
          ∑ time ∈ Finset.range horizon,
            |(quittingGame reward).expectedStagePayoff
                profile none time player -
              quittingTerminalPayoff reward profile player| := by
      exact mul_le_mul_of_nonneg_left
        (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ (horizon : ℝ)⁻¹ *
          ∑ time ∈ Finset.range horizon,
            bound * quittingLiveMass reward profile time := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro time _
      have htail :=
        abs_quittingTerminalPayoff_sub_expectedStagePayoff_le_liveTail
          reward profile time player bound hreward
      have hlimit := quittingLiveMassLimit_nonneg reward profile
      have hdrop :
          bound * (quittingLiveMass reward profile time -
              quittingLiveMassLimit reward profile) ≤
            bound * quittingLiveMass reward profile time := by
        nlinarith
      simpa only [abs_sub_comm] using htail.trans hdrop
    _ ≤ (horizon : ℝ)⁻¹ *
          ∑ time ∈ Finset.range horizon,
            bound * quittingLiveMass reward
              (quittingOpponentOnlyProfile reward profile player) time := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro time _
      exact mul_le_mul_of_nonneg_left
        (quittingLiveMass_le_opponentOnly reward profile player time) hbound
    _ = bound * quittingOpponentLiveCesaro
          reward profile player horizon := by
      unfold quittingOpponentLiveCesaro
      rw [← Finset.mul_sum]
      ring

/-- The standard unilateral finite-horizon comparison written with the
shared opponent-live Cesàro clock. -/
theorem finiteAveragePayoff_update_le_terminal_add_opponentLiveCesaro'
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (player : ι)
    (deviation : (quittingGame reward).BehaviorStrategy player)
    (horizon : ℕ) (hhorizon : 0 < horizon)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hreward : ∀ S, |reward S player| ≤ bound) :
    (quittingGame reward).finiteAveragePayoff none horizon
        (Function.update profile player deviation) player ≤
      quittingTerminalPayoff reward
          (Function.update profile player deviation) player +
        bound * quittingOpponentLiveCesaro
          reward profile player horizon := by
  simpa only [quittingOpponentLiveCesaro] using
    (finiteAveragePayoff_update_le_terminal_add_opponentLiveCesaro
      reward profile player deviation horizon hhorizon bound hbound hreward)

/-! ## Cyclic survival accounting -/

/-- The total mass of any finite prefix of a contracting cyclic survival
clock is at most one cycle length divided by its one-cycle contraction gap.
This is the quantitative `O(period)` boundary estimate. -/
theorem sum_quittingCyclicPrefixWeight_le_card_div_one_sub_prod
    (coefficient : Fin K → ℝ)
    (hcoefficient0 : ∀ cyclePhase, 0 ≤ coefficient cyclePhase)
    (hcoefficient1 : ∀ cyclePhase, coefficient cyclePhase ≤ 1)
    (phase : Fin K)
    (hcycle : (∏ cyclePhase : Fin K, coefficient cyclePhase) < 1)
    (horizon : ℕ) :
    (∑ time ∈ Finset.range horizon,
        quittingCyclicPrefixWeight coefficient phase time) ≤
      (K : ℝ) / (1 - ∏ cyclePhase : Fin K,
        coefficient cyclePhase) := by
  let ρ : ℝ := ∏ cyclePhase : Fin K, coefficient cyclePhase
  have hρ0 : 0 ≤ ρ :=
    Finset.prod_nonneg (fun cyclePhase _ ↦ hcoefficient0 cyclePhase)
  have hblock : ∀ turns : ℕ,
      (∑ time ∈ Finset.range (turns * K),
          quittingCyclicPrefixWeight coefficient phase time) ≤
        (K : ℝ) * ∑ turn ∈ Finset.range turns, ρ ^ turn := by
    intro turns
    induction turns with
    | zero => simp
    | succ turns ih =>
        have honeBlock :
            (∑ offset ∈ Finset.range K,
                quittingCyclicPrefixWeight coefficient phase
                  (turns * K + offset)) ≤
              (K : ℝ) * ρ ^ turns := by
          calc
            (∑ offset ∈ Finset.range K,
                quittingCyclicPrefixWeight coefficient phase
                  (turns * K + offset)) ≤
                ∑ _offset ∈ Finset.range K, ρ ^ turns := by
              apply Finset.sum_le_sum
              intro offset _
              have hmono := antitone_quittingCyclicPrefixWeight
                coefficient hcoefficient0 hcoefficient1 phase
              have hterm := hmono
                (Nat.le_add_right (turns * K) offset)
              rw [quittingCyclicPrefixWeight_mul_card] at hterm
              simpa only [ρ] using hterm
            _ = (K : ℝ) * ρ ^ turns := by
              simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        rw [Nat.succ_mul, Finset.sum_range_add,
          Finset.sum_range_succ]
        calc
          (∑ x ∈ Finset.range (turns * K),
              quittingCyclicPrefixWeight coefficient phase x) +
              ∑ x ∈ Finset.range K,
                quittingCyclicPrefixWeight coefficient phase
                  (turns * K + x) ≤
            (K : ℝ) * ∑ x ∈ Finset.range turns, ρ ^ x +
              (K : ℝ) * ρ ^ turns := add_le_add ih honeBlock
          _ = (K : ℝ) *
              ((∑ x ∈ Finset.range turns, ρ ^ x) + ρ ^ turns) := by
                ring
  let turns := horizon / K + 1
  have hhorizonTurns : horizon ≤ turns * K := by
    dsimp only [turns]
    rw [Nat.add_mul, one_mul]
    exact (Nat.lt_div_mul_add phase.pos).le
  have hprefixMono :
      (∑ time ∈ Finset.range horizon,
          quittingCyclicPrefixWeight coefficient phase time) ≤
        ∑ time ∈ Finset.range (turns * K),
          quittingCyclicPrefixWeight coefficient phase time := by
    calc
      (∑ time ∈ Finset.range horizon,
          quittingCyclicPrefixWeight coefficient phase time) ≤
        (∑ time ∈ Finset.range horizon,
            quittingCyclicPrefixWeight coefficient phase time) +
          ∑ time ∈ Finset.Ico horizon (turns * K),
            quittingCyclicPrefixWeight coefficient phase time := by
          exact le_add_of_nonneg_right (Finset.sum_nonneg fun time _ ↦
            quittingCyclicPrefixWeight_nonneg
              coefficient hcoefficient0 phase time)
      _ = ∑ time ∈ Finset.range (turns * K),
          quittingCyclicPrefixWeight coefficient phase time :=
            Finset.sum_range_add_sum_Ico _ hhorizonTurns
  have hgeometric :
      (∑ turn ∈ Finset.range turns, ρ ^ turn) ≤ (1 - ρ)⁻¹ := by
    have hpartial :=
      (summable_geometric_of_lt_one hρ0 hcycle).sum_le_tsum
        (Finset.range turns) (fun turn _ ↦ pow_nonneg hρ0 turn)
    simpa only [tsum_geometric_of_lt_one hρ0 hcycle] using hpartial
  calc
    (∑ time ∈ Finset.range horizon,
        quittingCyclicPrefixWeight coefficient phase time) ≤
      ∑ time ∈ Finset.range (turns * K),
        quittingCyclicPrefixWeight coefficient phase time := hprefixMono
    _ ≤ (K : ℝ) * ∑ turn ∈ Finset.range turns, ρ ^ turn :=
      hblock turns
    _ ≤ (K : ℝ) * (1 - ρ)⁻¹ :=
      mul_le_mul_of_nonneg_left hgeometric (Nat.cast_nonneg K)
    _ = (K : ℝ) / (1 - ∏ cyclePhase : Fin K,
        coefficient cyclePhase) := by
      simp only [ρ, div_eq_mul_inv]

/-- For a cyclic behavior profile, the opponent-live Cesàro clock is the
Cesàro average of the corresponding cyclic prefix weights. -/
theorem quittingOpponentLiveCesaro_cyclicBehaviorProfile_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K)
    (player : ι) (horizon : ℕ) :
    quittingOpponentLiveCesaro reward
        (quittingCyclicBehaviorProfile reward cycle phase) player horizon =
      (horizon : ℝ)⁻¹ * ∑ time ∈ Finset.range horizon,
        quittingCyclicPrefixWeight
          (fun cyclePhase ↦
            quittingStationaryFixedOpponentsContinueMass
              (cycle cyclePhase) player) phase time := by
  unfold quittingOpponentLiveCesaro
  congr 1
  apply Finset.sum_congr rfl
  intro time _
  have hweight :=
    quittingOpponentSurvivalWeight_profileLiveRoot_eq_liveMass
      reward (quittingCyclicBehaviorProfile reward cycle phase) player time
  rw [quittingProfileLiveRoot_cyclicBehaviorProfile,
    quittingOpponentSurvivalWeight_cyclicRootSequence] at hweight
  simpa using hweight.symm

/-- A contracting cyclic opponent clock has the explicit
`period / (gap * horizon)` Cesàro bound. -/
theorem quittingOpponentLiveCesaro_cyclicBehaviorProfile_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K)
    (player : ι) (horizon : ℕ)
    (hcontracts : (∏ cyclePhase : Fin K,
      quittingStationaryFixedOpponentsContinueMass
        (cycle cyclePhase) player) < 1) :
    quittingOpponentLiveCesaro reward
        (quittingCyclicBehaviorProfile reward cycle phase) player horizon ≤
      ((K : ℝ) / (1 - ∏ cyclePhase : Fin K,
        quittingStationaryFixedOpponentsContinueMass
          (cycle cyclePhase) player)) / (horizon : ℝ) := by
  rw [quittingOpponentLiveCesaro_cyclicBehaviorProfile_eq]
  have hsum :=
    sum_quittingCyclicPrefixWeight_le_card_div_one_sub_prod
      (fun cyclePhase ↦
        quittingStationaryFixedOpponentsContinueMass
          (cycle cyclePhase) player)
      (fun cyclePhase ↦
        quittingStationaryFixedOpponentsContinueMass_nonneg
          (cycle cyclePhase) player)
      (fun cyclePhase ↦
        quittingStationaryContinueMass_le_one
          (Function.update (cycle cyclePhase) player (PMF.pure false)))
      phase hcontracts horizon
  calc
    (horizon : ℝ)⁻¹ *
        ∑ time ∈ Finset.range horizon,
          quittingCyclicPrefixWeight
            (fun cyclePhase ↦
              quittingStationaryFixedOpponentsContinueMass
                (cycle cyclePhase) player) phase time ≤
      (horizon : ℝ)⁻¹ *
        ((K : ℝ) / (1 - ∏ cyclePhase : Fin K,
          quittingStationaryFixedOpponentsContinueMass
            (cycle cyclePhase) player)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = ((K : ℝ) / (1 - ∏ cyclePhase : Fin K,
          quittingStationaryFixedOpponentsContinueMass
            (cycle cyclePhase) player)) / (horizon : ℝ) := by
      ring

/-! ## Approximate periodic compiler -/

/-- A playerwise bound on the cyclic residual charge packages the periodic
root-error closing theorem as a terminal behavioral approximate Nash
equilibrium. -/
theorem isεAsymptoticNash_quittingCyclicBehaviorProfile_of_rootError
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K)
    (rootError : Fin K → ι → ℝ) (ε bound : ℝ)
    (hbound0 : 0 ≤ bound)
    (hreward : ∀ S player, |reward S player| ≤ bound)
    (hrootError0 : ∀ cyclePhase player,
      0 ≤ rootError cyclePhase player)
    (hroot : ∀ cyclePhase player (oneShot : PMF Bool),
      quittingRootExpectedPayoff reward
          (quittingCyclicTerminalValue reward cycle
            (finRotate K cyclePhase))
          (Function.update (cycle cyclePhase) player oneShot) player ≤
        quittingRootExpectedPayoff reward
            (quittingCyclicTerminalValue reward cycle
              (finRotate K cyclePhase))
            (cycle cyclePhase) player + rootError cyclePhase player)
    (hcontracts : ∀ player,
      (∏ cyclePhase : Fin K,
        quittingStationaryFixedOpponentsContinueMass
          (cycle cyclePhase) player) < 1)
    (hcharge : ∀ player,
      quittingCyclicResidualCharge
          (fun cyclePhase ↦
            quittingStationaryFixedOpponentsContinueMass
              (cycle cyclePhase) player)
          (fun cyclePhase ↦ rootError cyclePhase player) phase K /
        (1 - ∏ cyclePhase : Fin K,
          quittingStationaryFixedOpponentsContinueMass
            (cycle cyclePhase) player) ≤ ε) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) ε
      (quittingCyclicBehaviorProfile reward cycle phase) := by
  intro player deviation
  have hhazard := quittingCyclicHazardTerminalGap_le_of_rootError
    reward cycle phase player
      (quittingBehaviorLiveHazard reward deviation)
      (fun cyclePhase ↦ rootError cyclePhase player)
      bound hbound0 hreward
      (fun cyclePhase ↦ hrootError0 cyclePhase player)
      (fun cyclePhase oneShot ↦ hroot cyclePhase player oneShot)
      (hcontracts player)
  have hdeviation :=
    quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue
      reward (quittingCyclicBehaviorProfile reward cycle phase)
        player deviation
  rw [quittingProfileLiveRoot_cyclicBehaviorProfile] at hdeviation
  rw [← quittingTerminalPayoff_cyclicBehaviorProfile
    reward cycle phase] at hhazard
  rw [hdeviation]
  linarith [hcharge player]

/-- Finiteness supplies the reward bound for the approximate periodic
compiler. -/
theorem isεAsymptoticNash_quittingCyclicBehaviorProfile_of_rootError_finite
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K)
    (rootError : Fin K → ι → ℝ) (ε : ℝ)
    (hrootError0 : ∀ cyclePhase player,
      0 ≤ rootError cyclePhase player)
    (hroot : ∀ cyclePhase player (oneShot : PMF Bool),
      quittingRootExpectedPayoff reward
          (quittingCyclicTerminalValue reward cycle
            (finRotate K cyclePhase))
          (Function.update (cycle cyclePhase) player oneShot) player ≤
        quittingRootExpectedPayoff reward
            (quittingCyclicTerminalValue reward cycle
              (finRotate K cyclePhase))
            (cycle cyclePhase) player + rootError cyclePhase player)
    (hcontracts : ∀ player,
      (∏ cyclePhase : Fin K,
        quittingStationaryFixedOpponentsContinueMass
          (cycle cyclePhase) player) < 1)
    (hcharge : ∀ player,
      quittingCyclicResidualCharge
          (fun cyclePhase ↦
            quittingStationaryFixedOpponentsContinueMass
              (cycle cyclePhase) player)
          (fun cyclePhase ↦ rootError cyclePhase player) phase K /
        (1 - ∏ cyclePhase : Fin K,
          quittingStationaryFixedOpponentsContinueMass
            (cycle cyclePhase) player) ≤ ε) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) ε
      (quittingCyclicBehaviorProfile reward cycle phase) := by
  exact
    isεAsymptoticNash_quittingCyclicBehaviorProfile_of_rootError
      reward cycle phase rootError ε (quittingRewardBound reward)
      (quittingRewardBound_nonneg reward)
      (abs_reward_le_quittingRewardBound reward)
      hrootError0 hroot hcontracts hcharge

/-! ## Quantitative finite-horizon transfer -/

/-- At one fixed horizon, terminal Nash error, prescribed delivery error,
and the one-sided deviation boundary error add. -/
theorem StochasticGame.IsεAsymptoticNash.isεHorizonNash_of_explicitBounds
    {G : StochasticGame ι} {initial : G.State}
    {u : G.BehaviorProfile → ι → ℝ}
    {profile : G.BehaviorProfile}
    {horizon : ℕ} {terminalError deliveryError deviationError : ℝ}
    (hnash : G.IsεAsymptoticNash u terminalError profile)
    (hdelivery : ∀ player,
      |G.finiteAveragePayoff initial horizon profile player -
        u profile player| ≤ deliveryError)
    (hdeviation : ∀ player (deviation : G.BehaviorStrategy player),
      G.finiteAveragePayoff initial horizon
          (Function.update profile player deviation) player ≤
        u (Function.update profile player deviation) player +
          deviationError) :
    G.IsεHorizonNash initial horizon
      (terminalError + deliveryError + deviationError) profile := by
  intro player deviation
  have hterminal := hnash player deviation
  have honPath := (abs_le.mp (hdelivery player)).1
  have hfinite := hdeviation player deviation
  linarith

/-! ## Square-root periodic mesh rate -/

/-- Game-facing square-root rate for an accuracy-indexed cyclic quitting
certificate.  The cyclic residual charge supplies the terminal error; the
two explicit finite-horizon estimates supply the boundary error. -/
theorem isSqrtRateHorizonNash_quittingCyclicBehaviorProfile_of_rootError
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K)
    (rootError : Fin K → ι → ℝ)
    {N : ℕ} {A B m deliveryError deviationError : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hN : 1 ≤ (N : ℝ))
    (hm_lower : Real.sqrt (N : ℝ) ≤ m)
    (hm_upper : m ≤ 2 * Real.sqrt (N : ℝ))
    (hrootError0 : ∀ cyclePhase player,
      0 ≤ rootError cyclePhase player)
    (hroot : ∀ cyclePhase player (oneShot : PMF Bool),
      quittingRootExpectedPayoff reward
          (quittingCyclicTerminalValue reward cycle
            (finRotate K cyclePhase))
          (Function.update (cycle cyclePhase) player oneShot) player ≤
        quittingRootExpectedPayoff reward
            (quittingCyclicTerminalValue reward cycle
              (finRotate K cyclePhase))
            (cycle cyclePhase) player + rootError cyclePhase player)
    (hcontracts : ∀ player,
      (∏ cyclePhase : Fin K,
        quittingStationaryFixedOpponentsContinueMass
          (cycle cyclePhase) player) < 1)
    (hterminal : ∀ player,
      quittingCyclicResidualCharge
          (fun cyclePhase ↦
            quittingStationaryFixedOpponentsContinueMass
              (cycle cyclePhase) player)
          (fun cyclePhase ↦ rootError cyclePhase player) phase K /
        (1 - ∏ cyclePhase : Fin K,
          quittingStationaryFixedOpponentsContinueMass
            (cycle cyclePhase) player) ≤ A / m)
    (hdelivery : ∀ player,
      |(quittingGame reward).finiteAveragePayoff none N
          (quittingCyclicBehaviorProfile reward cycle phase) player -
        quittingCyclicTerminalValue reward cycle phase player| ≤
          deliveryError)
    (hdeviation : ∀ player
        (deviation : (quittingGame reward).BehaviorStrategy player),
      (quittingGame reward).finiteAveragePayoff none N
          (Function.update
            (quittingCyclicBehaviorProfile reward cycle phase)
            player deviation) player ≤
        quittingTerminalPayoff reward
            (Function.update
              (quittingCyclicBehaviorProfile reward cycle phase)
              player deviation) player + deviationError)
    (hboundary : deliveryError + deviationError ≤ B * m / (N : ℝ)) :
    (quittingGame reward).IsεHorizonNash none N
      ((A + 2 * B) / Real.sqrt (N : ℝ))
      (quittingCyclicBehaviorProfile reward cycle phase) := by
  let profile := quittingCyclicBehaviorProfile reward cycle phase
  have hterminalNash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) (A / m) profile := by
    exact
      isεAsymptoticNash_quittingCyclicBehaviorProfile_of_rootError_finite
        reward cycle phase rootError (A / m)
        hrootError0 hroot hcontracts hterminal
  have hdelivery' : ∀ player,
      |(quittingGame reward).finiteAveragePayoff none N
          profile player -
        quittingTerminalPayoff reward profile player| ≤ deliveryError := by
    intro player
    simpa only [profile,
      quittingTerminalPayoff_cyclicBehaviorProfile] using hdelivery player
  have hdeviation' : ∀ player
      (deviation : (quittingGame reward).BehaviorStrategy player),
      (quittingGame reward).finiteAveragePayoff none N
          (Function.update profile player deviation) player ≤
        quittingTerminalPayoff reward
            (Function.update profile player deviation) player +
          deviationError := by
    simpa only [profile] using hdeviation
  have hfinite :=
    hterminalNash.isεHorizonNash_of_explicitBounds
      hdelivery' hdeviation'
  apply hfinite.mono
  calc
    A / m + deliveryError + deviationError =
        A / m + (deliveryError + deviationError) := by ring
    _ ≤ A / m + B * m / (N : ℝ) :=
      add_le_add (le_refl _) hboundary
    _ ≤ (A + 2 * B) / Real.sqrt (N : ℝ) :=
      inv_add_linear_le_sqrt_rate hA hB hN hm_lower hm_upper

/-- The square-root rate with the finite-horizon boundary generated directly
from one opponent-survival Cesàro budget.  That single clock controls both
prescribed delivery and every unilateral finite-horizon deviation, so no
separate boundary hypotheses remain. -/
theorem
    isSqrtRateHorizonNash_quittingCyclicBehaviorProfile_of_opponentLiveCesaro
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K)
    (rootError : Fin K → ι → ℝ)
    {N : ℕ} {A C m bound : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hbound : 0 ≤ bound)
    (hN : 1 ≤ (N : ℝ))
    (hm_lower : Real.sqrt (N : ℝ) ≤ m)
    (hm_upper : m ≤ 2 * Real.sqrt (N : ℝ))
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hrootError0 : ∀ cyclePhase player,
      0 ≤ rootError cyclePhase player)
    (hroot : ∀ cyclePhase player (oneShot : PMF Bool),
      quittingRootExpectedPayoff reward
          (quittingCyclicTerminalValue reward cycle
            (finRotate K cyclePhase))
          (Function.update (cycle cyclePhase) player oneShot) player ≤
        quittingRootExpectedPayoff reward
            (quittingCyclicTerminalValue reward cycle
              (finRotate K cyclePhase))
            (cycle cyclePhase) player + rootError cyclePhase player)
    (hcontracts : ∀ player,
      (∏ cyclePhase : Fin K,
        quittingStationaryFixedOpponentsContinueMass
          (cycle cyclePhase) player) < 1)
    (hterminal : ∀ player,
      quittingCyclicResidualCharge
          (fun cyclePhase ↦
            quittingStationaryFixedOpponentsContinueMass
              (cycle cyclePhase) player)
          (fun cyclePhase ↦ rootError cyclePhase player) phase K /
        (1 - ∏ cyclePhase : Fin K,
          quittingStationaryFixedOpponentsContinueMass
            (cycle cyclePhase) player) ≤ A / m)
    (hsurvival : ∀ player,
      quittingOpponentLiveCesaro reward
          (quittingCyclicBehaviorProfile reward cycle phase) player N ≤
        C * m / (N : ℝ)) :
    (quittingGame reward).IsεHorizonNash none N
      ((A + 4 * bound * C) / Real.sqrt (N : ℝ))
      (quittingCyclicBehaviorProfile reward cycle phase) := by
  let profile := quittingCyclicBehaviorProfile reward cycle phase
  let boundaryError := bound * (C * m / (N : ℝ))
  have hNpositive : 0 < N := by
    have hNreal : 0 < (N : ℝ) := lt_of_lt_of_le zero_lt_one hN
    exact_mod_cast hNreal
  have hdelivery : ∀ player,
      |(quittingGame reward).finiteAveragePayoff none N profile player -
        quittingCyclicTerminalValue reward cycle phase player| ≤
          boundaryError := by
    intro player
    have htail :=
      abs_finiteAveragePayoff_sub_terminal_le_opponentLiveCesaro
        reward profile player N hNpositive bound hbound
          (fun terminal ↦ hreward terminal player)
    have hscaled := mul_le_mul_of_nonneg_left
      (hsurvival player) hbound
    simpa only [profile, quittingTerminalPayoff_cyclicBehaviorProfile,
      boundaryError] using htail.trans hscaled
  have hdeviation : ∀ player
      (deviation : (quittingGame reward).BehaviorStrategy player),
      (quittingGame reward).finiteAveragePayoff none N
          (Function.update profile player deviation) player ≤
        quittingTerminalPayoff reward
            (Function.update profile player deviation) player +
          boundaryError := by
    intro player deviation
    have hfinite :=
      finiteAveragePayoff_update_le_terminal_add_opponentLiveCesaro'
        reward profile player deviation N hNpositive bound hbound
          (fun terminal ↦ hreward terminal player)
    have hscaled := mul_le_mul_of_nonneg_left
      (hsurvival player) hbound
    exact hfinite.trans (add_le_add (le_refl _) (by
      simpa only [profile, boundaryError] using hscaled))
  have hboundary :
      boundaryError + boundaryError ≤
        (2 * bound * C) * m / (N : ℝ) := by
    have heq : boundaryError + boundaryError =
        (2 * bound * C) * m / (N : ℝ) := by
      dsimp only [boundaryError]
      ring
    exact heq.le
  have hrate :=
    isSqrtRateHorizonNash_quittingCyclicBehaviorProfile_of_rootError
      reward cycle phase rootError
      (N := N) (A := A) (B := 2 * bound * C) (m := m)
      (deliveryError := boundaryError) (deviationError := boundaryError)
      hA (mul_nonneg (mul_nonneg (by norm_num) hbound) hC)
      hN hm_lower hm_upper hrootError0 hroot hcontracts hterminal
      hdelivery (by simpa only [profile] using hdeviation) hboundary
  have hconstant : A + 2 * (2 * bound * C) = A + 4 * bound * C := by
    ring
  rw [hconstant] at hrate
  simpa only [profile] using hrate

/-- Fully cyclic boundary form of the square-root rate.  A one-cycle
contraction gap bounds the complete opponent-survival prefix by
`period / gap`; if this is at most `C * m`, both finite-horizon boundary
terms follow automatically. -/
theorem isSqrtRateHorizonNash_quittingCyclicBehaviorProfile_of_cycleGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool) (phase : Fin K)
    (rootError : Fin K → ι → ℝ)
    {N : ℕ} {A C m bound : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hbound : 0 ≤ bound)
    (hN : 1 ≤ (N : ℝ))
    (hm_lower : Real.sqrt (N : ℝ) ≤ m)
    (hm_upper : m ≤ 2 * Real.sqrt (N : ℝ))
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hrootError0 : ∀ cyclePhase player,
      0 ≤ rootError cyclePhase player)
    (hroot : ∀ cyclePhase player (oneShot : PMF Bool),
      quittingRootExpectedPayoff reward
          (quittingCyclicTerminalValue reward cycle
            (finRotate K cyclePhase))
          (Function.update (cycle cyclePhase) player oneShot) player ≤
        quittingRootExpectedPayoff reward
            (quittingCyclicTerminalValue reward cycle
              (finRotate K cyclePhase))
            (cycle cyclePhase) player + rootError cyclePhase player)
    (hcontracts : ∀ player,
      (∏ cyclePhase : Fin K,
        quittingStationaryFixedOpponentsContinueMass
          (cycle cyclePhase) player) < 1)
    (hterminal : ∀ player,
      quittingCyclicResidualCharge
          (fun cyclePhase ↦
            quittingStationaryFixedOpponentsContinueMass
              (cycle cyclePhase) player)
          (fun cyclePhase ↦ rootError cyclePhase player) phase K /
        (1 - ∏ cyclePhase : Fin K,
          quittingStationaryFixedOpponentsContinueMass
            (cycle cyclePhase) player) ≤ A / m)
    (hcycleBudget : ∀ player,
      (K : ℝ) / (1 - ∏ cyclePhase : Fin K,
          quittingStationaryFixedOpponentsContinueMass
            (cycle cyclePhase) player) ≤ C * m) :
    (quittingGame reward).IsεHorizonNash none N
      ((A + 4 * bound * C) / Real.sqrt (N : ℝ))
      (quittingCyclicBehaviorProfile reward cycle phase) := by
  have hNpositive : 0 < (N : ℝ) :=
    lt_of_lt_of_le zero_lt_one hN
  have hsurvival : ∀ player,
      quittingOpponentLiveCesaro reward
          (quittingCyclicBehaviorProfile reward cycle phase) player N ≤
        C * m / (N : ℝ) := by
    intro player
    have hclock :=
      quittingOpponentLiveCesaro_cyclicBehaviorProfile_le
        reward cycle phase player N (hcontracts player)
    have hscaled :
        ((K : ℝ) / (1 - ∏ cyclePhase : Fin K,
            quittingStationaryFixedOpponentsContinueMass
              (cycle cyclePhase) player)) / (N : ℝ) ≤
          C * m / (N : ℝ) :=
      div_le_div_of_nonneg_right (hcycleBudget player) hNpositive.le
    exact hclock.trans hscaled
  exact
    isSqrtRateHorizonNash_quittingCyclicBehaviorProfile_of_opponentLiveCesaro
      reward cycle phase rootError hA hC hbound hN hm_lower hm_upper
      hreward hrootError0 hroot hcontracts hterminal hsurvival

end GameTheory
