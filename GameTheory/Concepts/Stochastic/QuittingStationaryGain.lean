/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingStationarySnellCap
import GameTheory.Concepts.Stochastic.QuittingBellmanTelescope

/-!
# Stationary quitting gains and complementarity

This file isolates the scalar algebra behind stationary quitting profiles
before specializing it to the game-facing quantities.  The exceptional
zero- and singleton-support boundaries are kept separate from the later
contracting equivalences.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

/-! ## Scalar balance algebra -/

/-- The two exact stationary gap factorizations.  Here `x` is the player's
quit probability, `c` is the opponents' continue mass, `Q` is the pure-Quit
value, `A` is the unconditional absorbing contribution under pure Continue,
`h` is total absorption mass, `W` is the prescribed stationary payoff, and
`G = (1-c)Q-A` is the stationary gain.

No division, positivity, or contraction hypothesis is needed for these
identities. -/
theorem stationaryQuittingGain_balance_identities
    (c x Q A h W G : ℝ)
    (habsorption : h = 1 - (1 - x) * c)
    (hpayoff : h * W = x * Q + (1 - x) * A)
    (hgain : G = (1 - c) * Q - A) :
    h * (Q - W) = (1 - x) * G ∧
      h * (A - (1 - c) * W) = -x * G := by
  rw [habsorption] at hpayoff ⊢
  constructor
  · rw [hgain]
    linear_combination -hpayoff
  · rw [hgain]
    linear_combination -(1 - c) * hpayoff

/-- With positive total absorption, the factored gain signs are exactly the
two pure endpoint inequalities against the stationary payoff. -/
theorem stationaryQuittingGain_complementarity_iff_endpoints
    (c x Q A h W G : ℝ)
    (habsorption : h = 1 - (1 - x) * c)
    (hpayoff : h * W = x * Q + (1 - x) * A)
    (hgain : G = (1 - c) * Q - A)
    (hpos : 0 < h) :
    ((1 - x) * G ≤ 0 ∧ 0 ≤ x * G) ↔
      (Q ≤ W ∧ A + c * W ≤ W) := by
  obtain ⟨hquit, hcontinue⟩ :=
    stationaryQuittingGain_balance_identities
      c x Q A h W G habsorption hpayoff hgain
  constructor
  · rintro ⟨hquitSign, hcontinueSign⟩
    constructor
    · nlinarith
    · nlinarith
  · rintro ⟨hquitEndpoint, hcontinueEndpoint⟩
    constructor
    · nlinarith
    · nlinarith

/-- Multiplication by a strictly positive absorption mass preserves both
weighted complementarity signs. -/
theorem stationaryQuittingGain_weightedSigns_iff
    (p r h D G : ℝ) (hpos : 0 < h) (hfactor : h * D = G) :
    (r * G ≤ 0 ∧ 0 ≤ p * G) ↔
      (r * D ≤ 0 ∧ 0 ≤ p * D) := by
  have hquit : r * G = (r * D) * h := by rw [← hfactor]; ring
  have hcontinue : p * G = (p * D) * h := by rw [← hfactor]; ring
  rw [hquit, hcontinue]
  constructor
  · rintro ⟨hquitSign, hcontinueSign⟩
    exact ⟨nonpos_of_mul_nonpos_left hquitSign hpos,
      nonneg_of_mul_nonneg_left hcontinueSign hpos⟩
  · rintro ⟨hquitSign, hcontinueSign⟩
    exact ⟨mul_nonpos_of_nonpos_of_nonneg hquitSign hpos.le,
      mul_nonneg hcontinueSign hpos.le⟩

/-! ## Game-facing stationary quantities -/

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The stationary gain of player `who`: opponent absorption probability
times the pure-Quit value, less the pure-Continue absorbing contribution. -/
def quittingStationaryGain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) : ℝ :=
  (1 - quittingStationaryFixedOpponentsContinueMass root who) *
      quittingStationaryFixedOpponentsQuitValue reward root who -
    quittingStationaryFixedOpponentsContinueReward reward root who

/-- Stationary gain complementarity: a player continuing with positive mass
cannot have positive gain, while a player quitting with positive mass cannot
have negative gain. -/
def IsQuittingStationaryGainComplementary
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) : Prop :=
  ∀ who,
    (root who false).toReal * quittingStationaryGain reward root who ≤ 0 ∧
      0 ≤ (root who true).toReal * quittingStationaryGain reward root who

/-- Total stationary absorption is one minus the player's continue
probability times the probability that all opponents continue. -/
theorem quittingRootAbsorptionMass_eq_one_sub_continueProbability_mul
    (root : ι → PMF Bool) (who : ι) :
    quittingRootAbsorptionMass root =
      1 - (root who false).toReal *
        quittingStationaryFixedOpponentsContinueMass root who := by
  classical
  unfold quittingRootAbsorptionMass
    quittingStationaryFixedOpponentsContinueMass
    quittingFixedOpponentsContinueMass
    quittingStationaryContinueMass
  rw [pmfPi_apply, pmfPi_apply_update_family]
  simp only [quittingAllContinueAction, ENNReal.toReal_prod, PMF.pure_apply,
    if_true, one_mul, sub_right_inj]
  exact prod_factor_erase
    (fun player action => ((root player) action).toReal) who
    (quittingAllContinueAction : ι → Bool)

/-- The stationary payoff balance in playerwise endpoint coordinates. -/
theorem quittingRootAbsorptionMass_mul_stationaryTerminalValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) :
    quittingRootAbsorptionMass root *
        quittingTerminalPayoff reward
          (quittingStationaryProfile reward root) who =
      (root who true).toReal *
          quittingStationaryFixedOpponentsQuitValue reward root who +
        (root who false).toReal *
          quittingStationaryFixedOpponentsContinueReward reward root who := by
  let value : Payoff ι := fun player =>
    quittingTerminalPayoff reward
      (quittingStationaryProfile reward root) player
  have hfixed : value who =
      quittingRootSuccessorPayoff reward value root who := by
    simpa [value, quittingRootSuccessorPayoff] using
      quittingTerminalPayoff_stationary_eq_rootExpectedPayoff reward root who
  have hquit : quittingRootQuitPayoff reward value root who =
      quittingStationaryFixedOpponentsQuitValue reward root who := by
    simpa [quittingStationaryFixedOpponentsQuitValue] using
      quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
        reward (fun _ => root) who value 0
  have hcontinue : quittingRootContinuePayoff reward value root who =
      quittingStationaryFixedOpponentsContinueReward reward root who +
        quittingStationaryFixedOpponentsContinueMass root who * value who := by
    simpa [quittingStationaryFixedOpponentsContinueReward,
      quittingStationaryFixedOpponentsContinueMass] using
      quittingRootContinuePayoff_eq_fixedOpponents
        reward (fun _ => root) who value 0
  have hmix := quittingRootSuccessorPayoff_eq_endpointMix
    reward value root who
  rw [hquit, hcontinue] at hmix
  have habsorption :=
    quittingRootAbsorptionMass_eq_one_sub_continueProbability_mul root who
  have hvalueEq := hfixed.trans hmix
  dsimp [value] at hvalueEq ⊢
  rw [habsorption]
  linear_combination hvalueEq

/-- The stationary endpoint difference is pure Quit minus pure Continue,
with the latter split into its absorbing contribution and surviving
stationary continuation. -/
theorem quittingRootEndpointDifference_stationary_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) :
    quittingRootEndpointDifference reward
        (fun player => quittingTerminalPayoff reward
          (quittingStationaryProfile reward root) player)
        root who =
      quittingStationaryFixedOpponentsQuitValue reward root who -
        (quittingStationaryFixedOpponentsContinueReward reward root who +
          quittingStationaryFixedOpponentsContinueMass root who *
            quittingTerminalPayoff reward
              (quittingStationaryProfile reward root) who) := by
  let value : Payoff ι := fun player =>
    quittingTerminalPayoff reward
      (quittingStationaryProfile reward root) player
  have hquit : quittingRootQuitPayoff reward value root who =
      quittingStationaryFixedOpponentsQuitValue reward root who := by
    simpa [quittingStationaryFixedOpponentsQuitValue] using
      quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
        reward (fun _ => root) who value 0
  have hcontinue : quittingRootContinuePayoff reward value root who =
      quittingStationaryFixedOpponentsContinueReward reward root who +
        quittingStationaryFixedOpponentsContinueMass root who * value who := by
    simpa [quittingStationaryFixedOpponentsContinueReward,
      quittingStationaryFixedOpponentsContinueMass] using
      quittingRootContinuePayoff_eq_fixedOpponents
        reward (fun _ => root) who value 0
  unfold quittingRootEndpointDifference
  simpa only [value] using congrArg₂ (· - ·) hquit hcontinue

/-- All three exact stationary gain identities in the quitting-game API. -/
theorem quittingStationaryGain_identities
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) :
    quittingRootAbsorptionMass root *
        quittingRootEndpointDifference reward
          (fun player => quittingTerminalPayoff reward
            (quittingStationaryProfile reward root) player)
          root who =
        quittingStationaryGain reward root who ∧
      quittingRootAbsorptionMass root *
          (quittingStationaryFixedOpponentsQuitValue reward root who -
            quittingTerminalPayoff reward
              (quittingStationaryProfile reward root) who) =
        (root who false).toReal *
          quittingStationaryGain reward root who ∧
      quittingRootAbsorptionMass root *
          (quittingStationaryFixedOpponentsContinueReward reward root who -
            (1 - quittingStationaryFixedOpponentsContinueMass root who) *
              quittingTerminalPayoff reward
                (quittingStationaryProfile reward root) who) =
        -(root who true).toReal *
          quittingStationaryGain reward root who := by
  let c := quittingStationaryFixedOpponentsContinueMass root who
  let x := (root who true).toReal
  let Q := quittingStationaryFixedOpponentsQuitValue reward root who
  let A := quittingStationaryFixedOpponentsContinueReward reward root who
  let h := quittingRootAbsorptionMass root
  let W := quittingTerminalPayoff reward
    (quittingStationaryProfile reward root) who
  let G := quittingStationaryGain reward root who
  have hcontinueProbability :
      (root who false).toReal = 1 - (root who true).toReal := by
    have hprobability :=
      quittingRoot_continueProbability_add_quitProbability root who
    linarith
  have habsorption : h = 1 - (1 - x) * c := by
    dsimp [h, x, c]
    rw [quittingRootAbsorptionMass_eq_one_sub_continueProbability_mul]
    rw [hcontinueProbability]
  have hpayoff : h * W = x * Q + (1 - x) * A := by
    dsimp [h, W, x, Q, A]
    rw [quittingRootAbsorptionMass_mul_stationaryTerminalValue]
    rw [hcontinueProbability]
  have hgain : G = (1 - c) * Q - A := rfl
  obtain ⟨hquitGap, hcontinueGap⟩ :=
    stationaryQuittingGain_balance_identities
      c x Q A h W G habsorption hpayoff hgain
  have hendpoint :
      quittingRootEndpointDifference reward
          (fun player => quittingTerminalPayoff reward
            (quittingStationaryProfile reward root) player)
          root who = Q - (A + c * W) := by
    simpa only [Q, A, c, W] using
      quittingRootEndpointDifference_stationary_eq reward root who
  have hx : x = 1 - (root who false).toReal := by
    dsimp [x]
    linarith [hcontinueProbability]
  refine ⟨?_, ?_, ?_⟩
  · rw [hendpoint]
    calc
      h * (Q - (A + c * W)) =
          h * (Q - W) - h * (A - (1 - c) * W) := by ring
      _ = (1 - x) * G - (-x * G) := by
        rw [hquitGap, hcontinueGap]
      _ = G := by rw [hx]; ring
  · rw [hx] at hquitGap
    simpa only [h, Q, W, G] using (by
      convert hquitGap using 1
      ring)
  · simpa only [h, A, c, W, G, x] using hcontinueGap

/-- With positive total absorption, stationary gain complementarity is
exactly zero-regret endpoint Nash at the actual stationary terminal payoff.
This is a root-game statement; no full behavioral-deviation conclusion is
made here. -/
theorem isQuittingStationaryGainComplementary_iff_endpointNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (habsorption : 0 < quittingRootAbsorptionMass root) :
    IsQuittingStationaryGainComplementary reward root ↔
      IsεQuittingRootEndpointNash reward
        (fun player => quittingTerminalPayoff reward
          (quittingStationaryProfile reward root) player)
        0 root := by
  unfold IsQuittingStationaryGainComplementary
    IsεQuittingRootEndpointNash
  constructor
  · intro hgain who
    have hfactor := (quittingStationaryGain_identities
      reward root who).1
    simpa using (stationaryQuittingGain_weightedSigns_iff
      (root who true).toReal (root who false).toReal
      (quittingRootAbsorptionMass root)
      (quittingRootEndpointDifference reward
        (fun player => quittingTerminalPayoff reward
          (quittingStationaryProfile reward root) player)
        root who)
      (quittingStationaryGain reward root who)
      habsorption hfactor).mp (hgain who)
  · intro hendpoint who
    have hfactor := (quittingStationaryGain_identities
      reward root who).1
    exact (stationaryQuittingGain_weightedSigns_iff
      (root who true).toReal (root who false).toReal
      (quittingRootAbsorptionMass root)
      (quittingRootEndpointDifference reward
        (fun player => quittingTerminalPayoff reward
          (quittingStationaryProfile reward root) player)
        root who)
      (quittingStationaryGain reward root who)
      habsorption hfactor).mpr (by simpa using hendpoint who)

end GameTheory
