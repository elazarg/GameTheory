/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Topology.Order.IntermediateValue
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticEqualityStratum
import UniformEquilibrium.Quitting.Stationary.EndpointCompiler

/-!
# A scalar sign fence for symmetric stationary counterexample searches

This experiment records one rejection test, not a new branch of the quitting
frontier.  Suppose a one-parameter family of absorbing stationary roots has
stationary fixed-point values, and symmetry makes every player's endpoint
gap the same scalar continuous function.  If that scalar changes sign, the
intermediate value theorem produces an exact stationary equilibrium.  The
stationary endpoint compiler then upgrades it to a uniform-equilibrium payoff,
and its literal terminal semantic debt is zero.

For an equal-hazard family in a player-transitive four-player table, the
common scalar is the Quit-minus-Continue endpoint gap.  This theorem is the
precise invariant a concrete cyclic search has to evade: merely arranging a
debt-preserving unilateral hot-potato cycle is irrelevant if the equal-hazard
gap has opposite endpoint signs.

The theorem deliberately assumes the common-gap and fixed-point identities.
It makes no assertion that arbitrary cyclic tables have them, nor that
nonpositive punishment value supplies a sign.  In particular,
`quittingPunishmentValue reward who ≤ 0` is weaker than nonpositivity of the
player's solo reward and is not enough by itself.
-/

noncomputable section

namespace GameTheory
namespace CyclicSymmetricStationaryGapIVT

open Math.Probability Math.PMFProduct Set StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A common continuous endpoint gap with opposite signs somewhere along an
absorbing stationary fixed-point family forces a literal exact stationary
equilibrium.  The conclusion includes the named uniform payoff and zero total
semantic debt of the executable stationary profile.

The two disjuncts in `hbracket` allow either orientation of the sign change.
No monotonicity or uniqueness is required. -/
theorem exists_zeroDebt_uniformPayoff_of_commonStationaryGap_signChange
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ℝ → ι → PMF Bool) (value : ℝ → Payoff ι)
    (gap : ℝ → ℝ) (lower upper : ℝ)
    (hlowerUpper : lower ≤ upper)
    (hgapContinuous : ContinuousOn gap (Icc lower upper))
    (hbracket :
      (gap lower ≤ 0 ∧ 0 ≤ gap upper) ∨
        (gap upper ≤ 0 ∧ 0 ≤ gap lower))
    (hfixed : ∀ q ∈ Icc lower upper,
      value q = quittingRootSuccessorPayoff reward (value q) (root q))
    (hcommonGap : ∀ q ∈ Icc lower upper, ∀ who,
      quittingRootEndpointDifference reward (value q) (root q) who = gap q)
    (habsorbs : ∀ q ∈ Icc lower upper,
      quittingStationaryContinueMass (root q) < 1)
    (hcontracts : ∀ q ∈ Icc lower upper, ∀ who,
      quittingStationaryFixedOpponentsContinueMass (root q) who < 1) :
    ∃ q ∈ Icc lower upper,
      gap q = 0 ∧
        (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) 0
          (quittingStationaryProfile reward (root q)) ∧
        (quittingGame reward).IsUniformEquilibriumPayoff none (value q) ∧
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingStationaryProfile reward (root q))) = 0 := by
  have hzero : ∃ q ∈ Icc lower upper, gap q = 0 := by
    rcases hbracket with hforward | hreverse
    · have htarget : (0 : ℝ) ∈ Icc (gap lower) (gap upper) := hforward
      exact intermediate_value_Icc hlowerUpper hgapContinuous htarget
    · have hnegativeContinuous : ContinuousOn (fun q ↦ -gap q)
          (Icc lower upper) := hgapContinuous.neg
      have htarget : (0 : ℝ) ∈
          Icc (-gap lower) (-gap upper) := by
        constructor <;> linarith
      obtain ⟨q, hq, hqzero⟩ :=
        intermediate_value_Icc hlowerUpper hnegativeContinuous htarget
      exact ⟨q, hq, by linarith⟩
  obtain ⟨q, hq, hqzero⟩ := hzero
  have hendpoint :
      IsεQuittingRootEndpointNash reward (value q) 0 (root q) := by
    intro who
    rw [hcommonGap q hq who, hqzero]
    constructor <;> norm_num
  have hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0
      (quittingStationaryProfile reward (root q)) :=
    isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts
      reward (root q) (value q) (habsorbs q hq) (hfixed q hq)
        hendpoint (hcontracts q hq)
  have huniform :
      (quittingGame reward).IsUniformEquilibriumPayoff none (value q) :=
    isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts
      reward (root q) (value q) (habsorbs q hq) (hfixed q hq)
        hendpoint (hcontracts q hq)
  let profile := quittingStationaryProfile reward (root q)
  have hdebtZero : ∀ who,
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) who = 0 := by
    intro who
    have hnonneg : 0 ≤ quittingTerminalDeviationDebt reward profile who :=
      quittingTerminalDeviationDebt_nonneg reward profile who
        (quittingRewardBound_nonneg reward)
        (abs_reward_le_quittingRewardBound reward)
    have hnonpos : quittingTerminalDeviationDebt reward profile who ≤ 0 := by
      let values : Set ℝ := Set.range fun deviation :
          (quittingGame reward).BehaviorStrategy who ↦
        quittingTerminalPayoff reward
          (Function.update profile who deviation) who
      have hvalues : values.Nonempty := by
        exact ⟨quittingTerminalPayoff reward
          (Function.update profile who (profile who)) who, profile who, rfl⟩
      have hcap : quittingContinuationBestResponseValue reward profile who ≤
          quittingTerminalPayoff reward profile who := by
        unfold quittingContinuationBestResponseValue
        apply csSup_le hvalues
        rintro _ ⟨deviation, rfl⟩
        simpa [profile] using hnash who deviation
      unfold quittingTerminalDeviationDebt
      linarith
    have hliteral : quittingTerminalDeviationDebt reward profile who = 0 :=
      le_antisymm hnonpos hnonneg
    simpa [quittingTerminalSemanticDebt, quittingTerminalSemanticPair,
      quittingTerminalDeviationDebt] using hliteral
  refine ⟨q, hq, hqzero, hnash, huniform, ?_⟩
  unfold quittingTerminalSemanticDebtSum
  exact Finset.sum_eq_zero fun who _ ↦ hdebtZero who

end CyclicSymmetricStationaryGapIVT
end GameTheory
