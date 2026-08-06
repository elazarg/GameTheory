/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingFullRateStationaryVerifier
import GameTheory.Concepts.Stochastic.QuittingStationaryPayoff
import GameTheory.Concepts.Stochastic.QuittingBellmanTelescope
import GameTheory.Concepts.Stochastic.QuittingOwnerSoloCertification

/-!
# Exact compilation of stationary endpoint certificates

A stationary quitting row has two logically distinct kinds of unilateral
best-response coordinates.

* If the opponents' all-Continue mass is strictly below one, the selected
  stationary Snell cap is determined by the two one-stage endpoint values.
  Exact root Nash at a stationary fixed point bounds both endpoints by the
  displayed value, hence bounds every history-dependent behavioral deviation.
* If the opponents' all-Continue mass is one, the player can postpone forever.
  The exact cap is therefore `max 0 r_i({i})`; this is the only additional
  boundary inequality not visible in the finite continuation game.

The main theorem below is an exact characterization, not merely a sufficient
condition: for every stationary product root, exact behavioral terminal Nash
is equivalent to exact endpoint Nash at the *actual* terminal payoff together
with precisely those saturated-coordinate boundary inequalities.

For an externally supplied fixed point `value`, one joint absorbing inequality
identifies `value` with the actual terminal payoff.  The characterization then
compiles the finite stationary certificate into an exact terminal Nash profile
and, through terminal-to-uniform selection, into the named uniform-equilibrium
payoff `value`.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The only boundary condition not priced by an exact finite root game.
When every opponent of `who` continues surely, the infinite-horizon cap is
`max 0 r_who({who})`; it must lie below the displayed value. -/
def IsQuittingStationaryBoundaryAdmissible
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (value : Payoff ι) : Prop :=
  ∀ who,
    quittingStationaryFixedOpponentsContinueMass root who = 1 →
      max 0 (reward (quittingSingletonTerminal who) who) ≤ value who

/-- A scalar endpoint supersolution bounds the selected stationary Snell cap.
The second endpoint inequality is rearranged through the positive denominator
`1 - continueMass`. -/
theorem quittingStationarySelectedCap_le_of_endpointBounds
    {quitValue continueReward continueMass value : ℝ}
    (hmass1 : continueMass < 1)
    (hquit : quitValue ≤ value)
    (hcontinue : continueReward + continueMass * value ≤ value) :
    quittingStationarySelectedCap
        quitValue continueReward continueMass ≤ value := by
  unfold quittingStationarySelectedCap
  apply max_le hquit
  unfold quittingStationaryNeverValue
  have hdenominator : 0 < 1 - continueMass := sub_pos.mpr hmass1
  rw [div_le_iff₀ hdenominator]
  nlinarith

/-- Exact finite root Nash at a displayed fixed point bounds both pure
endpoints by the displayed value. -/
theorem quittingStationaryEndpointBounds_of_fixedPoint_rootNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (value : Payoff ι)
    (hfixed : value = quittingRootSuccessorPayoff reward value root)
    (hroot : IsεQuittingRootNash reward value 0 root)
    (who : ι) :
    quittingStationaryFixedOpponentsQuitValue reward root who ≤ value who ∧
      quittingStationaryFixedOpponentsContinueReward reward root who +
          quittingStationaryFixedOpponentsContinueMass root who * value who ≤
        value who := by
  have hquit := hroot who (PMF.pure true)
  have hcontinue := hroot who (PMF.pure false)
  change quittingRootQuitPayoff reward value root who ≤
      quittingRootSuccessorPayoff reward value root who + 0 at hquit
  change quittingRootContinuePayoff reward value root who ≤
      quittingRootSuccessorPayoff reward value root who + 0 at hcontinue
  have hvalue := congrFun hfixed who
  rw [← hvalue] at hquit hcontinue
  have hquitEq :
      quittingRootQuitPayoff reward value root who =
        quittingStationaryFixedOpponentsQuitValue reward root who := by
    simpa [quittingStationaryFixedOpponentsQuitValue] using
      (quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
        reward (fun _ => root) who value 0)
  have hcontinueEq :
      quittingRootContinuePayoff reward value root who =
        quittingStationaryFixedOpponentsContinueReward reward root who +
          quittingStationaryFixedOpponentsContinueMass root who * value who := by
    simpa [quittingStationaryFixedOpponentsContinueReward,
      quittingStationaryFixedOpponentsContinueMass] using
      (quittingRootContinuePayoff_eq_fixedOpponents
        reward (fun _ => root) who value 0)
  rw [hquitEq] at hquit
  rw [hcontinueEq] at hcontinue
  exact ⟨by simpa using hquit, by simpa using hcontinue⟩

/-- A stationary fixed point plus exact root Nash and the saturated-coordinate
boundary inequalities bounds the complete behavioral unilateral cap.  No
joint absorption hypothesis is needed for this cap statement. -/
theorem quittingStationaryFullRateUnilateralCap_le_of_fixedPoint_rootNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (value : Payoff ι)
    (hfixed : value = quittingRootSuccessorPayoff reward value root)
    (hroot : IsεQuittingRootNash reward value 0 root)
    (hboundary : IsQuittingStationaryBoundaryAdmissible reward root value) :
    ∀ who,
      quittingStationaryFullRateUnilateralCap reward root who ≤ value who := by
  intro who
  by_cases hcontracts :
      quittingStationaryFixedOpponentsContinueMass root who < 1
  · rw [quittingStationaryFullRateUnilateralCap_of_lt
      reward root who hcontracts]
    obtain ⟨hquit, hcontinue⟩ :=
      quittingStationaryEndpointBounds_of_fixedPoint_rootNash
        reward root value hfixed hroot who
    simpa [quittingStationaryUnilateralCap] using
      (quittingStationarySelectedCap_le_of_endpointBounds
        hcontracts hquit hcontinue)
  · have hmassLe :
        quittingStationaryFixedOpponentsContinueMass root who ≤ 1 :=
      quittingStationaryContinueMass_le_one
        (Function.update root who (PMF.pure false))
    have hmass :
        quittingStationaryFixedOpponentsContinueMass root who = 1 :=
      le_antisymm hmassLe (not_lt.mp hcontracts)
    rw [quittingStationaryFullRateUnilateralCap_of_not_lt
      reward root who hcontracts]
    exact hboundary who hmass

/-- Endpoint form of the preceding cap theorem. -/
theorem quittingStationaryFullRateUnilateralCap_le_of_fixedPoint_endpointNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (value : Payoff ι)
    (hfixed : value = quittingRootSuccessorPayoff reward value root)
    (hroot : IsεQuittingRootEndpointNash reward value 0 root)
    (hboundary : IsQuittingStationaryBoundaryAdmissible reward root value) :
    ∀ who,
      quittingStationaryFullRateUnilateralCap reward root who ≤ value who :=
  quittingStationaryFullRateUnilateralCap_le_of_fixedPoint_rootNash
    reward root value hfixed
      ((isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
        reward value root).mp hroot)
    hboundary

/-- **Exact stationary local-to-global characterization.**  For an arbitrary
stationary product root, exact behavioral terminal Nash is equivalent to:

1. exact one-stage endpoint Nash at the root's actual terminal payoff; and
2. the finite boundary inequality at every coordinate whose opponents all
   continue surely.

The result is unconditional: the root may absorb, fail to absorb, contain
sure quitters, or lie on a saturated face. -/
theorem isZeroAsymptoticNash_stationary_iff_endpointNash_and_boundary
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) :
    (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) 0
        (quittingStationaryProfile reward root) ↔
      IsεQuittingRootEndpointNash reward
          (fun player => quittingTerminalPayoff reward
            (quittingStationaryProfile reward root) player)
          0 root ∧
        IsQuittingStationaryBoundaryAdmissible reward root
          (fun player => quittingTerminalPayoff reward
            (quittingStationaryProfile reward root) player) := by
  let value : Payoff ι := fun player =>
    quittingTerminalPayoff reward (quittingStationaryProfile reward root) player
  have hfixed : value = quittingRootSuccessorPayoff reward value root := by
    funext who
    exact quittingTerminalPayoff_stationary_eq_rootExpectedPayoff
      reward root who
  change (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0
      (quittingStationaryProfile reward root) ↔
    IsεQuittingRootEndpointNash reward value 0 root ∧
      IsQuittingStationaryBoundaryAdmissible reward root value
  constructor
  · intro hnash
    have hrootNash : IsεQuittingRootNash reward value 0 root := by
      simpa [value] using
        (isεQuittingRootNash_of_isεAsymptoticNash_stationary
          reward root 0 hnash)
    refine ⟨(isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward value root).mpr hrootNash, ?_⟩
    intro who hmass
    have hcap :=
      (isεAsymptoticNash_stationary_iff_fullRateUnilateralCap_le
        reward root 0).mp hnash who
    rw [quittingStationaryFullRateUnilateralCap_of_eq_one
      reward root who hmass] at hcap
    simpa [value] using hcap
  · rintro ⟨hroot, hboundary⟩
    rw [isεAsymptoticNash_stationary_iff_fullRateUnilateralCap_le]
    intro who
    have hcap :=
      quittingStationaryFullRateUnilateralCap_le_of_fixedPoint_endpointNash
        reward root value hfixed hroot hboundary who
    simpa [value] using hcap

omit [DecidableEq ι] in
/-- In the jointly absorbing regime, an externally supplied stationary fixed
point is the actual terminal payoff of the stationary profile. -/
theorem quittingTerminalPayoff_stationary_eq_of_fixedPoint
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (value : Payoff ι)
    (habsorbs : quittingStationaryContinueMass root < 1)
    (hfixed : value = quittingRootSuccessorPayoff reward value root) :
    quittingTerminalPayoff reward
      (quittingStationaryProfile reward root) = value := by
  funext who
  have hvalue := congrFun hfixed who
  rw [quittingRootSuccessorPayoff,
    quittingRootExpectedPayoff_eq_absorbingContribution_add] at hvalue
  rw [quittingTerminalPayoff_stationary_eq_absorbingContribution_div
    reward root who habsorbs]
  have hdenominator : 1 - quittingStationaryContinueMass root ≠ 0 :=
    ne_of_gt (sub_pos.mpr habsorbs)
  symm
  rw [eq_div_iff hdenominator]
  nlinarith

/-- For a jointly absorbing stationary fixed point which is exact endpoint
Nash, behavioral terminal Nash is equivalent to the finite boundary packet. -/
theorem isZeroAsymptoticNash_stationary_iff_boundary_of_fixedPoint_endpointNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (value : Payoff ι)
    (habsorbs : quittingStationaryContinueMass root < 1)
    (hfixed : value = quittingRootSuccessorPayoff reward value root)
    (hroot : IsεQuittingRootEndpointNash reward value 0 root) :
    (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) 0
        (quittingStationaryProfile reward root) ↔
      IsQuittingStationaryBoundaryAdmissible reward root value := by
  have hactual := quittingTerminalPayoff_stationary_eq_of_fixedPoint
    reward root value habsorbs hfixed
  constructor
  · intro hnash
    have hcharacter :=
      (isZeroAsymptoticNash_stationary_iff_endpointNash_and_boundary
        reward root).mp hnash
    simpa [hactual] using hcharacter.2
  · intro hboundary
    apply (isZeroAsymptoticNash_stationary_iff_endpointNash_and_boundary
      reward root).mpr
    constructor
    · simpa [hactual] using hroot
    · simpa [hactual] using hboundary

/-- Under the exact stationary certificate, every player's full behavioral cap
is not only bounded by but exactly equal to the displayed value. -/
theorem quittingStationaryFullRateUnilateralCap_eq_of_fixedPoint_endpointNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (value : Payoff ι)
    (habsorbs : quittingStationaryContinueMass root < 1)
    (hfixed : value = quittingRootSuccessorPayoff reward value root)
    (hroot : IsεQuittingRootEndpointNash reward value 0 root)
    (hboundary : IsQuittingStationaryBoundaryAdmissible reward root value)
    (who : ι) :
    quittingStationaryFullRateUnilateralCap reward root who = value who := by
  have hle :=
    quittingStationaryFullRateUnilateralCap_le_of_fixedPoint_endpointNash
      reward root value hfixed hroot hboundary who
  have hself := quittingTerminalPayoff_update_stationary_le_fullRateUnilateralCap
    reward root who (quittingStationaryProfile reward root who)
  have hself' :
      quittingTerminalPayoff reward
          (quittingStationaryProfile reward root) who ≤
        quittingStationaryFullRateUnilateralCap reward root who := by
    simpa only [Function.update_eq_self] using hself
  have hactual := quittingTerminalPayoff_stationary_eq_of_fixedPoint
    reward root value habsorbs hfixed
  rw [hactual] at hself'
  exact le_antisymm hle hself'

/-- **Stationary endpoint compiler.**  A jointly absorbing fixed point, exact
one-stage endpoint Nash, and the exact saturated-coordinate boundary packet
produce the named uniform-equilibrium payoff.  The deviation class is all
behavior strategies. -/
theorem isUniformEquilibriumPayoff_of_stationaryEndpointCertificate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (value : Payoff ι)
    (habsorbs : quittingStationaryContinueMass root < 1)
    (hfixed : value = quittingRootSuccessorPayoff reward value root)
    (hroot : IsεQuittingRootEndpointNash reward value 0 root)
    (hboundary : IsQuittingStationaryBoundaryAdmissible reward root value) :
    (quittingGame reward).IsUniformEquilibriumPayoff none value := by
  have hnash :=
    (isZeroAsymptoticNash_stationary_iff_boundary_of_fixedPoint_endpointNash
      reward root value habsorbs hfixed hroot).mpr hboundary
  have huniform := quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact
    reward (quittingStationaryProfile reward root) hnash
  have hactual := quittingTerminalPayoff_stationary_eq_of_fixedPoint
    reward root value habsorbs hfixed
  simpa [hactual] using huniform

/-- Playerwise opponent contraction makes the boundary packet vacuous. -/
theorem isQuittingStationaryBoundaryAdmissible_of_contracts
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (value : Payoff ι)
    (hcontracts : ∀ who,
      quittingStationaryFixedOpponentsContinueMass root who < 1) :
    IsQuittingStationaryBoundaryAdmissible reward root value := by
  intro who hmass
  have hlt := hcontracts who
  rw [hmass] at hlt
  exact (lt_irrefl 1 hlt).elim

/-- Contracting corollary: no separate boundary proof is needed. -/
theorem isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (value : Payoff ι)
    (habsorbs : quittingStationaryContinueMass root < 1)
    (hfixed : value = quittingRootSuccessorPayoff reward value root)
    (hroot : IsεQuittingRootEndpointNash reward value 0 root)
    (hcontracts : ∀ who,
      quittingStationaryFixedOpponentsContinueMass root who < 1) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0
      (quittingStationaryProfile reward root) :=
  (isZeroAsymptoticNash_stationary_iff_boundary_of_fixedPoint_endpointNash
    reward root value habsorbs hfixed hroot).mpr
      (isQuittingStationaryBoundaryAdmissible_of_contracts
        reward root value hcontracts)

/-- Contracting uniform-payoff corollary. -/
theorem isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (value : Payoff ι)
    (habsorbs : quittingStationaryContinueMass root < 1)
    (hfixed : value = quittingRootSuccessorPayoff reward value root)
    (hroot : IsεQuittingRootEndpointNash reward value 0 root)
    (hcontracts : ∀ who,
      quittingStationaryFixedOpponentsContinueMass root who < 1) :
    (quittingGame reward).IsUniformEquilibriumPayoff none value :=
  isUniformEquilibriumPayoff_of_stationaryEndpointCertificate
    reward root value habsorbs hfixed hroot
      (isQuittingStationaryBoundaryAdmissible_of_contracts
        reward root value hcontracts)

end GameTheory
