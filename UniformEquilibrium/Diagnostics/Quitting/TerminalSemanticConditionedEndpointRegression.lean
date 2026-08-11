/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalEndpointGapTransport
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticAllContinuePlateau

/-!
# The conditioned-endpoint sign regression on a semantic plateau

The affine endpoint-gap transport requires one actual profile whose
conditioned terminal payoff lies below a positive singleton payoff.  That
configuration cannot be extracted from the profiles which realize an
all-Continue semantic plateau.

Indeed, an actual terminal payoff is `alpha * conditioned`, where
`alpha ∈ [0,1]`.  On every nonnegative coordinate, conditioning can only
increase the payoff.  The prescribed coordinate of an all-Continue semantic
pair dominates the same player's singleton reward.  Consequently, if that
singleton reward is positive, every cluster point of the canonical
conditioned payoffs of any realizing sequence is at least the singleton.

This is a sign obstruction, not a compactness failure.  It also applies to
actual near-best-response profiles whose terminal payoffs converge to the
larger semantic-envelope coordinate.  Thus the finite profitable-atom law
does not provide the *global conditioned endpoint gap* consumed by affine
deconditioning: its payoff direction is the opposite one.

This does not rule out the marked deviation-coupling route.  A pure-time
deviation may still be split into absorption before its selected stop,
absorption at that stop, and the `Never` boundary, and those local channels
may carry opponent-absorption or collision charge even though their global
conditioned average is high.  The results below only fence off an attempted
direct application of endpoint-gap transport to the plateau-realizing or
near-best-response profiles themselves.  Any such application must first
construct a different co-realized actual family whose literal prescribed
payoff is genuinely below the singleton.
-/

noncomputable section

namespace GameTheory

open Filter Set
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- On a nonnegative coordinate, conditioning an actual terminal law on
eventual absorption can only increase its payoff. -/
theorem quittingTerminalPayoff_le_conditionedPayoff_of_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (hpayoff : 0 ≤ quittingTerminalPayoff reward profile who) :
    quittingTerminalPayoff reward profile who ≤
      quittingTerminalConditionedPayoff reward profile who := by
  let alpha := quittingTerminalAbsorptionProbability reward profile
  let conditioned := quittingTerminalConditionedPayoff reward profile who
  have halpha := quittingTerminalAbsorptionProbability_mem_Icc reward profile
  have hfactor :=
    quittingTerminalPayoff_eq_absorptionProbability_mul_conditionedPayoff
      reward profile who
  change alpha ∈ Set.Icc 0 1 at halpha
  change quittingTerminalPayoff reward profile who = alpha * conditioned at hfactor
  by_cases hzero : alpha = 0
  · have hconditioned : conditioned = 0 := by
      dsimp only [conditioned, quittingTerminalConditionedPayoff]
      rw [show quittingTerminalAbsorptionProbability reward profile = 0 by
        simpa only [alpha] using hzero]
      simp
    change quittingTerminalPayoff reward profile who ≤ conditioned
    rw [hfactor, hzero, zero_mul, hconditioned]
  · have halphaPositive : 0 < alpha := lt_of_le_of_ne halpha.1 (Ne.symm hzero)
    have hconditionedNonneg : 0 ≤ conditioned := by
      rw [hfactor] at hpayoff
      exact nonneg_of_mul_nonneg_right hpayoff halphaPositive
    calc
      quittingTerminalPayoff reward profile who = alpha * conditioned := hfactor
      _ ≤ 1 * conditioned :=
        mul_le_mul_of_nonneg_right halpha.2 hconditionedNonneg
      _ = conditioned := one_mul _

omit [DecidableEq ι] in
/-- A conditioned payoff strictly below a positive singleton forces the
literal payoff of that same actual profile below the singleton as well. -/
theorem quittingTerminalPayoff_lt_singleton_of_conditionedPayoff_lt_singleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (hsolo : 0 < reward (quittingSingletonTerminal who) who)
    (hconditioned : quittingTerminalConditionedPayoff reward profile who <
      reward (quittingSingletonTerminal who) who) :
    quittingTerminalPayoff reward profile who <
      reward (quittingSingletonTerminal who) who := by
  by_contra hnot
  have hsingletonLe : reward (quittingSingletonTerminal who) who ≤
      quittingTerminalPayoff reward profile who := le_of_not_gt hnot
  have hpayoffNonneg : 0 ≤ quittingTerminalPayoff reward profile who :=
    hsolo.le.trans hsingletonLe
  have hincrease := quittingTerminalPayoff_le_conditionedPayoff_of_nonneg
    reward profile who hpayoffNonneg
  linarith

omit [DecidableEq ι] in
/-- Sequence form: if literal payoffs converge to a positive limit which
dominates the singleton, then the canonical conditioned payoffs eventually
lie above the singleton up to every positive error. -/
theorem eventually_singleton_sub_lt_conditionedPayoff_of_terminalPayoff_tendsto
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile) (who : ι)
    (limit : ℝ)
    (hpayoff : Tendsto
      (fun n => quittingTerminalPayoff reward (profiles n) who)
      atTop (nhds limit))
    (hsolo : 0 < reward (quittingSingletonTerminal who) who)
    (hsingleton : reward (quittingSingletonTerminal who) who ≤ limit)
    {error : ℝ} (herror : 0 < error) :
    ∀ᶠ n in atTop,
      reward (quittingSingletonTerminal who) who - error <
        quittingTerminalConditionedPayoff reward (profiles n) who := by
  have hlimitPositive : 0 < limit := hsolo.trans_le hsingleton
  have htarget : reward (quittingSingletonTerminal who) who - error < limit :=
    (sub_lt_self _ herror).trans_le hsingleton
  have hpositive : ∀ᶠ n in atTop,
      0 < quittingTerminalPayoff reward (profiles n) who :=
    hpayoff.eventually_const_lt hlimitPositive
  have habove : ∀ᶠ n in atTop,
      reward (quittingSingletonTerminal who) who - error <
        quittingTerminalPayoff reward (profiles n) who :=
    hpayoff.eventually_const_lt htarget
  filter_upwards [hpositive, habove] with n hpositiveN haboveN
  exact haboveN.trans_le
    (quittingTerminalPayoff_le_conditionedPayoff_of_nonneg
      reward (profiles n) who hpositiveN.le)

omit [DecidableEq ι] in
/-- Every convergent canonical conditioned endpoint of such an actual
sequence dominates the positive singleton. -/
theorem singleton_le_conditionedEndpoint_of_terminalPayoff_tendsto
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile) (who : ι)
    (limit endpoint : ℝ)
    (hpayoff : Tendsto
      (fun n => quittingTerminalPayoff reward (profiles n) who)
      atTop (nhds limit))
    (hsolo : 0 < reward (quittingSingletonTerminal who) who)
    (hsingleton : reward (quittingSingletonTerminal who) who ≤ limit)
    (hconditioned : Tendsto (fun n =>
      quittingTerminalConditionedPayoff reward (profiles n) who)
      atTop (nhds endpoint)) :
    reward (quittingSingletonTerminal who) who ≤ endpoint := by
  by_contra hnot
  have hendpoint : endpoint < reward (quittingSingletonTerminal who) who :=
    lt_of_not_ge hnot
  let error :=
    (reward (quittingSingletonTerminal who) who - endpoint) / 2
  have herror : 0 < error := by
    dsimp only [error]
    linarith
  have hthreshold : endpoint <
      reward (quittingSingletonTerminal who) who - error := by
    dsimp only [error]
    linarith
  have hlower :=
    eventually_singleton_sub_lt_conditionedPayoff_of_terminalPayoff_tendsto
      reward profiles who limit hpayoff hsolo hsingleton herror
  have hupper : ∀ᶠ n in atTop,
      quittingTerminalConditionedPayoff reward (profiles n) who <
        reward (quittingSingletonTerminal who) who - error :=
    hconditioned.eventually_lt_const hthreshold
  obtain ⟨n, hlowerN, hupperN⟩ := (hlower.and hupper).exists
  linarith

omit [DecidableEq ι] in
/-- The same obstruction can be read directly from a convergent finite
terminal-outcome law.  In particular it applies to the pure-time deviation
laws used to realize one semantic-envelope coordinate. -/
theorem singleton_le_conditionedEndpoint_of_terminalOutcomeMass_tendsto
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (mass : QuittingTerminalOutcome ι → ℝ) (who : ι) (endpoint : ℝ)
    (hmass : Tendsto (fun n =>
      quittingTerminalOutcomeMass reward (profiles n)) atTop (nhds mass))
    (hsolo : 0 < reward (quittingSingletonTerminal who) who)
    (hmoment : reward (quittingSingletonTerminal who) who ≤
      quittingTerminalRewardMoment reward mass who)
    (hconditioned : Tendsto (fun n =>
      quittingTerminalConditionedPayoff reward (profiles n) who)
      atTop (nhds endpoint)) :
    reward (quittingSingletonTerminal who) who ≤ endpoint := by
  have hpayoff : Tendsto
      (fun n => quittingTerminalPayoff reward (profiles n) who)
      atTop (nhds (quittingTerminalRewardMoment reward mass who)) := by
    have hmomentLimit :=
      ((continuous_apply who).comp
        (continuous_quittingTerminalRewardMoment reward)).tendsto mass |>.comp
          hmass
    change Tendsto (fun n =>
      quittingTerminalRewardMoment reward
        (quittingTerminalOutcomeMass reward (profiles n)) who)
      atTop (nhds (quittingTerminalRewardMoment reward mass who)) at hmomentLimit
    simpa only [quittingTerminalRewardMoment_outcomeMass] using hmomentLimit
  exact singleton_le_conditionedEndpoint_of_terminalPayoff_tendsto
    reward profiles who (quittingTerminalRewardMoment reward mass who)
      endpoint hpayoff hsolo hmoment hconditioned

/-- The obstruction does not require the conditioned payoffs to converge.
No fixed positive gap below the singleton can persist along a sequence whose
literal payoffs converge to an all-Continue prescribed coordinate. -/
theorem not_eventually_conditionedPayoff_le_singleton_sub_of_allContinueSemanticPair
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (hprofiles : Tendsto (fun n =>
      quittingTerminalSemanticPair reward (profiles n)) atTop (nhds pair))
    (hnash : IsεQuittingRootNash reward pair.1 0
      (quittingAllContinueRoot : ι → PMF Bool))
    (who : ι)
    (hsolo : 0 < reward (quittingSingletonTerminal who) who)
    {gap : ℝ} (hgap : 0 < gap) :
    ¬ ∀ᶠ n in atTop,
      quittingTerminalConditionedPayoff reward (profiles n) who ≤
        reward (quittingSingletonTerminal who) who - gap := by
  have hpayoff : Tendsto
      (fun n => quittingTerminalPayoff reward (profiles n) who)
      atTop (nhds (pair.1 who)) := by
    exact ((continuous_apply who).comp (continuous_fst)).tendsto pair |>.comp
      hprofiles
  have hsingleton : reward (quittingSingletonTerminal who) who ≤ pair.1 who :=
    (isZeroQuittingRootNash_allContinue_iff_singleton_le
      reward pair.1).mp hnash who
  have hlower :=
    eventually_singleton_sub_lt_conditionedPayoff_of_terminalPayoff_tendsto
      reward profiles who (pair.1 who) hpayoff hsolo hsingleton hgap
  intro hupper
  obtain ⟨n, hlowerN, hupperN⟩ := (hlower.and hupper).exists
  linarith

/-- **No same-profile endpoint gap on an all-Continue semantic plateau.**
For any executable sequence converging jointly to the semantic pair, the
premises of affine endpoint-gap transport are inconsistent at every fixed
player: positive singleton floor plus a positive gap below that singleton
cannot hold at a convergent canonical conditioned endpoint. -/
theorem not_exists_sameProfile_conditionedEndpointGap_of_allContinueSemanticPair
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (hprofiles : Tendsto (fun n =>
      quittingTerminalSemanticPair reward (profiles n)) atTop (nhds pair))
    (hnash : IsεQuittingRootNash reward pair.1 0
      (quittingAllContinueRoot : ι → PMF Bool))
    (who : ι) :
    ¬ ∃ endpoint delta eta : ℝ,
      0 < delta ∧ 0 < eta ∧
      delta ≤ reward (quittingSingletonTerminal who) who ∧
      eta ≤ reward (quittingSingletonTerminal who) who - endpoint ∧
      Tendsto (fun n =>
        quittingTerminalConditionedPayoff reward (profiles n) who)
        atTop (nhds endpoint) := by
  rintro ⟨endpoint, delta, eta, hdelta, heta, hdeltaFloor,
    hetaGap, hconditioned⟩
  have hsolo : 0 < reward (quittingSingletonTerminal who) who :=
    hdelta.trans_le hdeltaFloor
  have hpayoff : Tendsto
      (fun n => quittingTerminalPayoff reward (profiles n) who)
      atTop (nhds (pair.1 who)) := by
    exact ((continuous_apply who).comp (continuous_fst)).tendsto pair |>.comp
      hprofiles
  have hsingleton : reward (quittingSingletonTerminal who) who ≤ pair.1 who :=
    (isZeroQuittingRootNash_allContinue_iff_singleton_le
      reward pair.1).mp hnash who
  have hendpointFloor := singleton_le_conditionedEndpoint_of_terminalPayoff_tendsto
    reward profiles who (pair.1 who) endpoint hpayoff hsolo hsingleton
      hconditioned
  linarith

end GameTheory
