/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.BehaviorPureTimeExtremality
import UniformEquilibrium.Quitting.Root.TerminalOpponentAdvantage

/-!
# Gluing a player prescribed to never quit

This file isolates the original-coordinate estimate needed when a profile on
a proper player face is extended by an outsider who is prescribed `Never`.
At one date, the outsider's pure-Quit gain is the survived solo-versus-tail
gap plus the payoff effect of joining the realized nonempty set of insider
quitters.  If rewards are bounded by `M`, the latter term is at most twice
`M` times the insider absorption mass.

The resulting bound is deliberately conditional.  A restricted equilibrium
does not by itself provide either the outsider continuation estimate or the
small insider absorption estimate used below.  No complementarity-residual
classification is assumed.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The local joining term -/

/-- The part of an outsider's pure-Quit gain caused by joining a realized
nonempty set of opponent quitters.  The sampling root forces the outsider to
Continue.  The sign is the negative of the existing terminal-opponent
advantage, because that advantage is oriented Continue-minus-Quit. -/
def quittingOutsiderJoiningContribution
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) : ℝ :=
  -expect (pmfPi (Function.update root who (PMF.pure false)))
    (quittingTerminalOpponentAdvantage reward who)

/-- With uniformly `M`-bounded terminal rewards, the absolute full-action
Continue-versus-join difference is at most `2*M`. -/
theorem abs_quittingTerminalOpponentAdvantage_le_two_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (action : ι → Bool) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M) :
    |quittingTerminalOpponentAdvantage reward owner action| ≤ 2 * M := by
  let singleton := reward (quittingSingletonTerminal owner) owner
  let before :=
    quittingRootPayoff reward (fun _ ↦ singleton) action owner
  let after := quittingRootPayoff reward (0 : Payoff ι)
    (Function.update action owner true) owner
  have hsingleton : |singleton| ≤ M :=
    hreward (quittingSingletonTerminal owner) owner
  have hbefore : |before| ≤ M := by
    exact abs_quittingRootPayoff_le reward (fun _ ↦ singleton)
      hreward (fun _ ↦ hsingleton) action owner
  have hafter : |after| ≤ M := by
    exact abs_quittingRootPayoff_le reward (0 : Payoff ι)
      hreward (fun _ ↦ by simpa using hM)
      (Function.update action owner true) owner
  unfold quittingTerminalOpponentAdvantage
  change |before - after| ≤ 2 * M
  calc
    |before - after| ≤ |before| + |after| := abs_sub _ _
    _ ≤ M + M := add_le_add hbefore hafter
    _ = 2 * M := by ring

/-- The full-action advantage vanishes when every opponent continues. -/
theorem quittingTerminalOpponentAdvantage_eq_zero_of_quitters_not_nonempty
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (action : ι → Bool)
    (hempty : ¬ (quittingQuitters action).Nonempty) :
    quittingTerminalOpponentAdvantage reward owner action = 0 := by
  have howner : action owner = false := by
    by_contra hnot
    have htrue : action owner = true := Bool.eq_true_of_not_eq_false hnot
    exact hempty ((quittingQuitters_nonempty_iff action).2 ⟨owner, htrue⟩)
  have hquitters : quittingQuitters action = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hempty
  have hupdated :
      quittingQuitters (Function.update action owner true) = {owner} := by
    rw [quittingQuitters_update_true_of_apply_false action owner, hquitters]
    simp
  unfold quittingTerminalOpponentAdvantage quittingRootPayoff
  rw [dif_neg hempty]
  have hupdatedNonempty :
      (quittingQuitters (Function.update action owner true)).Nonempty := by
    rw [hupdated]
    simp
  rw [dif_pos hupdatedNonempty]
  change reward (quittingSingletonTerminal owner) owner -
      reward
        ⟨quittingQuitters (Function.update action owner true),
          hupdatedNonempty⟩ owner = 0
  have hterminal :
      (⟨quittingQuitters (Function.update action owner true),
          hupdatedNonempty⟩ : {S : Finset ι // S.Nonempty}) =
        quittingSingletonTerminal owner := by
    apply Subtype.ext
    exact hupdated
  rw [hterminal]
  ring

/-- The expected payoff effect of joining opponent quitters is bounded by
`2*M` times their one-stage absorption probability. -/
theorem quittingOutsiderJoiningContribution_le_two_mul_absorptionMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M) :
    quittingOutsiderJoiningContribution reward root who ≤
      2 * M * quittingRootAbsorptionMass
        (Function.update root who (PMF.pure false)) := by
  let opponentRoot := Function.update root who (PMF.pure false)
  let advantage := quittingTerminalOpponentAdvantage reward who
  have hpoint : ∀ action : ι → Bool,
      -advantage action ≤
        2 * M * (if (quittingQuitters action).Nonempty then 1 else 0) := by
    intro action
    by_cases hquit : (quittingQuitters action).Nonempty
    · simp only [if_pos hquit, mul_one]
      exact (neg_le_abs (advantage action)).trans
        (abs_quittingTerminalOpponentAdvantage_le_two_mul
          reward who action hM hreward)
    · change -quittingTerminalOpponentAdvantage reward who action ≤ _
      rw [quittingTerminalOpponentAdvantage_eq_zero_of_quitters_not_nonempty
          reward who action hquit]
      simp [hquit]
  have hmono := expect_mono (pmfPi opponentRoot)
    (fun action ↦ -advantage action)
    (fun action ↦
      2 * M * (if (quittingQuitters action).Nonempty then 1 else 0)) hpoint
  have hleft :
      expect (pmfPi opponentRoot) (fun action ↦ -advantage action) =
        -expect (pmfPi opponentRoot) advantage := by
    rw [show (fun action ↦ -advantage action) =
        fun action ↦ (-1 : ℝ) * advantage action by
          funext action
          ring,
      expect_const_mul]
    ring
  have hright :
      expect (pmfPi opponentRoot) (fun action ↦
          2 * M *
            (if (quittingQuitters action).Nonempty then 1 else 0)) =
        2 * M * quittingRootAbsorptionMass opponentRoot := by
    rw [expect_const_mul,
      expect_quittingNonemptyIndicator_eq_absorptionMass]
  unfold quittingOutsiderJoiningContribution
  change -expect (pmfPi opponentRoot) advantage ≤ _
  rw [← hleft, ← hright]
  exact hmono

/-! ## Exact local formula and quantitative estimate -/

/-- Exact outsider pure-Quit gain formula.  The endpoint constructors already
overwrite the outsider's root marginal, so no hypothesis on `root who` is
needed.  The continuation `tail who` is paid only if every opponent
continues. -/
theorem quittingRootEndpointDifference_eq_outsiderNever
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootEndpointDifference reward tail root who =
      (1 - quittingRootAbsorptionMass
          (Function.update root who (PMF.pure false))) *
        (reward (quittingSingletonTerminal who) who - tail who) +
      quittingOutsiderJoiningContribution reward root who := by
  unfold quittingRootEndpointDifference quittingOutsiderJoiningContribution
  rw [expect_terminalOpponentAdvantage]
  unfold quittingRootQuitPayoff quittingRootContinuePayoff
  rw [quittingRootExpectedPayoff_eq_absorbingContribution_add,
    quittingRootExpectedPayoff_eq_absorbingContribution_add,
    quittingRootExpectedPayoff_eq_absorbingContribution_add,
    quittingRootExpectedPayoff_eq_absorbingContribution_add,
    quittingStationaryContinueMass_update_pure_true_eq_zero]
  unfold quittingRootAbsorptionMass
  simp only [zero_mul, add_zero, Pi.zero_apply]
  ring

/-- **One-stage outsider-Never gain bound.**  If the outsider continuation is
at most `eta` below its singleton payoff and the opponents absorb with mass at
most `delta`, then switching from Continue to Quit gains at most
`eta + 2*M*delta`. -/
theorem quittingRootEndpointDifference_le_eta_add_two_mul_M_mul_delta
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    {M eta delta : ℝ} (hM : 0 ≤ M) (heta : 0 ≤ eta)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hcontinuation :
      reward (quittingSingletonTerminal who) who - tail who ≤ eta)
    (habsorption :
      quittingRootAbsorptionMass
        (Function.update root who (PMF.pure false)) ≤ delta) :
    quittingRootEndpointDifference reward tail root who ≤
      eta + 2 * M * delta := by
  let mass := quittingRootAbsorptionMass
    (Function.update root who (PMF.pure false))
  have hmass0 : 0 ≤ mass := by
    unfold mass quittingRootAbsorptionMass
    linarith [quittingStationaryContinueMass_le_one
      (Function.update root who (PMF.pure false))]
  have hmass1 : mass ≤ 1 := by
    unfold mass quittingRootAbsorptionMass
    linarith [quittingStationaryContinueMass_nonneg
      (Function.update root who (PMF.pure false))]
  have hsurvival0 : 0 ≤ 1 - mass := by linarith
  have hgap :
      (1 - mass) *
          (reward (quittingSingletonTerminal who) who - tail who) ≤ eta := by
    calc
      (1 - mass) *
          (reward (quittingSingletonTerminal who) who - tail who) ≤
        (1 - mass) * eta :=
          mul_le_mul_of_nonneg_left hcontinuation hsurvival0
      _ ≤ 1 * eta :=
        mul_le_mul_of_nonneg_right (by linarith) heta
      _ = eta := one_mul eta
  have hjoining :=
    quittingOutsiderJoiningContribution_le_two_mul_absorptionMass
      reward root who hM hreward
  have hjoiningDelta :
      quittingOutsiderJoiningContribution reward root who ≤
        2 * M * delta := by
    exact hjoining.trans
      (mul_le_mul_of_nonneg_left habsorption (mul_nonneg (by positivity) hM))
  rw [quittingRootEndpointDifference_eq_outsiderNever]
  change (1 - mass) *
      (reward (quittingSingletonTerminal who) who - tail who) +
        quittingOutsiderJoiningContribution reward root who ≤ _
  exact add_le_add hgap hjoiningDelta

/-! ## Transport from a finite quit time to literal `Never` -/

/-- Exact pure-time gain transport.  The gain from quitting after `fuel`
opponent-survival stages, relative to literal `Never`, is the reach
probability times the local pure-Quit endpoint gain at that date.  The tail in
the endpoint is the actual `Never` terminal payoff from the next date. -/
theorem quittingRootSequencePureTimeTerminalValue_some_sub_none_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) :
    ∀ start fuel,
      quittingRootSequencePureTimeTerminalValue reward roots who
          (some (start + fuel)) start -
        quittingRootSequencePureTimeTerminalValue reward roots who none start =
      quittingOpponentSurvivalWeight roots who start fuel *
        quittingRootEndpointDifference reward
          (fun _ ↦ quittingRootSequencePureTimeTerminalValue
            reward roots who none (start + fuel + 1))
          (roots (start + fuel)) who := by
  intro start fuel
  induction fuel generalizing start with
  | zero =>
      rw [Nat.add_zero,
        quittingRootSequencePureTimeTerminalValue_some_self_eq_fixedOpponents,
        quittingRootSequencePureTimeTerminalValue_none_succ_eq_fixedOpponents]
      simp only [quittingOpponentSurvivalWeight, Finset.range_zero,
        Finset.prod_empty, one_mul]
      unfold quittingRootEndpointDifference
      rw [quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
          reward roots who _ start,
        quittingRootContinuePayoff_eq_fixedOpponents
          reward roots who _ start]
  | succ fuel ih =>
      have hne : start ≠ start + (fuel + 1) := by omega
      have hindex : start + (fuel + 1) = start + 1 + fuel := by omega
      have hsome :
          quittingRootSequencePureTimeTerminalValue reward roots who
              (some (start + (fuel + 1))) start =
            quittingFixedOpponentsContinueReward reward roots who start +
              quittingFixedOpponentsContinueMass roots who start *
                quittingRootSequencePureTimeTerminalValue reward roots who
                  (some (start + (fuel + 1))) (start + 1) := by
        unfold quittingRootSequencePureTimeTerminalValue
        rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman,
          quittingPureTimeHazard_some_of_ne hne]
        simp
      have hnever :=
        quittingRootSequencePureTimeTerminalValue_none_succ_eq_fixedOpponents
          reward roots who start
      calc
        quittingRootSequencePureTimeTerminalValue reward roots who
              (some (start + (fuel + 1))) start -
            quittingRootSequencePureTimeTerminalValue reward roots who none
              start =
          quittingFixedOpponentsContinueMass roots who start *
            (quittingRootSequencePureTimeTerminalValue reward roots who
                (some (start + (fuel + 1))) (start + 1) -
              quittingRootSequencePureTimeTerminalValue reward roots who none
                (start + 1)) := by rw [hsome, hnever]; ring
        _ = quittingFixedOpponentsContinueMass roots who start *
            (quittingOpponentSurvivalWeight roots who (start + 1) fuel *
              quittingRootEndpointDifference reward
                (fun _ ↦ quittingRootSequencePureTimeTerminalValue
                  reward roots who none (start + (fuel + 1) + 1))
                (roots (start + (fuel + 1))) who) := by
          rw [hindex, ih (start + 1)]
        _ = quittingOpponentSurvivalWeight roots who start (fuel + 1) *
            quittingRootEndpointDifference reward
              (fun _ ↦ quittingRootSequencePureTimeTerminalValue
                reward roots who none (start + (fuel + 1) + 1))
              (roots (start + (fuel + 1))) who := by
          rw [quittingOpponentSurvivalWeight_succ_left]
          ring

/-- Every deterministic quit time, including literal `Never`, is within
`eta + 2*M*delta` of literal `Never` when the two local hypotheses hold at
every possible stopping date. -/
theorem quittingRootSequencePureTimeTerminalValue_le_never_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    {M eta delta : ℝ} (hM : 0 ≤ M) (heta : 0 ≤ eta)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hcontinuation : ∀ time,
      reward (quittingSingletonTerminal who) who -
          quittingRootSequencePureTimeTerminalValue reward roots who none
            (time + 1) ≤ eta)
    (habsorption : ∀ time,
      quittingRootAbsorptionMass
          (Function.update (roots time) who (PMF.pure false)) ≤ delta)
    (quitTime : Option ℕ) :
    quittingRootSequencePureTimeTerminalValue reward roots who quitTime 0 ≤
      quittingRootSequencePureTimeTerminalValue reward roots who none 0 +
        (eta + 2 * M * delta) := by
  have hcap0 : 0 ≤ eta + 2 * M * delta := by
    have hdelta0 : 0 ≤ delta :=
      (by
        have hmass : 0 ≤ quittingRootAbsorptionMass
            (Function.update (roots 0) who (PMF.pure false)) := by
          unfold quittingRootAbsorptionMass
          linarith [quittingStationaryContinueMass_le_one
            (Function.update (roots 0) who (PMF.pure false))]
        exact hmass.trans (habsorption 0))
    positivity
  cases quitTime with
  | none => linarith
  | some time =>
      have hlocal :=
        quittingRootEndpointDifference_le_eta_add_two_mul_M_mul_delta
          reward
          (fun _ ↦ quittingRootSequencePureTimeTerminalValue
            reward roots who none (time + 1))
          (roots time) who hM heta hreward (hcontinuation time)
          (habsorption time)
      have hexact :=
        quittingRootSequencePureTimeTerminalValue_some_sub_none_eq
          reward roots who 0 time
      simp only [Nat.zero_add] at hexact
      have hweight0 :=
        quittingOpponentSurvivalWeight_nonneg roots who 0 time
      have hweight1 :=
        quittingOpponentSurvivalWeight_le_one roots who 0 time
      have hscaled := mul_le_mul_of_nonneg_left hlocal hweight0
      have hcapScaled :=
        mul_le_mul_of_nonneg_right hweight1 hcap0
      linarith

/-! ## All-behavior outsider wrapper -/

/-- Against fixed opponent behavior, every behavioral deviation is within
`eta + 2*M*delta` of the explicit behavior strategy `Never`, provided the
corresponding live-root sequence satisfies the two local hypotheses at every
date.  This theorem does not infer those hypotheses from a restricted
equilibrium. -/
theorem quittingTerminalPayoff_update_le_never_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (deviation : (quittingGame reward).BehaviorStrategy who)
    {M eta delta : ℝ} (hM : 0 ≤ M) (heta : 0 ≤ eta)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hcontinuation : ∀ time,
      reward (quittingSingletonTerminal who) who -
          quittingRootSequencePureTimeTerminalValue reward
            (quittingProfileLiveRoot reward profile) who none (time + 1) ≤
        eta)
    (habsorption : ∀ time,
      quittingRootAbsorptionMass
          (Function.update
            (quittingProfileLiveRoot reward profile time) who
            (PMF.pure false)) ≤ delta) :
    quittingTerminalPayoff reward (Function.update profile who deviation) who ≤
      quittingTerminalPayoff reward
          (Function.update profile who
            (quittingPureTimeBehaviorStrategy reward who none)) who +
        (eta + 2 * M * delta) := by
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  obtain ⟨quitTime, hquitTime⟩ :=
    exists_quittingPureTimeBehaviorStrategy_terminalPayoff_ge_sub
      reward profile who deviation hε
  have hpure :=
    quittingRootSequencePureTimeTerminalValue_le_never_add
      reward (quittingProfileLiveRoot reward profile) who hM heta hreward
      hcontinuation habsorption quitTime
  rw [← quittingTerminalPayoff_update_pureTimeBehaviorStrategy
      reward profile who quitTime,
    ← quittingTerminalPayoff_update_pureTimeBehaviorStrategy
      reward profile who none] at hpure
  linarith

end GameTheory
