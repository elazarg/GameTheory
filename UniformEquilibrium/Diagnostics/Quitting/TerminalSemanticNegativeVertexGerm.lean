/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticMinimumDebtSimplex
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauPositivePartSplit
import UniformEquilibrium.Quitting.Punishment.InstantPunishment

/-!
# Stationary germs at a terminal-semantic debt vertex

A stationary semantic germ whose honest owner payoff approaches the owner's
singleton payoff and whose owner debt vanishes is already a strategic
certificate: its selected stationary caps approach the singleton payoff.  If
outsiders do not gain by joining the owner's singleton exit, the stationary
min-max identity compiles that limiting cap into an instant-punishment uniform
payoff.

Consequently a counterexample has a sharp alternative at every singleton
face, and hence at the negative zero-slack debt vertex: either some outsider
strictly gains by joining the owner, or the owner's singleton payoff lies
strictly below its punishment value.  In the second branch every stationary
owner cap stays above the singleton payoff by the same positive moat, so the
vanishing-cap mechanism exhibited by the finite negative control is
impossible.

This does not manufacture a stationary germ.  It identifies its exact
strategic consumer and the exact obstruction to its existence in a
counterexample.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.PMFProduct
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- The envelope coordinate of a literal stationary semantic pair is exactly
the selected stationary unilateral cap. -/
theorem quittingTerminalSemanticPair_stationary_envelope_eq_cap
    (root : ι → PMF Bool) (who : ι) :
    (quittingTerminalSemanticPair reward
        (quittingStationaryProfile reward root)).2 who =
      quittingStationaryUnilateralCap reward root who := by
  change quittingContinuationBestResponseValue reward
      (quittingStationaryProfile reward root) who = _
  simpa [quittingContinuationBestResponseValue, quittingBestReplyValue, iSup]
    using quittingBestReplyValue_stationary reward root who

/-- A stationary semantic germ at the singleton vector compiles to the
owner's singleton uniform payoff whenever outsiders do not gain by joining.

Only the owner coordinate is needed: honest payoff convergence plus vanishing
owner debt forces the stationary owner caps to converge to the same singleton
payoff.  Stationary min-max weak duality then supplies the instant-punishment
individual-rationality inequality. -/
theorem isUniformEquilibriumPayoff_soloReward_of_stationarySemanticGerm
    (owner : ι)
    (hnoJoin : IsQuittingInstantNoJoin reward owner)
    (roots : ℕ → ι → PMF Bool)
    (hpayoff : Tendsto (fun n =>
        quittingTerminalPayoff reward
          (quittingStationaryProfile reward (roots n)) owner)
        atTop (nhds (quittingSoloReward reward owner owner)))
    (hdebt : Tendsto (fun n =>
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (quittingStationaryProfile reward (roots n))) owner)
        atTop (nhds 0)) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (quittingSoloReward reward owner) := by
  have hcap : Tendsto
      (fun n => quittingStationaryUnilateralCap reward (roots n) owner)
      atTop (nhds (quittingSoloReward reward owner owner)) := by
    have hadd := hdebt.add hpayoff
    convert hadd using 1
    · funext n
      unfold quittingTerminalSemanticDebt
      rw [quittingTerminalSemanticPair_stationary_envelope_eq_cap]
      change quittingStationaryUnilateralCap reward (roots n) owner =
        quittingStationaryUnilateralCap reward (roots n) owner -
          quittingTerminalPayoff reward
            (quittingStationaryProfile reward (roots n)) owner +
          quittingTerminalPayoff reward
            (quittingStationaryProfile reward (roots n)) owner
      ring_nf
    · ring_nf
  have hIR : IsQuittingInstantPunishmentIR reward owner := by
    unfold IsQuittingInstantPunishmentIR
    apply ge_of_tendsto' hcap
    exact fun n =>
      quittingPunishmentValue_le_stationaryUnilateralCap
        reward owner (roots n)
  exact isUniformEquilibriumPayoff_soloReward_of_instantPunishment
    reward owner hIR hnoJoin

/-- A stationary zero-debt singleton germ has only two strategic outcomes:
an outsider strictly gains by joining the owner, or the singleton payoff is a
uniform-equilibrium payoff. -/
theorem strictJoiner_or_uniformPayoff_of_stationarySemanticGerm
    (owner : ι) (roots : ℕ → ι → PMF Bool)
    (hpayoff : Tendsto (fun n =>
        quittingTerminalPayoff reward
          (quittingStationaryProfile reward (roots n)) owner)
        atTop (nhds (quittingSoloReward reward owner owner)))
    (hdebt : Tendsto (fun n =>
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (quittingStationaryProfile reward (roots n))) owner)
        atTop (nhds 0)) :
    (∃ other, other ≠ owner ∧
        quittingSoloReward reward owner other <
          quittingSingletonCollisionReward reward owner other) ∨
      (quittingGame reward).IsUniformEquilibriumPayoff none
        (quittingSoloReward reward owner) := by
  by_cases hnoJoin : IsQuittingInstantNoJoin reward owner
  · exact Or.inr
      (isUniformEquilibriumPayoff_soloReward_of_stationarySemanticGerm
        owner hnoJoin roots hpayoff hdebt)
  · left
    unfold IsQuittingInstantNoJoin at hnoJoin
    push Not at hnoJoin
    exact hnoJoin

/-- Universal singleton-face restriction in a counterexample.  Either a
strict joiner exposes support entry, or the exact punishment value is
strictly above the owner's singleton payoff. -/
theorem QuittingCounterexampleRegime.strictJoiner_or_soloReward_lt_punishmentValue
    (regime : QuittingCounterexampleRegime reward) (owner : ι) :
    (∃ other, other ≠ owner ∧
        quittingSoloReward reward owner other <
          quittingSingletonCollisionReward reward owner other) ∨
      quittingSoloReward reward owner owner <
        quittingPunishmentValue reward owner := by
  by_cases hnoJoin : IsQuittingInstantNoJoin reward owner
  · right
    by_contra hnot
    have hIR : IsQuittingInstantPunishmentIR reward owner := by
      unfold IsQuittingInstantPunishmentIR
      exact le_of_not_gt hnot
    exact regime.not_exists_uniformEquilibriumPayoff
      ⟨quittingSoloReward reward owner,
        isUniformEquilibriumPayoff_soloReward_of_instantPunishment
          reward owner hIR hnoJoin⟩
  · left
    unfold IsQuittingInstantNoJoin at hnoJoin
    push Not at hnoJoin
    exact hnoJoin

/-- In the no-join branch of a counterexample, every stationary owner cap is
separated strictly above the singleton payoff.  The gap is at least the fixed
punishment moat. -/
theorem QuittingCounterexampleRegime.soloReward_lt_stationaryCap_of_noJoin
    (regime : QuittingCounterexampleRegime reward) (owner : ι)
    (hnoJoin : IsQuittingInstantNoJoin reward owner)
    (root : ι → PMF Bool) :
    quittingSoloReward reward owner owner <
      quittingStationaryUnilateralCap reward root owner := by
  have hgap : quittingSoloReward reward owner owner <
      quittingPunishmentValue reward owner := by
    rcases regime.strictJoiner_or_soloReward_lt_punishmentValue owner with
      hjoin | hgap
    · obtain ⟨other, hne, hstrict⟩ := hjoin
      exact False.elim
        (not_lt_of_ge (hnoJoin other hne) hstrict)
    · exact hgap
  exact hgap.trans_le
    (quittingPunishmentValue_le_stationaryUnilateralCap
      reward owner root)

/-- Hence a counterexample with no singleton joiner admits no stationary
semantic germ whose honest owner payoff approaches its singleton payoff while
the owner debt vanishes. -/
theorem QuittingCounterexampleRegime.not_exists_stationarySemanticGerm_of_noJoin
    (regime : QuittingCounterexampleRegime reward) (owner : ι)
    (hnoJoin : IsQuittingInstantNoJoin reward owner) :
    ¬ ∃ roots : ℕ → ι → PMF Bool,
        Tendsto (fun n =>
          quittingTerminalPayoff reward
            (quittingStationaryProfile reward (roots n)) owner)
          atTop (nhds (quittingSoloReward reward owner owner)) ∧
        Tendsto (fun n =>
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (quittingStationaryProfile reward (roots n))) owner)
          atTop (nhds 0) := by
  rintro ⟨roots, hpayoff, hdebt⟩
  have hUE :=
    isUniformEquilibriumPayoff_soloReward_of_stationarySemanticGerm
      owner hnoJoin roots hpayoff hdebt
  exact regime.not_exists_uniformEquilibriumPayoff
    ⟨quittingSoloReward reward owner, hUE⟩

/-! ## The actual negative-vertex alternative -/

/-- At a minimum debt gate, the prescribed owner coordinate is its singleton
payoff and the owner carries positive debt. -/
theorem minimumTerminalSemantic_debtGate_ownerPin_and_debt_pos
    (pair : QuittingTerminalSemanticPair ι) (owner : ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (hgate : IsMinimumTerminalSemanticDebtGate reward pair owner) :
    pair.1 owner = quittingSoloReward reward owner owner ∧
      0 < quittingTerminalSemanticDebt pair owner := by
  constructor
  · simpa [quittingSoloReward, quittingSingletonTerminal] using
      (minimumTerminalSemantic_singletonTight_iff_debtGate
        (reward := reward) pair hM hreward hpair hminimum hpositive owner).2
        hgate
  · rw [hgate.1]
    exact hpositive

/-- **Actual-sequence negative vertex alternative.**  At a positive minimum
debt gate in a counterexample, either a strict singleton joiner is already
present, or the owner has a positive punishment moat and the *actual realizing
sequence* supplies the same-law harmonic-Never/chronological-charge
alternative.

The second branch is deliberately nonstationary.  The preceding germ theorem
shows that it cannot be replaced by a stationary zero-debt singleton germ:
such a replacement would compile to a uniform payoff. -/
theorem QuittingCounterexampleRegime.exists_joiner_or_punishmentMoat_sameLaw
    (regime : QuittingCounterexampleRegime reward)
    (pair : QuittingTerminalSemanticPair ι) (owner : ι) {M theta : ℝ}
    (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (hnash : IsεQuittingRootNash reward pair.1 0
      (quittingAllContinueRoot : ι → PMF Bool))
    (hgate : IsMinimumTerminalSemanticDebtGate reward pair owner)
    (htheta : 0 < theta) (hthetaOne : theta < 1) :
    (∃ other, other ≠ owner ∧
        quittingSoloReward reward owner other <
          quittingSingletonCollisionReward reward owner other) ∨
      quittingSoloReward reward owner owner <
          quittingPunishmentValue reward owner ∧
        ∃ (profiles : ℕ → (quittingGame reward).BehaviorProfile)
            (quitTime : ℕ → Option ℕ)
            (mass : QuittingTerminalOutcome ι → ℝ)
            (subseq : ℕ → ℕ),
          Tendsto (fun n => quittingTerminalSemanticPair reward (profiles n))
              atTop (nhds pair) ∧
          mass ∈ stdSimplex ℝ (QuittingTerminalOutcome ι) ∧
          StrictMono subseq ∧
          Tendsto (fun n => quittingTerminalOutcomeMass reward
              (Function.update (profiles (subseq n)) owner
                (quittingPureTimeBehaviorStrategy reward owner
                  (quitTime (subseq n)))))
            atTop (nhds mass) ∧
          ((pair.1 owner ≤
                -theta * quittingTerminalSemanticDebtSum pair ∧
              theta * quittingTerminalSemanticDebtSum pair / M ≤ mass none ∧
              ∀ᶠ n in atTop, quitTime (subseq n) = none) ∨
            ((1 - theta) * quittingTerminalSemanticDebtSum pair / (2 * M) ≤
                quittingTerminalOpponentContainingMass owner mass ∧
              ∀ᶠ n in atTop,
                ((1 - theta) * quittingTerminalSemanticDebtSum pair /
                    (2 * M)) / 2 <
                  ∑ terminal ∈ Finset.univ.filter
                      (fun terminal => terminal.val ≠ {owner}),
                    ∑' time, quittingStageCoalitionMass reward
                      (Function.update (profiles (subseq n)) owner
                        (quittingPureTimeBehaviorStrategy reward owner
                          (quitTime (subseq n)))) time terminal)) := by
  rcases regime.strictJoiner_or_soloReward_lt_punishmentValue owner with
    hjoin | hpunishment
  · exact Or.inl hjoin
  · right
    refine ⟨hpunishment, ?_⟩
    have howner := minimumTerminalSemantic_debtGate_ownerPin_and_debt_pos
      (reward := reward) pair owner hM.le hreward hpair hminimum hpositive hgate
    obtain ⟨profiles, quitTime, mass, subseq, hprofiles, hmass, hsubseq,
        hmassLimit, hlaw⟩ :=
      exists_samePureTimeLaw_negativeNever_or_chronologicalOpponentCharge
        reward pair hpair hnash owner howner.2 hM hreward htheta hthetaOne
    refine ⟨profiles, quitTime, mass, subseq, hprofiles, hmass, hsubseq,
      hmassLimit, ?_⟩
    rcases hlaw with hnever | hfinite
    · left
      simpa [hgate.1] using hnever
    · right
      simpa [hgate.1] using hfinite

end GameTheory
