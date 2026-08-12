/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPureTimeRectangleDisintegration
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauMarkedTailLocalization
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPositiveSlopeTargetEdgeStateMatchRegression
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticAllContinuePlateau

/-!
# Minimum-fiber provenance for a positive pure-time rectangle row

A positive signed chronological rectangle is not, by itself, a local Nash
sign.  There is nevertheless one branch on which the counterexample/minimum
provenance has an immediate consumer.

Suppose the literal rectangle coalition contains the pure-time observer, is
a collision, and pays that observer positively.  A uniform positive lower
bound on the signed stage atom then gives a uniform positive lower bound on
the *target* profile's mass at the same causal row.  If the observer's debt
on those target profiles tends to zero, marked-tail localization applies
without changing the terminal coalition or replacing the actual profile.
At a positive global minimum debt, either the target tails escape strictly
above the minimum fiber or a uniformly positive local Nash defect is carried
by the other players at the same reached rows.

The positivity of the target reward is essential to this orientation.  With
a negative reward, positivity of the signed atom can instead be carried by
mass in the source profile, where the endpoint approximate-best-response
debt gives no control.  Likewise, a singleton or a coalition excluding the
pure-time observer does not meet the marked-collision consumer.  These are
the first hypotheses lost between the global positive-slope decoder and the
local marked-row theorem.
-/

noncomputable section

namespace GameTheory

open Filter StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The literal target endpoint underlying a sequence of pure-time
rectangles, before inserting the observer's deterministic response. -/
def quittingPureTimeRectangleTargetBase
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile) (mover : ι)
    (target : ℕ → (quittingGame reward).BehaviorStrategy mover) (n : ℕ) :
    (quittingGame reward).BehaviorProfile :=
  Function.update (profiles n) mover (target n)

/-- **Positive target-row provenance.**

The conclusion is exactly the marked-tail escape/other-defect alternative,
now produced from a positive signed rectangle stage.  The selected `stop`
is the observer's literal pure stopping date; because the coalition contains
the observer, the supplied causal-stage passport rules out both preemption
and `Never`.

No generic atomization is used: `terminal`, the target endpoint, its
pure-time response, and its actual reached row are retained throughout. -/
theorem exists_markedTailCluster_escape_or_otherNashDefect_of_positiveTargetRectangleStage
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (mover observer : ι) (hmoverObserver : mover ≠ observer)
    (source target : ℕ → (quittingGame reward).BehaviorStrategy mover)
    (quitTime : ℕ → Option ℕ) (time : ℕ → ℕ)
    (terminal : {S : Finset ι // S.Nonempty})
    (hobserver : observer ∈ terminal.val)
    {lower M : ℝ} (hlower : 0 < lower) (hM : 0 ≤ M)
    (hreward : ∀ outcome player, |reward outcome player| ≤ M)
    (hterminalReward : 0 < reward terminal observer)
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPositive : 0 < quittingTerminalSemanticDebtSum minimum)
    (hcollision : 1 < terminal.val.card)
    (hcausal : ∀ n,
      IsQuittingPureTimeRectangleStage observer terminal (quitTime n) (time n))
    (hrectangle : ∀ᶠ n in atTop, lower ≤
      quittingStoppingLawRectangleStageAtom reward
        (Function.update (profiles n) observer
          (quittingPureTimeBehaviorStrategy reward observer (quitTime n)))
        mover (source n) (target n) observer (time n) terminal)
    (hreset : Tendsto (fun n => quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (Function.update
          (quittingPureTimeRectangleTargetBase reward profiles mover target n)
          observer
          (quittingPureTimeBehaviorStrategy reward observer (quitTime n))))
      observer) atTop (nhds 0)) :
    ∃ (stop : ℕ → ℕ) (cluster : QuittingTerminalSemanticPair ι)
        (subseq : ℕ → ℕ),
      cluster ∈ quittingTerminalSemanticCarrier reward ∧
      StrictMono subseq ∧
      (∀ᶠ rank in atTop,
        quitTime (subseq rank) = some (stop (subseq rank))) ∧
      (∀ᶠ rank in atTop,
        stop (subseq rank) = time (subseq rank)) ∧
      (∀ᶠ rank in atTop, lower / M ≤
        quittingStageCoalitionMass reward
          (Function.update
            (quittingPureTimeRectangleTargetBase reward profiles mover target
              (subseq rank))
            observer
            (quittingPureTimeBehaviorStrategy reward observer
              (quitTime (subseq rank))))
          (stop (subseq rank)) terminal) ∧
      Tendsto (fun rank => quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward
            (Function.update
              (quittingPureTimeRectangleTargetBase reward profiles mover target
                (subseq rank))
              observer
              (quittingPureTimeBehaviorStrategy reward observer
                (quitTime (subseq rank))))
            (stop (subseq rank) + 1)))
        atTop (nhds cluster) ∧
      Tendsto (fun rank =>
        let deviated := Function.update
          (quittingPureTimeRectangleTargetBase reward profiles mover target
            (subseq rank)) observer
          (quittingPureTimeBehaviorStrategy reward observer
            (quitTime (subseq rank)))
        quittingRootCoordinateNashDefect reward
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward deviated
              (stop (subseq rank) + 1))).1
          (quittingProfileLiveRoot reward deviated (stop (subseq rank)))
          observer) atTop (nhds 0) ∧
      (quittingTerminalSemanticDebtSum minimum <
          quittingTerminalSemanticDebtSum cluster ∨
        quittingTerminalSemanticDebtSum cluster =
            quittingTerminalSemanticDebtSum minimum ∧
          ∀ᶠ rank in atTop,
            (lower / M) * quittingTerminalSemanticDebtSum minimum / 2 ≤
              ∑ other ∈ Finset.univ.erase observer,
                let deviated := Function.update
                  (quittingPureTimeRectangleTargetBase reward profiles mover
                    target (subseq rank)) observer
                  (quittingPureTimeBehaviorStrategy reward observer
                    (quitTime (subseq rank)))
                quittingRootCoordinateNashDefect reward
                  (quittingTerminalSemanticPair reward
                    (quittingAllContinueProfileSpine reward deviated
                      (stop (subseq rank) + 1))).1
                  (quittingProfileLiveRoot reward deviated
                    (stop (subseq rank))) other) := by
  have hterminalRewardLe : reward terminal observer ≤ M := by
    exact (le_abs_self (reward terminal observer)).trans
      (hreward terminal observer)
  have hMpos : 0 < M := hterminalReward.trans_le hterminalRewardLe
  have hlowerDiv : 0 < lower / M := div_pos hlower hMpos
  have hquitAt : ∀ n, quitTime n = some (time n) := by
    intro n
    have h := hcausal n
    cases hquit : quitTime n with
    | none =>
        rw [hquit] at h
        exact False.elim (h hobserver)
    | some stop =>
        rw [hquit] at h
        rcases h with hbefore | hat
        · exact False.elim (hbefore.2 hobserver)
        · rw [hat.1]
  let targetBase : ℕ → (quittingGame reward).BehaviorProfile := fun n =>
    quittingPureTimeRectangleTargetBase reward profiles mover target n
  let deviated : ℕ → (quittingGame reward).BehaviorProfile := fun n =>
    Function.update (targetBase n) observer
      (quittingPureTimeBehaviorStrategy reward observer (quitTime n))
  have hstage : ∀ᶠ n in atTop, lower / M ≤
      quittingStageCoalitionMass reward (deviated n) (time n) terminal := by
    filter_upwards [hrectangle] with n hrectangleN
    let targetMass := quittingStageCoalitionMass reward (deviated n)
      (time n) terminal
    let sourceMass := quittingStageCoalitionMass reward
      (Function.update
        (Function.update (profiles n) observer
          (quittingPureTimeBehaviorStrategy reward observer (quitTime n)))
        mover (source n)) (time n) terminal
    have htargetMass0 : 0 ≤ targetMass :=
      quittingStageCoalitionMass_nonneg reward (deviated n) (time n) terminal
    have hsourceMass0 : 0 ≤ sourceMass :=
      quittingStageCoalitionMass_nonneg reward _ (time n) terminal
    have htargetOrder :
        Function.update
            (Function.update (profiles n) observer
              (quittingPureTimeBehaviorStrategy reward observer (quitTime n)))
            mover (target n) = deviated n := by
      dsimp only [deviated, targetBase,
        quittingPureTimeRectangleTargetBase]
      exact (Function.update_comm hmoverObserver
        (target n)
        (quittingPureTimeBehaviorStrategy reward observer (quitTime n))
        (profiles n)).symm
    have hproduct : lower ≤
        (targetMass - sourceMass) * reward terminal observer := by
      dsimp only [quittingStoppingLawRectangleStageAtom] at hrectangleN
      rw [htargetOrder] at hrectangleN
      simpa only [targetMass, sourceMass] using hrectangleN
    have htargetProduct : lower ≤
        targetMass * reward terminal observer := by
      nlinarith
    have hboundedProduct : targetMass * reward terminal observer ≤
        targetMass * M :=
      mul_le_mul_of_nonneg_left hterminalRewardLe htargetMass0
    apply (div_le_iff₀ hMpos).2
    nlinarith
  have hpersistent : ∀ᶠ n in atTop, lower / M ≤
      quittingTerminalOutcomeMass reward (deviated n) (some terminal) := by
    filter_upwards [hstage] with n hstageN
    exact hstageN.trans
      (quittingStageCoalitionMass_le_terminalOutcomeMass reward
        (deviated n) (time n) terminal)
  have hlocalized :=
    exists_markedTailCluster_escape_or_otherNashDefect reward minimum
      targetBase observer quitTime terminal hobserver hlowerDiv hM hreward
      hminimumCarrier hminimum hminimumPositive hcollision (by
        simpa only [targetBase, deviated] using hreset) (by
        simpa only [deviated] using hpersistent)
  obtain ⟨stop, cluster, subseq, hcluster, hsubseq, hfinite, hstageSub,
    htail, hmarked, hbranch⟩ := hlocalized
  refine ⟨stop, cluster, subseq, hcluster, hsubseq, hfinite, ?_, ?_, ?_,
    ?_, ?_⟩
  · filter_upwards [hfinite] with rank hfiniteRank
    have hinput := hquitAt (subseq rank)
    rw [hinput] at hfiniteRank
    exact (Option.some.inj hfiniteRank).symm
  · simpa only [targetBase, deviated] using hstageSub
  · simpa only [targetBase, deviated] using htail
  · simpa only [targetBase, deviated] using hmarked
  · simpa only [targetBase, deviated] using hbranch

/-! ## Sharpness: exact minimum provenance is still insufficient at zero floor -/

namespace PositiveSlopeTargetEdgeStateMatchRegression

/-- The regression reward table is uniformly bounded by one. -/
theorem abs_reward_le_one (terminal : {S : Finset Player // S.Nonempty})
    (who : Player) : |reward terminal who| ≤ 1 := by
  unfold reward
  split_ifs <;> norm_num

theorem target_payoff_clock_eq_zero :
    quittingTerminalPayoff reward target clock = 0 := by
  rw [← quittingTerminalRewardMoment_outcomeMass reward target]
  unfold quittingTerminalRewardMoment
  apply Finset.sum_eq_zero
  intro outcome _houtcome
  cases outcome with
  | none => simp [quittingTerminalOutcomeReward]
  | some terminal =>
      simp [quittingTerminalOutcomeReward, reward, clock, observer]

theorem target_debt_observer_eq_zero :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward target) observer = 0 := by
  have hcapUpper :=
    quittingContinuationBestResponseValue_le_of_terminalOutcomeReward_le
      (reward := reward) target observer 1 (by
        intro outcome
        cases outcome with
        | none => simp [quittingTerminalOutcomeReward]
        | some terminal =>
            simp [quittingTerminalOutcomeReward, reward, observer]
            split_ifs <;> norm_num)
  have hcapLower :=
    quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward target observer (target observer) (by norm_num)
        abs_reward_le_one
  rw [Function.update_eq_self, target_payoff_eq_one] at hcapLower
  change quittingContinuationBestResponseValue reward target observer -
      quittingTerminalPayoff reward target observer = 0
  rw [target_payoff_eq_one]
  linarith

theorem target_debt_clock_eq_zero :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward target) clock = 0 := by
  have hcapUpper :=
    quittingContinuationBestResponseValue_le_of_terminalOutcomeReward_le
      (reward := reward) target clock 0 (by
        intro outcome
        cases outcome with
        | none => simp [quittingTerminalOutcomeReward]
        | some terminal =>
            simp [quittingTerminalOutcomeReward, reward, clock, observer])
  have hcapLower :=
    quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward target clock (target clock) (by norm_num) abs_reward_le_one
  rw [Function.update_eq_self, target_payoff_clock_eq_zero] at hcapLower
  change quittingContinuationBestResponseValue reward target clock -
      quittingTerminalPayoff reward target clock = 0
  rw [target_payoff_clock_eq_zero]
  linarith

/-- The strategically neutral positive target atom already lies at an exact
global total-debt minimizer.  What it does not satisfy is the counterexample
regime's *positive* minimum: this minimum is zero. -/
theorem target_is_zeroDebt_globalMinimizer :
    quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward target) = 0 ∧
      (∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward target) ≤
          quittingTerminalSemanticDebtSum candidate) := by
  have htarget : quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward target) = 0 := by
    unfold quittingTerminalSemanticDebtSum
    rw [Fintype.sum_bool, target_debt_observer_eq_zero,
      target_debt_clock_eq_zero]
    norm_num
  refine ⟨htarget, ?_⟩
  intro candidate hcandidate
  rw [htarget]
  unfold quittingTerminalSemanticDebtSum
  apply Finset.sum_nonneg
  intro who _hwho
  exact quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward
    (by norm_num) abs_reward_le_one hcandidate who

/-- Hence exact minimum provenance, an actual positive collision atom, and
an exact best response at the target still do not force a marked-row sign.
The positive-minimum hypothesis in the producer above is the first genuinely
counterexample-specific condition absent from this regression. -/
theorem zeroMinimum_positiveActualAtom_but_markedState_neutral :
    quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward target) = 0 ∧
      (∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward target) ≤
          quittingTerminalSemanticDebtSum candidate) ∧
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward target) observer = 0 ∧
      quittingTerminalPayoffDifferenceAtom reward target source observer
          (some collisionTerminal) = 1 ∧
      quittingTerminalOutcomeMass reward target (some collisionTerminal) = 1 ∧
      ∀ tail : Payoff Player,
        quittingRootEndpointDifference reward tail markedRoot observer = 0 ∧
          quittingRootCoordinateNashDefect reward tail markedRoot observer = 0 := by
  exact ⟨target_is_zeroDebt_globalMinimizer.1,
    target_is_zeroDebt_globalMinimizer.2, target_debt_observer_eq_zero,
    targetEdge_collisionAtom_eq_one, target_collision_mass_eq_one,
    fun tail => ⟨markedRow_endpointDifference_eq_zero tail,
      markedRow_coordinateNashDefect_eq_zero tail⟩⟩

end PositiveSlopeTargetEdgeStateMatchRegression

end GameTheory
