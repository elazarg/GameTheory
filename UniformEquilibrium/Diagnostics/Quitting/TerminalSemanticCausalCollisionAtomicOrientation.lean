/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticCausalCollisionRecipientAtom
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticAtomicBlockerBarrier

/-!
# Atomic orientation of a causal collision recipient edge

The endpoint-debt recipient is needed only when the causal best endpoint is
Continue.  If the same reached-row endpoint is Quit, the target row has a
surely quitting owner and enters the counterexample regime's atomic-blocker
barrier immediately.  The routed collision retains quantitative stage mass.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {reward : {S : Finset iota // S.Nonempty} → Payoff iota}

omit [Fintype iota] in
/-- Routing a nonsingleton coalition through one pure endpoint never produces
the empty coalition. -/
theorem quittingPureEndpointRoutedCoalition_nonempty_of_one_lt_card
    (coalition : Finset iota) (who : iota) (action : Bool)
    (hcoalition : 1 < coalition.card) :
    (quittingPureEndpointRoutedCoalition coalition who action).Nonempty := by
  cases action
  · rw [quittingPureEndpointRoutedCoalition_false]
    exact (Finset.one_lt_card_iff_nontrivial.mp hcoalition).erase_nonempty
  · simp

/-- The live root of a pure one-stage endpoint profile is the corresponding
pure coordinate update at that reached stage. -/
theorem quittingProfileLiveRoot_stagePureEndpoint_self
    (profile : (quittingGame reward).BehaviorProfile)
    (who : iota) (stage : ℕ) (action : Bool) :
    quittingProfileLiveRoot reward
        (Function.update profile who
          (quittingStagePureEndpointBehaviorDeviation
            reward profile who stage action)) stage =
      Function.update (quittingProfileLiveRoot reward profile stage) who
        (PMF.pure action) := by
  rw [quittingProfileLiveRoot_update_eq_rootSequenceUpdate,
    quittingBehaviorLiveHazard_stagePureEndpointBehaviorDeviation,
    quittingRootSequenceUpdate_stageDeviationHazard_self]

/-- A pure one-stage endpoint update does not change the probability of
reaching that stage. -/
theorem quittingLiveMass_stagePureEndpoint_eq
    (profile : (quittingGame reward).BehaviorProfile)
    (who : iota) (stage : ℕ) (action : Bool) :
    quittingLiveMass reward
        (Function.update profile who
          (quittingStagePureEndpointBehaviorDeviation
            reward profile who stage action)) stage =
      quittingLiveMass reward profile stage := by
  let root := quittingProfileLiveRoot reward profile
  let targetProfile := Function.update profile who
    (quittingStagePureEndpointBehaviorDeviation
      reward profile who stage action)
  let targetRoot := quittingProfileLiveRoot reward targetProfile
  have hagree : ∀ time, time < stage → targetRoot time = root time := by
    intro time htime
    dsimp only [targetRoot, targetProfile, root]
    rw [quittingProfileLiveRoot_update_eq_rootSequenceUpdate,
      quittingBehaviorLiveHazard_stagePureEndpointBehaviorDeviation]
    exact quittingRootSequenceUpdate_stageDeviationHazard_of_lt
      (quittingProfileLiveRoot reward profile) who (PMF.pure action)
        (fun offset ↦
          quittingProfileLiveRoot reward profile (stage + 1 + offset) who) htime
  rw [quittingLiveMass_eq_jointSurvivalWeight_profileLiveRoot,
    quittingLiveMass_eq_jointSurvivalWeight_profileLiveRoot]
  exact quittingJointSurvivalWeight_congr targetRoot root 0 stage
    (fun time htime ↦ by
      apply hagree
      omega)

/-- **Quit endpoint or Continue-recipient split.**

Assume a causal endpoint has retained a marked collision root and already
compiled its positive transfer recipient.  If the selected endpoint is Quit,
the target stage carries at least `lower^2` mass on the routed coalition and
the same row satisfies the counterexample atomic barrier: either a forced-
owner outsider defect or a punishment-refusal balance pays the full terminal
gap.  If it is Continue, the recipient atom packet is returned unchanged.
-/
theorem QuittingCounterexampleRegime.causalCollisionEndpoint_atomicBarrier_or_continueRecipient
    (regime : QuittingCounterexampleRegime reward)
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (terminal : {S : Finset iota // S.Nonempty})
    (lower epsilon : ℝ) (who : iota)
    (hlower : 0 < lower)
    (hcollision : 1 < terminal.val.card)
    (hmass : lower ≤
      quittingStageCoalitionMass reward profile stage terminal)
    (hrouted :
      let tail := quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward profile (stage + 1))
      let root := quittingProfileLiveRoot reward profile stage
      let action := quittingRootBestEndpointAction reward tail.1 root who
      let routed := quittingPureEndpointRoutedCoalition terminal.val who action
      lower ≤ quittingRootCoalitionMass
        (Function.update root who (PMF.pure action)) routed)
    (hrecipient :
      let tail := quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward profile (stage + 1))
      let root := quittingProfileLiveRoot reward profile stage
      let action := quittingRootBestEndpointAction reward tail.1 root who
      let targetStrategy := quittingStagePureEndpointBehaviorDeviation
        reward profile who stage action
      let targetProfile := Function.update profile who targetStrategy
      let gain := quittingTerminalPayoff reward targetProfile who -
        quittingTerminalPayoff reward profile who
      epsilon < gain →
        ∃ recipient ∈ Finset.univ.erase who,
          HasQuittingEndpointDebtRecipientAtom reward profile who recipient
            targetStrategy) :
    let tail := quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (stage + 1))
    let root := quittingProfileLiveRoot reward profile stage
    let action := quittingRootBestEndpointAction reward tail.1 root who
    let routed := quittingPureEndpointRoutedCoalition terminal.val who action
    let targetStrategy := quittingStagePureEndpointBehaviorDeviation
      reward profile who stage action
    let targetProfile := Function.update profile who targetStrategy
    let targetRoot := quittingProfileLiveRoot reward targetProfile stage
    let gain := quittingTerminalPayoff reward targetProfile who -
      quittingTerminalPayoff reward profile who
    (action = true ∧
        lower ^ 2 ≤
          quittingStageCoalitionMass reward targetProfile stage
            ⟨routed, by
              exact
                quittingPureEndpointRoutedCoalition_nonempty_of_one_lt_card
                  terminal.val who action hcollision⟩ ∧
        (regime.terminalGap ≤
            quittingForcedOwnerOutsiderDefect reward targetRoot who ∨
          regime.terminalGap ≤
            max 0 (-quittingAtomicBlockerBalance reward targetRoot who))) ∨
      (action = false ∧
        (epsilon < gain →
          ∃ recipient ∈ Finset.univ.erase who,
            HasQuittingEndpointDebtRecipientAtom reward profile who recipient
              targetStrategy)) := by
  dsimp only
  let tail := quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward profile (stage + 1))
  let root := quittingProfileLiveRoot reward profile stage
  let action := quittingRootBestEndpointAction reward tail.1 root who
  let routed := quittingPureEndpointRoutedCoalition terminal.val who action
  let targetStrategy := quittingStagePureEndpointBehaviorDeviation
    reward profile who stage action
  let targetProfile := Function.update profile who targetStrategy
  let targetRoot := quittingProfileLiveRoot reward targetProfile stage
  let gain := quittingTerminalPayoff reward targetProfile who -
    quittingTerminalPayoff reward profile who
  cases haction : action with
  | false =>
      exact Or.inr ⟨haction, by
        simpa only [tail, root, action, targetStrategy, targetProfile, gain]
          using hrecipient⟩
  | true =>
      left
      have hroot : targetRoot =
          Function.update root who (PMF.pure action) := by
        dsimp only [targetRoot, targetProfile, targetStrategy, root]
        exact quittingProfileLiveRoot_stagePureEndpoint_self profile who stage
          action
      have hlive : lower ≤ quittingLiveMass reward profile stage :=
        hmass.trans
          (quittingStageCoalitionMass_le_liveMass reward profile stage terminal)
      have hliveTarget : quittingLiveMass reward targetProfile stage =
          quittingLiveMass reward profile stage := by
        dsimp only [targetProfile, targetStrategy]
        exact quittingLiveMass_stagePureEndpoint_eq profile who stage action
      have hrouted' : lower ≤ quittingRootCoalitionMass targetRoot routed := by
        rw [hroot]
        simpa only [tail, root, action, routed] using hrouted
      have hstage : lower ^ 2 ≤
          quittingStageCoalitionMass reward targetProfile stage
            ⟨routed, by
              exact
                quittingPureEndpointRoutedCoalition_nonempty_of_one_lt_card
                  terminal.val who action hcollision⟩ := by
        rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
          hliveTarget, pow_two]
        exact mul_le_mul hlive hrouted' hlower.le
          (quittingLiveMass_nonneg reward profile stage)
      have howner : targetRoot who = PMF.pure true := by
        rw [hroot, haction]
        simp
      have hbarrier := regime.terminalGap_le_atomicBlockerBarrier howner
      refine ⟨haction, hstage, ?_⟩
      exact (le_max_iff.mp hbarrier)

/-- **Direct causal collision wrapper with the Quit orientation consumed.**

The tail-escape branch is unchanged.  In the profitable branch, all exact
gain, mover-debt, aggregate-transfer, and routed-cylinder data are retained.
If `epsilon < gain`, then either:

* the endpoint action is Quit and the reached target row has routed stage
  mass at least `lower ^ 2` together with the counterexample atomic barrier;
* the endpoint action is Continue and a distinct positive debt recipient has
  already been compiled into its same-edge literal atom/rectangle packet.

The atomic barrier is a strategic handoff, not by itself an equilibrium
closure theorem. -/
theorem QuittingCounterexampleRegime.causalCollision_tailEscape_or_atomicQuit_or_continueRecipient
    [Nonempty iota]
    (regime : QuittingCounterexampleRegime reward)
    (minimum : QuittingTerminalSemanticPair iota)
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (terminal : {S : Finset iota // S.Nonempty})
    (lower epsilon : ℝ) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ outcome player, |reward outcome player| ≤ M)
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumDebt : 0 < quittingTerminalSemanticDebtSum minimum)
    (hcollision : 1 < terminal.val.card)
    (hlower : 0 < lower)
    (hnear : quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward profile) ≤
      quittingTerminalSemanticDebtSum minimum + epsilon)
    (hmass : lower ≤
      quittingStageCoalitionMass reward profile stage terminal) :
    let tail := quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (stage + 1))
    (lower * quittingTerminalSemanticDebtSum minimum / 2 ≤
          quittingTerminalSemanticDebtSum tail -
            quittingTerminalSemanticDebtSum minimum ∧
        ∀ capRoot : iota → PMF Bool,
          IsεQuittingRootNash reward tail.2 0 capRoot →
          let returned := quittingTerminalSemanticPrefix reward capRoot tail
          returned ∈ quittingTerminalSemanticCarrier reward ∧
            quittingTerminalSemanticDebtSum minimum ≤
              quittingTerminalSemanticDebtSum returned ∧
            quittingTerminalSemanticDebtSum returned =
              quittingTerminalSemanticDebtSum tail -
                quittingTerminalSemanticDebtSum tail *
                  quittingRootAbsorptionMass capRoot ∧
            quittingTerminalSemanticDebtSum tail *
                quittingRootAbsorptionMass capRoot ≤
              quittingTerminalSemanticDebtSum tail -
                quittingTerminalSemanticDebtSum minimum) ∨
      ∃ who,
        let root := quittingProfileLiveRoot reward profile stage
        let action := quittingRootBestEndpointAction reward tail.1 root who
        let routed := quittingPureEndpointRoutedCoalition terminal.val who action
        let targetStrategy := quittingStagePureEndpointBehaviorDeviation
          reward profile who stage action
        let targetProfile := Function.update profile who targetStrategy
        let targetRoot := quittingProfileLiveRoot reward targetProfile stage
        let source := quittingTerminalSemanticPair reward profile
        let target := quittingTerminalSemanticPair reward targetProfile
        let gain := quittingTerminalPayoff reward targetProfile who -
          quittingTerminalPayoff reward profile who
        0 < gain ∧
          lower ^ 2 * quittingTerminalSemanticDebtSum minimum / 2 ≤
            (Fintype.card iota : ℝ) * gain ∧
          target ∈ quittingTerminalSemanticCarrier reward ∧
          quittingTerminalSemanticDebt target who =
            quittingTerminalSemanticDebt source who - gain ∧
          gain - epsilon ≤
            ∑ recipient ∈ Finset.univ.erase who,
              quittingTerminalSemanticDebtChange source target recipient ∧
          lower ≤ quittingRootCoalitionMass
            (Function.update root who (PMF.pure action)) routed ∧
          ((who ∈ terminal.val ∧ action = true ∧ routed = terminal.val) ∨
            (who ∈ terminal.val ∧ action = false ∧
              routed = terminal.val.erase who) ∨
            (who ∉ terminal.val ∧ action = true ∧
              routed = insert who terminal.val) ∨
            (who ∉ terminal.val ∧ action = false ∧
              routed = terminal.val)) ∧
          (epsilon < gain →
            (action = true ∧
                lower ^ 2 ≤
                  quittingStageCoalitionMass reward targetProfile stage
                    ⟨routed,
                      quittingPureEndpointRoutedCoalition_nonempty_of_one_lt_card
                        terminal.val who action hcollision⟩ ∧
                (regime.terminalGap ≤
                    quittingForcedOwnerOutsiderDefect reward targetRoot who ∨
                  regime.terminalGap ≤
                    max 0
                      (-quittingAtomicBlockerBalance reward targetRoot who))) ∨
              (action = false ∧
                ∃ recipient ∈ Finset.univ.erase who,
                  HasQuittingEndpointDebtRecipientAtom reward profile who
                    recipient targetStrategy)) := by
  dsimp only
  have hdispatch := causalCollision_tailEscape_or_quantitativeRecipientAtom
    reward minimum profile stage terminal lower epsilon hM hreward
      hminimumCarrier hminimum hminimumDebt hcollision hlower hnear hmass
  rcases hdispatch with hescape | hgain
  · exact Or.inl hescape
  · right
    rcases hgain with ⟨who, hpositive, hquantitative, htarget, hmover,
      htransfer, hrecipient, hrouted, horientation⟩
    refine ⟨who, hpositive, hquantitative, htarget, hmover, htransfer,
      hrouted, horientation, ?_⟩
    intro hepsilon
    have horiented := regime.causalCollisionEndpoint_atomicBarrier_or_continueRecipient
      profile stage terminal lower epsilon who hlower hcollision hmass hrouted
        hrecipient
    rcases horiented with hquit | hcontinue
    · exact Or.inl hquit
    · exact Or.inr ⟨hcontinue.1, hcontinue.2 hepsilon⟩

end GameTheory
