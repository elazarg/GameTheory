/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticSingletonClockDebtFace
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauDefectStratification
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetReprojectionTwoFaceBridge

/-!
# Finite reset extraction from a singleton-clock defect reservoir

The singleton-clock debt estimate produces an all-player defect occupation on
the same finite window.  A strict partial endpoint move at any one date retains
at least its `1 - lambda` share of every chronological coalition atom, including
atoms before and after the modified date.  Consequently the defect need not be
on a date at which the singleton clock itself is positive: any positive defect
row in the window gives a literal state-matched reset while preserving the
whole singleton window.

Finite averaging selects the reset row and player with the exact loss
`cutoff * Fintype.card iota`.  Thus label, state, and finite-clock provenance
are all retained.  The remaining quantitative seam is precisely the absence
of a cutoff-independent concentration estimate, or of a legal unilateral
deviation that collects a diffuse multi-date reservoir without that loss.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {iota : Type} [Fintype iota] [DecidableEq iota]

/-- Away from the modified date, a stagewise partial endpoint deviation has
exactly the original live root. -/
theorem quittingProfileLiveRoot_stagePartialBestEndpoint_of_ne
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : iota) (stage time : ℕ) (lambda : ℝ)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (htime : time ≠ stage) :
    quittingProfileLiveRoot reward
        (Function.update profile who
          (quittingStagePartialBestEndpointBehaviorDeviation
            reward profile who stage lambda hlambda0 hlambda1)) time =
      quittingProfileLiveRoot reward profile time := by
  rw [quittingProfileLiveRoot_update_eq_rootSequenceUpdate]
  dsimp only [quittingStagePartialBestEndpointBehaviorDeviation]
  rw [quittingBehaviorLiveHazard_stageMarginalBehaviorDeviation]
  by_cases hbefore : time < stage
  · exact quittingRootSequenceUpdate_stageDeviationHazard_of_lt
      (quittingProfileLiveRoot reward profile) who _ _ hbefore
  · have hafter : stage < time := by omega
    obtain ⟨offset, hoffset⟩ : ∃ offset, time = stage + 1 + offset := by
      exact ⟨time - (stage + 1), by omega⟩
    subst time
    rw [quittingRootSequenceUpdate, quittingStageDeviationHazard_add]
    exact Function.update_eq_self who _

/-- A strict partial endpoint move at one date retains at least its
`1 - lambda` share of the joint live mass at every date. -/
theorem one_sub_mul_liveMass_le_stagePartialBestEndpoint
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : iota) (stage time : ℕ) (lambda : ℝ)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    (1 - lambda) * quittingLiveMass reward profile time ≤
      quittingLiveMass reward
        (Function.update profile who
          (quittingStagePartialBestEndpointBehaviorDeviation
            reward profile who stage lambda hlambda0 hlambda1)) time := by
  let targetProfile := Function.update profile who
    (quittingStagePartialBestEndpointBehaviorDeviation
      reward profile who stage lambda hlambda0 hlambda1)
  let sourceRoot := quittingProfileLiveRoot reward profile
  let targetRoot := quittingProfileLiveRoot reward targetProfile
  by_cases htime : time ≤ stage
  · have hagree : ∀ offset, offset < time →
        targetRoot offset = sourceRoot offset := by
      intro offset hoffset
      apply quittingProfileLiveRoot_stagePartialBestEndpoint_of_ne
      omega
    have hliveEq : quittingLiveMass reward targetProfile time =
        quittingLiveMass reward profile time := by
      rw [quittingLiveMass_eq_jointSurvivalWeight_profileLiveRoot,
        quittingLiveMass_eq_jointSurvivalWeight_profileLiveRoot]
      exact quittingJointSurvivalWeight_congr targetRoot sourceRoot 0 time
        (fun offset hoffset ↦ by simpa using hagree offset hoffset)
    rw [hliveEq]
    have hlive := quittingLiveMass_nonneg reward profile time
    nlinarith
  · have hstageTime : stage < time := lt_of_not_ge htime
    let oldContinue : ℕ → ℝ := fun offset ↦
      quittingStationaryContinueMass (sourceRoot offset)
    let newContinue : ℕ → ℝ := fun offset ↦
      quittingStationaryContinueMass (targetRoot offset)
    have hstageMem : stage ∈ Finset.range time :=
      Finset.mem_range.mpr hstageTime
    have hother : ∀ offset ∈ (Finset.range time).erase stage,
        newContinue offset = oldContinue offset := by
      intro offset hoffset
      have hne : offset ≠ stage := (Finset.mem_erase.mp hoffset).1
      exact congrArg quittingStationaryContinueMass
        (quittingProfileLiveRoot_stagePartialBestEndpoint_of_ne
          reward profile who stage offset lambda hlambda0 hlambda1 hne)
    have hrest :
        (∏ offset ∈ (Finset.range time).erase stage,
            newContinue offset) =
          ∏ offset ∈ (Finset.range time).erase stage,
            oldContinue offset :=
      Finset.prod_congr rfl hother
    have hstageRoot : targetRoot stage =
        quittingPartialEndpointRoot (sourceRoot stage) who
          (quittingRootBestEndpointAction reward
            (quittingTerminalSemanticPair reward
              (quittingAllContinueProfileSpine reward profile (stage + 1))).1
            (sourceRoot stage) who)
          lambda hlambda0 hlambda1 := by
      exact quittingProfileLiveRoot_stagePartialBestEndpoint_self
        (reward := reward) profile who stage lambda hlambda0 hlambda1
    have hstageContinue :
        (1 - lambda) * oldContinue stage ≤ newContinue stage := by
      dsimp only [oldContinue, newContinue]
      rw [hstageRoot]
      rw [quittingStationaryContinueMass_partialEndpointRoot]
      exact le_add_of_nonneg_right
        (mul_nonneg hlambda0 (quittingStationaryContinueMass_nonneg _))
    have hrestNonneg : 0 ≤
        ∏ offset ∈ (Finset.range time).erase stage,
          oldContinue offset := by
      exact Finset.prod_nonneg fun offset _ ↦
        quittingStationaryContinueMass_nonneg _
    rw [quittingLiveMass_eq_jointSurvivalWeight_profileLiveRoot,
      quittingLiveMass_eq_jointSurvivalWeight_profileLiveRoot,
      quittingJointSurvivalWeight_eq_prod,
      quittingJointSurvivalWeight_eq_prod]
    simp only [Nat.zero_add]
    rw [← Finset.mul_prod_erase (Finset.range time) newContinue hstageMem,
      hrest,
      ← Finset.mul_prod_erase (Finset.range time) oldContinue hstageMem]
    calc
      (1 - lambda) *
            (oldContinue stage *
              ∏ offset ∈ (Finset.range time).erase stage,
                oldContinue offset) =
          ((1 - lambda) * oldContinue stage) *
            ∏ offset ∈ (Finset.range time).erase stage,
              oldContinue offset := by ring
      _ ≤ newContinue stage *
            ∏ offset ∈ (Finset.range time).erase stage,
              oldContinue offset :=
        mul_le_mul_of_nonneg_right hstageContinue hrestNonneg

/-- Every chronological coalition atom, before, at, or after the modified
date, retains at least the `1 - lambda` share of its old mass. -/
theorem one_sub_mul_stageCoalitionMass_le_stagePartialBestEndpoint_all
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : iota) (stage time : ℕ)
    (terminal : {S : Finset iota // S.Nonempty})
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    (1 - lambda) * quittingStageCoalitionMass reward profile time terminal ≤
      quittingStageCoalitionMass reward
        (Function.update profile who
          (quittingStagePartialBestEndpointBehaviorDeviation
            reward profile who stage lambda hlambda0 hlambda1))
        time terminal := by
  by_cases htime : time = stage
  · subst time
    exact one_sub_mul_stageCoalitionMass_le_stagePartialBestEndpoint
      (reward := reward) profile who stage terminal lambda hlambda0 hlambda1
  · have hroot := quittingProfileLiveRoot_stagePartialBestEndpoint_of_ne
      reward profile who stage time lambda hlambda0 hlambda1 htime
    have hlive := one_sub_mul_liveMass_le_stagePartialBestEndpoint
      reward profile who stage time lambda hlambda0 hlambda1
    rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
      quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass, hroot]
    have hmass := MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg
      (quittingProfileLiveRoot reward profile time) terminal.val
    calc
      (1 - lambda) *
            (quittingLiveMass reward profile time *
              quittingRootCoalitionMass
                (quittingProfileLiveRoot reward profile time) terminal.val) =
          ((1 - lambda) * quittingLiveMass reward profile time) *
            quittingRootCoalitionMass
              (quittingProfileLiveRoot reward profile time) terminal.val := by
        ring
      _ ≤ quittingLiveMass reward
              (Function.update profile who
                (quittingStagePartialBestEndpointBehaviorDeviation
                  reward profile who stage lambda hlambda0 hlambda1)) time *
            quittingRootCoalitionMass
              (quittingProfileLiveRoot reward profile time) terminal.val :=
        mul_le_mul_of_nonneg_right hlive hmass

/-- Consequently a partial endpoint reset at any date preserves the same
fraction of every finite chronological coalition window. -/
theorem one_sub_mul_sum_stageCoalitionMass_le_stagePartialBestEndpoint
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : iota) (stage cutoff : ℕ)
    (terminal : {S : Finset iota // S.Nonempty})
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    (1 - lambda) *
        (∑ time ∈ Finset.range cutoff,
          quittingStageCoalitionMass reward profile time terminal) ≤
      ∑ time ∈ Finset.range cutoff,
        quittingStageCoalitionMass reward
          (Function.update profile who
            (quittingStagePartialBestEndpointBehaviorDeviation
              reward profile who stage lambda hlambda0 hlambda1))
          time terminal := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun time _ ↦
    one_sub_mul_stageCoalitionMass_le_stagePartialBestEndpoint_all
      reward profile who stage time terminal lambda hlambda0 hlambda1

/-- A positive total local defect on a row carrying the owner's singleton
cylinder selects one literal profitable endpoint deviation.  Its root and
continuation are the actual state-matched row, and the same singleton cylinder
is routed without loss to one of its four one-coordinate toggles. -/
theorem exists_stageBestEndpointDeviation_singletonRouting_of_totalDefect_pos
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile)
    (owner : iota) (stage : ℕ)
    (hstage : 0 < quittingStageCoalitionMass reward profile stage
      (quittingSingletonTerminal owner))
    (hdefect : 0 < quittingSpineTotalNashDefect reward profile stage) :
    ∃ who,
      let tail := quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward profile (stage + 1))
      let root := quittingProfileLiveRoot reward profile stage
      let action := quittingRootBestEndpointAction reward tail.1 root who
      let routed := quittingPureEndpointRoutedCoalition {owner} who action
      0 < quittingRootCoordinateNashDefect reward tail.1 root who ∧
        quittingTerminalPayoff reward
              (Function.update profile who
                (quittingStagePureEndpointBehaviorDeviation
                  reward profile who stage action)) who -
            quittingTerminalPayoff reward profile who =
              quittingLiveMass reward profile stage *
                quittingRootCoordinateNashDefect reward tail.1 root who ∧
        0 < quittingTerminalPayoff reward
              (Function.update profile who
                (quittingStagePureEndpointBehaviorDeviation
                  reward profile who stage action)) who -
            quittingTerminalPayoff reward profile who ∧
        0 < quittingRootCoalitionMass
          (Function.update root who (PMF.pure action)) routed ∧
        quittingRootCoalitionMass root {owner} ≤
          quittingRootCoalitionMass
            (Function.update root who (PMF.pure action)) routed ∧
        ((who = owner ∧ action = true ∧ routed = {owner}) ∨
          (who = owner ∧ action = false ∧ routed = ∅) ∨
          (who ≠ owner ∧ action = true ∧ routed = {owner, who}) ∨
          (who ≠ owner ∧ action = false ∧ routed = {owner})) := by
  let tail := quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward profile (stage + 1))
  let root := quittingProfileLiveRoot reward profile stage
  have hnonneg : ∀ who ∈ (Finset.univ : Finset iota),
      0 ≤ quittingRootCoordinateNashDefect reward tail.1 root who := by
    intro who _
    exact quittingRootCoordinateNashDefect_nonneg reward _ _ who
  have hsum : 0 < ∑ who,
      quittingRootCoordinateNashDefect reward tail.1 root who := by
    simpa only [quittingSpineTotalNashDefect,
      quittingRootTotalNashDefect, tail, root] using hdefect
  obtain ⟨who, _hwho, hwhoDefect⟩ :=
    (Finset.sum_pos_iff_of_nonneg hnonneg).mp hsum
  have hlive : 0 < quittingLiveMass reward profile stage :=
    hstage.trans_le (quittingStageCoalitionMass_le_liveMass
      reward profile stage (quittingSingletonTerminal owner))
  have hrootMass : 0 < quittingRootCoalitionMass root {owner} := by
    rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass]
      at hstage
    rcases mul_pos_iff.mp hstage with hpositive | hnegative
    · exact hpositive.2
    · exact (not_lt_of_ge (quittingLiveMass_nonneg reward profile stage)
        hnegative.1).elim
  refine ⟨who, hwhoDefect, ?_⟩
  have hrouting :=
    quittingTerminalPayoff_stageBestEndpointDeviation_markedRouting
      reward profile who stage {owner} hlive hrootMass hwhoDefect
  dsimp only at hrouting ⊢
  refine ⟨hrouting.1, hrouting.2.1, hrouting.2.2.1,
    hrouting.2.2.2.1, ?_⟩
  rcases hrouting.2.2.2.2 with hkeep | hdrop | hjoin | hsuppress
  · left
    simpa using hkeep
  · right; left
    rcases hdrop with ⟨hmem, haction, hrouted⟩
    have heq : who = owner := by simpa using hmem
    subst who
    exact ⟨rfl, haction, by simpa using hrouted⟩
  · right; right; left
    rcases hjoin with ⟨hne, haction, hrouted⟩
    have hne' : who ≠ owner := by simpa using hne
    exact ⟨hne', haction, by simpa [Finset.pair_comm] using hrouted⟩
  · right; right; right
    rcases hsuppress with ⟨hne, haction, hrouted⟩
    exact ⟨by simpa using hne, haction, hrouted⟩

/-- A positive survival-weighted total defect atom selects a coordinate at
least as large as the player average and produces a literal strict fractional
reset at that actual row.  The selected debt action and the minimum-reference
opposite-coordinate transfer account are exact. -/
theorem exists_stagePartialBestEndpoint_transfer_of_liveTotalDefect_pos
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (minimum : QuittingTerminalSemanticPair iota)
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hdefect : 0 < quittingLiveMass reward profile stage *
      quittingSpineTotalNashDefect reward profile stage)
    (lambda : ℝ) (hlambda0 : 0 < lambda) (hlambda1 : lambda < 1) :
    ∃ who,
      let tail := quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward profile (stage + 1))
      let root := quittingProfileLiveRoot reward profile stage
      let action := quittingRootBestEndpointAction reward tail.1 root who
      let targetProfile := Function.update profile who
        (quittingStageMarginalBehaviorDeviation reward profile who stage
          (quittingPartialEndpointMarginal root who action lambda
            hlambda0.le hlambda1.le))
      let source := quittingTerminalSemanticPair reward profile
      let target := quittingTerminalSemanticPair reward targetProfile
      let sourcePoint : QuittingTerminalSemanticLawPoint iota :=
        (source, quittingTerminalOutcomeMass reward profile)
      let targetPoint : QuittingTerminalSemanticLawPoint iota :=
        (target, quittingTerminalOutcomeMass reward targetProfile)
      let gain := lambda * quittingLiveMass reward profile stage *
        quittingRootCoordinateNashDefect reward tail.1 root who
      quittingLiveMass reward profile stage *
          quittingSpineTotalNashDefect reward profile stage ≤
        (Fintype.card iota : ℝ) *
          (quittingLiveMass reward profile stage *
            quittingRootCoordinateNashDefect reward tail.1 root who) ∧
        sourcePoint ∈ quittingTerminalSemanticLawCarrier reward ∧
        targetPoint ∈ quittingTerminalSemanticLawCarrier reward ∧
        0 < gain ∧
        quittingTerminalSemanticDebt target who =
          quittingTerminalSemanticDebt source who - gain ∧
        (∑ recipient ∈ Finset.univ.erase who,
            quittingTerminalSemanticDebtChange source target recipient) =
          (quittingTerminalSemanticDebtSum target -
            quittingTerminalSemanticDebtSum source) + gain ∧
        gain ≤
          (quittingTerminalSemanticDebtSum source -
            quittingTerminalSemanticDebtSum minimum) +
          ∑ recipient ∈ Finset.univ.erase who,
            quittingTerminalSemanticDebtChange source target recipient ∧
        0 < quittingTerminalSemanticDebt target who := by
  let tail := quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward profile (stage + 1))
  let root := quittingProfileLiveRoot reward profile stage
  have hnonneg : ∀ who ∈ (Finset.univ : Finset iota),
      0 ≤ quittingLiveMass reward profile stage *
        quittingRootCoordinateNashDefect reward tail.1 root who := by
    intro who _
    exact mul_nonneg (quittingLiveMass_nonneg reward profile stage)
      (quittingRootCoordinateNashDefect_nonneg reward _ _ who)
  have hsum : 0 < ∑ who,
      quittingLiveMass reward profile stage *
        quittingRootCoordinateNashDefect reward tail.1 root who := by
    rw [← Finset.mul_sum]
    simpa only [quittingSpineTotalNashDefect,
      quittingRootTotalNashDefect, tail, root] using hdefect
  have huniv : (Finset.univ : Finset iota).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at hsum
    simp at hsum
  obtain ⟨who, _hwho, haverage⟩ :=
    QuittingMarkedFencePacket.exists_sum_le_card_mul
      (Finset.univ : Finset iota) huniv
      (fun player => quittingLiveMass reward profile stage *
        quittingRootCoordinateNashDefect reward tail.1 root player)
  have hrowBound :
      quittingLiveMass reward profile stage *
          quittingSpineTotalNashDefect reward profile stage ≤
        (Fintype.card iota : ℝ) *
          (quittingLiveMass reward profile stage *
            quittingRootCoordinateNashDefect reward tail.1 root who) := by
    rw [quittingSpineTotalNashDefect, quittingRootTotalNashDefect,
      Finset.mul_sum]
    simpa only [Finset.sum_filter, Finset.mem_univ, ↓reduceIte,
      Finset.card_univ] using haverage
  have hwhoDefect : 0 < quittingLiveMass reward profile stage *
      quittingRootCoordinateNashDefect reward tail.1 root who := by
    have hcardNonneg : 0 ≤ (Fintype.card iota : ℝ) := by positivity
    by_contra hnot
    have hnonpos : quittingLiveMass reward profile stage *
        quittingRootCoordinateNashDefect reward tail.1 root who ≤ 0 :=
      le_of_not_gt hnot
    nlinarith
  refine ⟨who, ?_⟩
  dsimp only
  refine ⟨hrowBound, ?_⟩
  let action := quittingRootBestEndpointAction reward tail.1 root who
  let targetProfile := Function.update profile who
    (quittingStageMarginalBehaviorDeviation reward profile who stage
      (quittingPartialEndpointMarginal root who action lambda
        hlambda0.le hlambda1.le))
  let source := quittingTerminalSemanticPair reward profile
  let target := quittingTerminalSemanticPair reward targetProfile
  let gain := lambda * quittingLiveMass reward profile stage *
    quittingRootCoordinateNashDefect reward tail.1 root who
  have hgain : 0 < gain := by
    simpa only [gain, mul_assoc] using mul_pos hlambda0 hwhoDefect
  have hsourceDebt : 0 < quittingTerminalSemanticDebt source who := by
    have hcollectable := quittingLiveMass_mul_coordinateNashDefect_le_initialDebt
      (reward := reward) profile who stage hM hreward
    exact hwhoDefect.trans_le hcollectable
  have hsourcePoint :
      (source, quittingTerminalOutcomeMass reward profile) ∈
        quittingTerminalSemanticLawCarrier reward :=
    quittingTerminalSemanticLawPoint_mem_carrier reward profile
  have htargetPoint :
      (target, quittingTerminalOutcomeMass reward targetProfile) ∈
        quittingTerminalSemanticLawCarrier reward :=
    quittingTerminalSemanticLawPoint_mem_carrier reward targetProfile
  have hdecrease : quittingTerminalSemanticDebt target who =
      quittingTerminalSemanticDebt source who - gain :=
    quittingTerminalSemanticDebt_stagePartialBestEndpoint_eq
      reward profile who stage lambda hlambda0.le hlambda1.le
  have htransferExact :
      (∑ recipient ∈ Finset.univ.erase who,
          quittingTerminalSemanticDebtChange source target recipient) =
        (quittingTerminalSemanticDebtSum target -
          quittingTerminalSemanticDebtSum source) + gain := by
    have hsumChange := Finset.sum_erase_add Finset.univ
      (fun player ↦ quittingTerminalSemanticDebtChange source target player)
      (Finset.mem_univ who)
    have htotal : (∑ player,
        quittingTerminalSemanticDebtChange source target player) =
        quittingTerminalSemanticDebtSum target -
          quittingTerminalSemanticDebtSum source := by
      unfold quittingTerminalSemanticDebtChange
        quittingTerminalSemanticDebtSum
      rw [Finset.sum_sub_distrib]
    have hwhoChange : quittingTerminalSemanticDebtChange source target who =
        -gain := by
      unfold quittingTerminalSemanticDebtChange
      rw [hdecrease]
      ring
    rw [htotal, hwhoChange] at hsumChange
    linarith
  have htargetCarrier : target ∈
      quittingTerminalSemanticCarrier reward :=
    quittingTerminalSemanticPair_mem_carrier reward targetProfile
  have htransfer := minimumReference_opponentTransfer_of_coordinateDecrease
    reward minimum source target who gain hminimum htargetCarrier hdecrease
  have htargetDebt : 0 < quittingTerminalSemanticDebt target who := by
    exact terminalSemanticDebt_stagePartialBestEndpoint_pos
      (reward := reward) profile who stage lambda hlambda0.le hlambda1
        hM hreward hsourceDebt
  exact ⟨hsourcePoint, htargetPoint, hgain, hdecrease, htransferExact,
    htransfer, htargetDebt⟩

/-- A singleton/defect overlap row also supplies a strict fractional reset
which preserves positive mass on the original singleton cylinder.  The source
and target are literal profiles, the selected debt decrease is exact, and the
minimum-reference transfer account has no unmatched player label. -/
theorem exists_stagePartialBestEndpoint_singletonTransfer_of_totalDefect_pos
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (minimum : QuittingTerminalSemanticPair iota)
    (profile : (quittingGame reward).BehaviorProfile)
    (owner : iota) (stage : ℕ)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hstage : 0 < quittingStageCoalitionMass reward profile stage
      (quittingSingletonTerminal owner))
    (hdefect : 0 < quittingSpineTotalNashDefect reward profile stage)
    (lambda : ℝ) (hlambda0 : 0 < lambda) (hlambda1 : lambda < 1) :
    ∃ who,
      let tail := quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward profile (stage + 1))
      let root := quittingProfileLiveRoot reward profile stage
      let action := quittingRootBestEndpointAction reward tail.1 root who
      let targetProfile := Function.update profile who
        (quittingStageMarginalBehaviorDeviation reward profile who stage
          (quittingPartialEndpointMarginal root who action lambda
            hlambda0.le hlambda1.le))
      let source := quittingTerminalSemanticPair reward profile
      let target := quittingTerminalSemanticPair reward targetProfile
      let sourcePoint : QuittingTerminalSemanticLawPoint iota :=
        (source, quittingTerminalOutcomeMass reward profile)
      let targetPoint : QuittingTerminalSemanticLawPoint iota :=
        (target, quittingTerminalOutcomeMass reward targetProfile)
      let gain := lambda * quittingLiveMass reward profile stage *
        quittingRootCoordinateNashDefect reward tail.1 root who
      sourcePoint ∈ quittingTerminalSemanticLawCarrier reward ∧
        targetPoint ∈ quittingTerminalSemanticLawCarrier reward ∧
        0 < gain ∧
        quittingTerminalSemanticDebt target who =
          quittingTerminalSemanticDebt source who - gain ∧
        (∑ recipient ∈ Finset.univ.erase who,
            quittingTerminalSemanticDebtChange source target recipient) =
          (quittingTerminalSemanticDebtSum target -
            quittingTerminalSemanticDebtSum source) + gain ∧
        gain ≤
          (quittingTerminalSemanticDebtSum source -
            quittingTerminalSemanticDebtSum minimum) +
          ∑ recipient ∈ Finset.univ.erase who,
            quittingTerminalSemanticDebtChange source target recipient ∧
        (1 - lambda) *
            quittingStageCoalitionMass reward profile stage
              (quittingSingletonTerminal owner) ≤
          quittingStageCoalitionMass reward targetProfile stage
            (quittingSingletonTerminal owner) ∧
        0 < quittingStageCoalitionMass reward targetProfile stage
          (quittingSingletonTerminal owner) ∧
        0 < quittingTerminalSemanticDebt target who := by
  let tail := quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward profile (stage + 1))
  let root := quittingProfileLiveRoot reward profile stage
  have hnonneg : ∀ who ∈ (Finset.univ : Finset iota),
      0 ≤ quittingRootCoordinateNashDefect reward tail.1 root who := by
    intro who _
    exact quittingRootCoordinateNashDefect_nonneg reward _ _ who
  have hsum : 0 < ∑ who,
      quittingRootCoordinateNashDefect reward tail.1 root who := by
    simpa only [quittingSpineTotalNashDefect,
      quittingRootTotalNashDefect, tail, root] using hdefect
  obtain ⟨who, _hwho, hwhoDefect⟩ :=
    (Finset.sum_pos_iff_of_nonneg hnonneg).mp hsum
  refine ⟨who, ?_⟩
  dsimp only
  let action := quittingRootBestEndpointAction reward tail.1 root who
  let targetProfile := Function.update profile who
    (quittingStageMarginalBehaviorDeviation reward profile who stage
      (quittingPartialEndpointMarginal root who action lambda
        hlambda0.le hlambda1.le))
  let source := quittingTerminalSemanticPair reward profile
  let target := quittingTerminalSemanticPair reward targetProfile
  let gain := lambda * quittingLiveMass reward profile stage *
    quittingRootCoordinateNashDefect reward tail.1 root who
  have hlive : 0 < quittingLiveMass reward profile stage :=
    hstage.trans_le (quittingStageCoalitionMass_le_liveMass
      reward profile stage (quittingSingletonTerminal owner))
  have hgain : 0 < gain := mul_pos (mul_pos hlambda0 hlive) hwhoDefect
  have hsourceDebt : 0 < quittingTerminalSemanticDebt source who := by
    have hcollectable := quittingLiveMass_mul_coordinateNashDefect_le_initialDebt
      (reward := reward) profile who stage hM hreward
    exact (mul_pos hlive hwhoDefect).trans_le hcollectable
  have hsourcePoint :
      (source, quittingTerminalOutcomeMass reward profile) ∈
        quittingTerminalSemanticLawCarrier reward :=
    quittingTerminalSemanticLawPoint_mem_carrier reward profile
  have htargetPoint :
      (target, quittingTerminalOutcomeMass reward targetProfile) ∈
        quittingTerminalSemanticLawCarrier reward :=
    quittingTerminalSemanticLawPoint_mem_carrier reward targetProfile
  have hdecrease : quittingTerminalSemanticDebt target who =
      quittingTerminalSemanticDebt source who - gain :=
    quittingTerminalSemanticDebt_stagePartialBestEndpoint_eq
      reward profile who stage lambda hlambda0.le hlambda1.le
  have htransferExact :
      (∑ recipient ∈ Finset.univ.erase who,
          quittingTerminalSemanticDebtChange source target recipient) =
        (quittingTerminalSemanticDebtSum target -
          quittingTerminalSemanticDebtSum source) + gain := by
    have hsumChange := Finset.sum_erase_add Finset.univ
      (fun player ↦ quittingTerminalSemanticDebtChange source target player)
      (Finset.mem_univ who)
    have htotal : (∑ player,
        quittingTerminalSemanticDebtChange source target player) =
        quittingTerminalSemanticDebtSum target -
          quittingTerminalSemanticDebtSum source := by
      unfold quittingTerminalSemanticDebtChange
        quittingTerminalSemanticDebtSum
      rw [Finset.sum_sub_distrib]
    have hwhoChange : quittingTerminalSemanticDebtChange source target who =
        -gain := by
      unfold quittingTerminalSemanticDebtChange
      rw [hdecrease]
      ring
    rw [htotal, hwhoChange] at hsumChange
    linarith
  have htargetCarrier : target ∈
      quittingTerminalSemanticCarrier reward :=
    quittingTerminalSemanticPair_mem_carrier reward targetProfile
  have htransfer := minimumReference_opponentTransfer_of_coordinateDecrease
    reward minimum source target who gain hminimum htargetCarrier hdecrease
  have hretention :=
    one_sub_mul_stageCoalitionMass_le_stagePartialBestEndpoint
      (reward := reward) profile who stage (quittingSingletonTerminal owner)
        lambda hlambda0.le hlambda1.le
  have htargetStage : 0 < quittingStageCoalitionMass reward targetProfile stage
      (quittingSingletonTerminal owner) := by
    have hpositive : 0 < (1 - lambda) *
        quittingStageCoalitionMass reward profile stage
          (quittingSingletonTerminal owner) :=
      mul_pos (sub_pos.mpr hlambda1) hstage
    exact hpositive.trans_le hretention
  have htargetDebt : 0 < quittingTerminalSemanticDebt target who := by
    exact terminalSemanticDebt_stagePartialBestEndpoint_pos
      (reward := reward) profile who stage lambda hlambda0.le hlambda1
        hM hreward hsourceDebt
  exact ⟨hsourcePoint, htargetPoint, hgain, hdecrease, htransferExact,
    htransfer, hretention, htargetStage, htargetDebt⟩

/-- **Singleton-clock overlap or off-clock leakage.**

Once `faceFloor * clockMass` strictly exceeds the one near-minimality error,
the all-player defect occupation is positive.  Either some positive singleton
row carries positive total defect, or a positive defect summand occurs at a
row on which that singleton has exactly zero mass.

The second branch is the precise temporal-support premise still absent from
the quantile-block Nashification route.  Neither compactness nor finite-player
pigeonholing can remove it. -/
theorem exists_singletonClock_defectOverlap_or_offClockLeak
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile)
    (owner : iota)
    (reference epsilon faceFloor clockMass : ℝ) (cutoff : ℕ) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hinitial : 0 ≤ quittingSpineDebtExcess reward profile reference 0)
    (hnear : ∀ time ≤ cutoff,
      quittingSpineDebtExcess reward profile reference time ≤ epsilon)
    (hfaceFloor : 0 ≤ faceFloor)
    (hface : ∀ time < cutoff, faceFloor ≤
      quittingTerminalSemanticComplementaryDebt
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward profile (time + 1)))
        owner)
    (hclock : clockMass ≤
      ∑ time ∈ Finset.range cutoff,
        quittingStageCoalitionMass reward profile time
          (quittingSingletonTerminal owner))
    (hstrict : epsilon < faceFloor * clockMass) :
    (∃ time < cutoff,
      0 < quittingStageCoalitionMass reward profile time
        (quittingSingletonTerminal owner) ∧
      0 < quittingSpineTotalNashDefect reward profile time) ∨
      ∃ time < cutoff,
        quittingStageCoalitionMass reward profile time
            (quittingSingletonTerminal owner) = 0 ∧
          0 < quittingLiveMass reward profile time *
            quittingSpineTotalNashDefect reward profile time := by
  have hbudget := faceFloor_mul_clockMass_le_epsilon_add_defect
    reward profile owner reference epsilon faceFloor clockMass cutoff
      hM hreward hinitial hnear hfaceFloor hface hclock
  have hoccupation : 0 < ∑ time ∈ Finset.range cutoff,
      quittingLiveMass reward profile time *
        quittingSpineTotalNashDefect reward profile time := by
    linarith
  have hnonneg : ∀ time ∈ Finset.range cutoff,
      0 ≤ quittingLiveMass reward profile time *
        quittingSpineTotalNashDefect reward profile time := by
    intro time _
    exact mul_nonneg (quittingLiveMass_nonneg reward profile time)
      (quittingRootTotalNashDefect_nonneg reward _ _)
  obtain ⟨time, htime, htimeDefect⟩ :=
    (Finset.sum_pos_iff_of_nonneg hnonneg).mp hoccupation
  have htimeLt : time < cutoff := Finset.mem_range.mp htime
  by_cases hclockRow : quittingStageCoalitionMass reward profile time
      (quittingSingletonTerminal owner) = 0
  · exact Or.inr ⟨time, htimeLt, hclockRow, htimeDefect⟩
  · left
    have hclockNonneg := quittingStageCoalitionMass_nonneg reward profile time
      (quittingSingletonTerminal owner)
    have hclockPos : 0 < quittingStageCoalitionMass reward profile time
        (quittingSingletonTerminal owner) :=
      lt_of_le_of_ne hclockNonneg (Ne.symm hclockRow)
    have htotalNonneg : 0 ≤ quittingSpineTotalNashDefect
        reward profile time := quittingRootTotalNashDefect_nonneg reward _ _
    have htotalPos : 0 < quittingSpineTotalNashDefect reward profile time := by
      rcases mul_pos_iff.mp htimeDefect with hpositive | hnegative
      · exact hpositive.2
      · exact (not_lt_of_ge htotalNonneg hnegative.2).elim
    exact ⟨time, htimeLt, hclockPos, htotalPos⟩

/-- The literal semantic/law certificate carried by one strict partial
best-endpoint reset. -/
def IsQuittingStagePartialBestEndpointTransfer
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (minimum : QuittingTerminalSemanticPair iota)
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (who : iota) (lambda : ℝ)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) : Prop :=
  let tail := quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward profile (stage + 1))
  let root := quittingProfileLiveRoot reward profile stage
  let action := quittingRootBestEndpointAction reward tail.1 root who
  let targetProfile := Function.update profile who
    (quittingStageMarginalBehaviorDeviation reward profile who stage
      (quittingPartialEndpointMarginal root who action lambda
        hlambda0 hlambda1))
  let source := quittingTerminalSemanticPair reward profile
  let target := quittingTerminalSemanticPair reward targetProfile
  let sourcePoint : QuittingTerminalSemanticLawPoint iota :=
    (source, quittingTerminalOutcomeMass reward profile)
  let targetPoint : QuittingTerminalSemanticLawPoint iota :=
    (target, quittingTerminalOutcomeMass reward targetProfile)
  let gain := lambda * quittingLiveMass reward profile stage *
    quittingRootCoordinateNashDefect reward tail.1 root who
  sourcePoint ∈ quittingTerminalSemanticLawCarrier reward ∧
    targetPoint ∈ quittingTerminalSemanticLawCarrier reward ∧
    0 < gain ∧
    quittingTerminalSemanticDebt target who =
      quittingTerminalSemanticDebt source who - gain ∧
    (∑ recipient ∈ Finset.univ.erase who,
        quittingTerminalSemanticDebtChange source target recipient) =
      (quittingTerminalSemanticDebtSum target -
        quittingTerminalSemanticDebtSum source) + gain ∧
    gain ≤
      (quittingTerminalSemanticDebtSum source -
        quittingTerminalSemanticDebtSum minimum) +
      ∑ recipient ∈ Finset.univ.erase who,
        quittingTerminalSemanticDebtChange source target recipient ∧
    0 < quittingTerminalSemanticDebt target who

/-- **Window-preserving reset from the defect reservoir.**

Every strict singleton-clock reservoir produces one literal fractional reset
inside the same finite window.  The reset has the exact semantic/law transfer
certificate, and it retains at least `1 - lambda` of the *whole* singleton
window even when its profitable row is outside the clock's temporal support.
The selected coordinate carries the full reservoir lower bound with only the
explicit finite averaging loss `cutoff * Fintype.card iota`.

This removes the label and state-provenance seams at finite depth.  What it
does not provide is a cutoff-independent lower bound on the selected one-row
gain: a diffuse defect reservoir may split among arbitrarily many dates. -/
theorem exists_singletonClock_windowPreservingPartialReset
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (minimum : QuittingTerminalSemanticPair iota)
    (profile : (quittingGame reward).BehaviorProfile)
    (owner : iota)
    (reference epsilon faceFloor clockMass : ℝ) (cutoff : ℕ) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hinitial : 0 ≤ quittingSpineDebtExcess reward profile reference 0)
    (hnear : ∀ time ≤ cutoff,
      quittingSpineDebtExcess reward profile reference time ≤ epsilon)
    (hfaceFloor : 0 ≤ faceFloor)
    (hface : ∀ time < cutoff, faceFloor ≤
      quittingTerminalSemanticComplementaryDebt
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward profile (time + 1)))
        owner)
    (hclock : clockMass ≤
      ∑ time ∈ Finset.range cutoff,
        quittingStageCoalitionMass reward profile time
          (quittingSingletonTerminal owner))
    (hstrict : epsilon < faceFloor * clockMass)
    (lambda : ℝ) (hlambda0 : 0 < lambda) (hlambda1 : lambda < 1) :
    ∃ stage < cutoff, ∃ who,
      faceFloor * clockMass - epsilon ≤
          (cutoff : ℝ) * (Fintype.card iota : ℝ) *
            (quittingLiveMass reward profile stage *
              quittingRootCoordinateNashDefect reward
                (quittingTerminalSemanticPair reward
                  (quittingAllContinueProfileSpine reward profile
                    (stage + 1))).1
                (quittingProfileLiveRoot reward profile stage) who) ∧
      IsQuittingStagePartialBestEndpointTransfer
          reward minimum profile stage who lambda hlambda0.le hlambda1.le ∧
      (1 - lambda) *
          (∑ time ∈ Finset.range cutoff,
            quittingStageCoalitionMass reward profile time
              (quittingSingletonTerminal owner)) ≤
        ∑ time ∈ Finset.range cutoff,
          quittingStageCoalitionMass reward
            (Function.update profile who
              (quittingStagePartialBestEndpointBehaviorDeviation
                reward profile who stage lambda hlambda0.le hlambda1.le))
            time (quittingSingletonTerminal owner) ∧
      0 < ∑ time ∈ Finset.range cutoff,
          quittingStageCoalitionMass reward
            (Function.update profile who
              (quittingStagePartialBestEndpointBehaviorDeviation
                reward profile who stage lambda hlambda0.le hlambda1.le))
            time (quittingSingletonTerminal owner) := by
  have hbudget := faceFloor_mul_clockMass_le_epsilon_add_defect
    reward profile owner reference epsilon faceFloor clockMass cutoff
      hM hreward hinitial hnear hfaceFloor hface hclock
  have hoccupation : 0 < ∑ time ∈ Finset.range cutoff,
      quittingLiveMass reward profile time *
        quittingSpineTotalNashDefect reward profile time := by
    linarith
  have hcutoff : 0 < cutoff := by
    by_contra hnot
    have hzero : cutoff = 0 := Nat.eq_zero_of_not_pos hnot
    subst cutoff
    simp at hoccupation
  have hrange : (Finset.range cutoff).Nonempty :=
    ⟨0, Finset.mem_range.mpr hcutoff⟩
  obtain ⟨stage, hstage, hstageAverage⟩ :=
    QuittingMarkedFencePacket.exists_sum_le_card_mul
      (Finset.range cutoff) hrange
      (fun time => quittingLiveMass reward profile time *
        quittingSpineTotalNashDefect reward profile time)
  have htimeBound :
      (∑ time ∈ Finset.range cutoff,
          quittingLiveMass reward profile time *
            quittingSpineTotalNashDefect reward profile time) ≤
        (cutoff : ℝ) *
          (quittingLiveMass reward profile stage *
            quittingSpineTotalNashDefect reward profile stage) := by
    simpa only [Finset.card_range] using hstageAverage
  have hstageDefect : 0 < quittingLiveMass reward profile stage *
      quittingSpineTotalNashDefect reward profile stage := by
    have hcutoffNonneg : 0 ≤ (cutoff : ℝ) := by positivity
    by_contra hnot
    have hnonpos : quittingLiveMass reward profile stage *
        quittingSpineTotalNashDefect reward profile stage ≤ 0 :=
      le_of_not_gt hnot
    nlinarith
  obtain ⟨who, hcoordinateBound, hreset⟩ :=
    exists_stagePartialBestEndpoint_transfer_of_liveTotalDefect_pos
      reward minimum profile stage hM hreward hminimum hstageDefect
        lambda hlambda0 hlambda1
  have hreservoir : faceFloor * clockMass - epsilon ≤
      ∑ time ∈ Finset.range cutoff,
        quittingLiveMass reward profile time *
          quittingSpineTotalNashDefect reward profile time := by
    linarith
  have hcutoffNonneg : 0 ≤ (cutoff : ℝ) := by positivity
  have hquantitative : faceFloor * clockMass - epsilon ≤
      (cutoff : ℝ) * (Fintype.card iota : ℝ) *
        (quittingLiveMass reward profile stage *
          quittingRootCoordinateNashDefect reward
            (quittingTerminalSemanticPair reward
              (quittingAllContinueProfileSpine reward profile
                (stage + 1))).1
            (quittingProfileLiveRoot reward profile stage) who) := by
    calc
      faceFloor * clockMass - epsilon ≤
          ∑ time ∈ Finset.range cutoff,
            quittingLiveMass reward profile time *
              quittingSpineTotalNashDefect reward profile time := hreservoir
      _ ≤ (cutoff : ℝ) *
          (quittingLiveMass reward profile stage *
            quittingSpineTotalNashDefect reward profile stage) := htimeBound
      _ ≤ (cutoff : ℝ) * ((Fintype.card iota : ℝ) *
          (quittingLiveMass reward profile stage *
            quittingRootCoordinateNashDefect reward
              (quittingTerminalSemanticPair reward
                (quittingAllContinueProfileSpine reward profile
                  (stage + 1))).1
              (quittingProfileLiveRoot reward profile stage) who)) :=
        mul_le_mul_of_nonneg_left hcoordinateBound hcutoffNonneg
      _ = _ := by ring
  have hcertificate : IsQuittingStagePartialBestEndpointTransfer
      reward minimum profile stage who lambda hlambda0.le hlambda1.le := by
    simpa only [IsQuittingStagePartialBestEndpointTransfer] using hreset
  have hretention :=
    one_sub_mul_sum_stageCoalitionMass_le_stagePartialBestEndpoint
      reward profile who stage cutoff (quittingSingletonTerminal owner)
        lambda hlambda0.le hlambda1.le
  have hepsilon : 0 ≤ epsilon :=
    hinitial.trans (hnear 0 (Nat.zero_le cutoff))
  have hproduct : 0 < faceFloor * clockMass := hstrict.trans_le' hepsilon
  have hclockMassPos : 0 < clockMass := by
    rcases mul_pos_iff.mp hproduct with hpositive | hnegative
    · exact hpositive.2
    · exact (not_lt_of_ge hfaceFloor hnegative.1).elim
  have holdWindow : 0 < ∑ time ∈ Finset.range cutoff,
      quittingStageCoalitionMass reward profile time
        (quittingSingletonTerminal owner) := hclockMassPos.trans_le hclock
  have hfactor : 0 < 1 - lambda := sub_pos.mpr hlambda1
  have htargetWindow : 0 < ∑ time ∈ Finset.range cutoff,
      quittingStageCoalitionMass reward
        (Function.update profile who
          (quittingStagePartialBestEndpointBehaviorDeviation
            reward profile who stage lambda hlambda0.le hlambda1.le))
        time (quittingSingletonTerminal owner) :=
    (mul_pos hfactor holdWindow).trans_le hretention
  exact ⟨stage, Finset.mem_range.mp hstage, who,
    hquantitative, hcertificate, hretention, htargetWindow⟩

/-- Game-facing capstone: a strict singleton-clock defect reservoir produces
either a literal profitable, state-matched endpoint reset routing the clock
cylinder, or an explicit positive defect atom outside the clock's temporal
support. -/
theorem exists_singletonClock_routedReset_or_offClockLeak
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile)
    (owner : iota)
    (reference epsilon faceFloor clockMass : ℝ) (cutoff : ℕ) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hinitial : 0 ≤ quittingSpineDebtExcess reward profile reference 0)
    (hnear : ∀ time ≤ cutoff,
      quittingSpineDebtExcess reward profile reference time ≤ epsilon)
    (hfaceFloor : 0 ≤ faceFloor)
    (hface : ∀ time < cutoff, faceFloor ≤
      quittingTerminalSemanticComplementaryDebt
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward profile (time + 1)))
        owner)
    (hclock : clockMass ≤
      ∑ time ∈ Finset.range cutoff,
        quittingStageCoalitionMass reward profile time
          (quittingSingletonTerminal owner))
    (hstrict : epsilon < faceFloor * clockMass) :
    (∃ time < cutoff, ∃ who,
      let tail := quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward profile (time + 1))
      let root := quittingProfileLiveRoot reward profile time
      let action := quittingRootBestEndpointAction reward tail.1 root who
      let routed := quittingPureEndpointRoutedCoalition {owner} who action
      0 < quittingStageCoalitionMass reward profile time
          (quittingSingletonTerminal owner) ∧
        0 < quittingRootCoordinateNashDefect reward tail.1 root who ∧
        quittingTerminalPayoff reward
              (Function.update profile who
                (quittingStagePureEndpointBehaviorDeviation
                  reward profile who time action)) who -
            quittingTerminalPayoff reward profile who =
              quittingLiveMass reward profile time *
                quittingRootCoordinateNashDefect reward tail.1 root who ∧
        0 < quittingTerminalPayoff reward
              (Function.update profile who
                (quittingStagePureEndpointBehaviorDeviation
                  reward profile who time action)) who -
            quittingTerminalPayoff reward profile who ∧
        0 < quittingRootCoalitionMass
          (Function.update root who (PMF.pure action)) routed ∧
        quittingRootCoalitionMass root {owner} ≤
          quittingRootCoalitionMass
            (Function.update root who (PMF.pure action)) routed) ∨
      ∃ time < cutoff,
        quittingStageCoalitionMass reward profile time
            (quittingSingletonTerminal owner) = 0 ∧
          0 < quittingLiveMass reward profile time *
            quittingSpineTotalNashDefect reward profile time := by
  rcases exists_singletonClock_defectOverlap_or_offClockLeak
      reward profile owner reference epsilon faceFloor clockMass cutoff
      hM hreward hinitial hnear hfaceFloor hface hclock hstrict with
    hoverlap | hleak
  · left
    obtain ⟨time, htime, hstage, hdefect⟩ := hoverlap
    obtain ⟨who, hwho⟩ :=
      exists_stageBestEndpointDeviation_singletonRouting_of_totalDefect_pos
        reward profile owner time hstage hdefect
    refine ⟨time, htime, who, ?_⟩
    dsimp only at hwho ⊢
    exact ⟨hstage, hwho.1, hwho.2.1, hwho.2.2.1,
      hwho.2.2.2.1, hwho.2.2.2.2.1⟩
  · exact Or.inr hleak

end GameTheory
