/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticLawCarrierCausalization
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauDefectStratification
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStrictTailEscapeReturn

/-!
# Causal collision rows: escape or a legal endpoint deviation

Moving the prefix/suffix cut to an actual collision row does not make that
row exact Nash.  Exact predecessor existence never fails.  The useful
same-profile dispatch is instead quantitative: a persistent collision is
paid either by escape of its own shifted tail from the minimum-debt fiber or
by a local Nash defect.  In the latter case a player-average selection turns
the defect into a legal reached-row best-endpoint deviation and routes the
marked coalition without losing root mass.

The escape branch records the exact cap--Nash return account for every cap
root selected at that same shifted tail.  It does not assert that such a root
spends enough of the escape to return; the all-Continue stall remains the
sharp obstruction.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- **Causal collision Nash dispatch.**

For one actual collision row of mass at least `lower` over a positive global
minimum, either its own shifted tail pays at least half of the collision
charge as debt escape, with the exact cap--Nash return account available at
that tail, or one player carries at least the player-average share of the
remaining local defect.  The latter share is realized by one legal unilateral
behavioral deviation on the same profile and row.  Its pure endpoint routes
the displayed coalition through one Boolean-cube edge without losing the
original quantitative root mass.

No root, cap, tail, or coalition in the conclusion is independently chosen.
-/
theorem causalCollision_tailEscape_or_quantitativeBestEndpoint
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (terminal : {S : Finset ι // S.Nonempty})
    (lower : ℝ) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ outcome player, |reward outcome player| ≤ M)
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumDebt : 0 < quittingTerminalSemanticDebtSum minimum)
    (hcollision : 1 < terminal.val.card)
    (hlower : 0 < lower)
    (hmass : lower ≤
      quittingStageCoalitionMass reward profile stage terminal) :
    let tail := quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (stage + 1))
    let root := quittingProfileLiveRoot reward profile stage
    (lower * quittingTerminalSemanticDebtSum minimum / 2 ≤
          quittingTerminalSemanticDebtSum tail -
            quittingTerminalSemanticDebtSum minimum ∧
        ∀ capRoot : ι → PMF Bool,
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
        lower * quittingTerminalSemanticDebtSum minimum / 2 ≤
          (Fintype.card ι : ℝ) *
            quittingRootCoordinateNashDefect reward tail.1 root who ∧
        let action := quittingRootBestEndpointAction reward tail.1 root who
        let routed := quittingPureEndpointRoutedCoalition terminal.val who action
        let target := Function.update profile who
          (quittingStagePureEndpointBehaviorDeviation
            reward profile who stage action)
        quittingTerminalPayoff reward target who -
              quittingTerminalPayoff reward profile who =
            quittingLiveMass reward profile stage *
              quittingRootCoordinateNashDefect reward tail.1 root who ∧
          0 < quittingTerminalPayoff reward target who -
              quittingTerminalPayoff reward profile who ∧
          lower ≤ quittingRootCoalitionMass
            (Function.update root who (PMF.pure action)) routed ∧
          ((who ∈ terminal.val ∧ action = true ∧ routed = terminal.val) ∨
            (who ∈ terminal.val ∧ action = false ∧
              routed = terminal.val.erase who) ∨
            (who ∉ terminal.val ∧ action = true ∧
              routed = insert who terminal.val) ∨
            (who ∉ terminal.val ∧ action = false ∧
              routed = terminal.val)) := by
  dsimp only
  let tail := quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward profile (stage + 1))
  let root := quittingProfileLiveRoot reward profile stage
  have hsplit := tailExcess_or_totalNashDefect_of_persistent_collision
    reward minimum profile stage terminal lower hM hreward hminimumCarrier
      hminimum hcollision hmass
  rcases hsplit with hescape | hdefect
  · left
    refine ⟨by simpa only [quittingSpineDebtExcess, tail] using hescape, ?_⟩
    intro capRoot hnash
    simpa only [tail] using capNashPrefix_tailEscape_exact_account
      (reward := reward) minimum tail capRoot hM hreward hminimum
        (quittingTerminalSemanticPair_mem_carrier reward _) hnash
  · right
    have htotalPos : 0 < quittingSpineTotalNashDefect reward profile stage :=
      lt_of_lt_of_le (div_pos (mul_pos hlower hminimumDebt) (by norm_num)) hdefect
    let defect : ι → ℝ := fun who ↦
      quittingRootCoordinateNashDefect reward tail.1 root who
    obtain ⟨who, _hwho, hmax⟩ := Finset.exists_max_image
      (Finset.univ : Finset ι) defect Finset.univ_nonempty
    have hsumLe : quittingSpineTotalNashDefect reward profile stage ≤
        (Fintype.card ι : ℝ) * defect who := by
      have hsum := (Finset.univ : Finset ι).sum_le_card_nsmul
        defect (defect who) (fun player hplayer ↦ hmax player hplayer)
      simpa only [quittingSpineTotalNashDefect,
        quittingRootTotalNashDefect, tail, root, defect, nsmul_eq_mul,
        Finset.card_univ] using hsum
    have hcoordinate : lower * quittingTerminalSemanticDebtSum minimum / 2 ≤
        (Fintype.card ι : ℝ) *
          quittingRootCoordinateNashDefect reward tail.1 root who :=
      hdefect.trans hsumLe
    have hcoordinatePos : 0 <
        quittingRootCoordinateNashDefect reward tail.1 root who := by
      have hcardPos : 0 < (Fintype.card ι : ℝ) := by positivity
      have hthresholdPos : 0 <
          lower * quittingTerminalSemanticDebtSum minimum / 2 := by positivity
      nlinarith
    have hlive : 0 < quittingLiveMass reward profile stage :=
      (hlower.trans_le hmass).trans_le
        (quittingStageCoalitionMass_le_liveMass
          reward profile stage terminal)
    have hrootMassLower : lower ≤ quittingRootCoalitionMass root terminal.val := by
      have hrootNonneg :=
        MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg root terminal.val
      have hliveLe := quittingLiveMass_le_one reward profile stage
      have hstageLe : quittingStageCoalitionMass reward profile stage terminal ≤
          quittingRootCoalitionMass root terminal.val := by
        rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass]
        exact mul_le_of_le_one_left hrootNonneg hliveLe
      exact hmass.trans hstageLe
    have hrouting :=
      quittingTerminalPayoff_stageBestEndpointDeviation_markedRouting
        reward profile who stage terminal.val hlive
          (hlower.trans_le hrootMassLower) hcoordinatePos
    refine ⟨who, hcoordinate, ?_⟩
    dsimp only [tail, root] at hrouting ⊢
    refine ⟨hrouting.1, hrouting.2.1, ?_, hrouting.2.2.2.2⟩
    exact hrootMassLower.trans hrouting.2.2.2.1

end GameTheory
