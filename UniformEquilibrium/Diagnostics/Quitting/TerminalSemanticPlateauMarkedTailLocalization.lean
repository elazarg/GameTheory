/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauDefectTelescope
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauMarkedVariational

/-!
# Localizing a persistent marked collision row

A profitable collision atom selected from a pure-time best-response reset
belongs to one actual profile and one actual stop row.  Compactness by itself
does not put the shifted tail of that row on the minimum-total-debt fiber.
This module records the exact alternative which is available without changing
the profile or the row.

At every collision row,

`stage mass * minimum debt <= tail excess + total local Nash defect`.

Thus a persistent collision above a positive minimum either escapes the
minimum fiber through its own shifted tail, or leaves a uniformly positive
local Nash-defect charge.  The pure-time reset makes the marked coordinate's
defect vanish, so on a minimum-fiber cluster the charge is carried by other
players.  A second theorem retains the full stopped defect/excess account and
shows that the same collision forces a positive budget on its actual prefix.

No independently selected tail or Nash root occurs below.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability Math.PMFProduct
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Same-row minimum-fiber charge -/

/-- A collision atom at one actual row is paid by the excess of that row's
own shifted terminal-semantic tail over a global minimum, or by the total
Nash defect of that row's own live root. -/
theorem quittingStageCollisionMass_mul_minimumDebt_le_tailExcess_add_totalNashDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hcollision : 1 < terminal.val.card) :
    quittingStageCoalitionMass reward profile time terminal *
        quittingTerminalSemanticDebtSum minimum ≤
      quittingSpineDebtExcess reward profile
          (quittingTerminalSemanticDebtSum minimum) (time + 1) +
        quittingSpineTotalNashDefect reward profile time := by
  let tail := quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward profile (time + 1))
  let charge := quittingSpineOpponentAbsorptionDebtCharge reward profile time
  have htailCarrier : tail ∈ quittingTerminalSemanticCarrier reward :=
    quittingTerminalSemanticPair_mem_carrier reward _
  have htailDebt : ∀ who, 0 ≤ quittingTerminalSemanticDebt tail who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hM hreward htailCarrier
  have htailMin : quittingTerminalSemanticDebtSum minimum ≤
      quittingTerminalSemanticDebtSum tail :=
    hminimum tail htailCarrier
  have hstageNonneg : 0 ≤
      quittingStageCoalitionMass reward profile time terminal :=
    quittingStageCoalitionMass_nonneg reward profile time terminal
  have hminimumToTail :
      quittingStageCoalitionMass reward profile time terminal *
          quittingTerminalSemanticDebtSum minimum ≤
        quittingStageCoalitionMass reward profile time terminal *
          quittingTerminalSemanticDebtSum tail :=
    mul_le_mul_of_nonneg_left htailMin hstageNonneg
  have hstageCharge :
      quittingStageCoalitionMass reward profile time terminal *
          quittingTerminalSemanticDebtSum tail ≤
        quittingLiveMass reward profile time * charge := by
    simpa only [tail, charge] using
      quittingStageCoalitionMass_mul_tailDebtSum_le_liveMass_mul_charge
        reward profile time terminal hM hreward hcollision
  have hchargeNonneg : 0 ≤ charge := by
    unfold charge quittingSpineOpponentAbsorptionDebtCharge
    exact Finset.sum_nonneg fun who _ => mul_nonneg
      (quittingRootOpponentAbsorptionMass_nonneg
        (quittingProfileLiveRoot reward profile time) who)
      (htailDebt who)
  have hliveCharge : quittingLiveMass reward profile time * charge ≤ charge :=
    mul_le_of_le_one_left hchargeNonneg
      (quittingLiveMass_le_one reward profile time)
  have hcharge :=
    minimumTerminalSemantic_sum_opponentAbsorption_charge_le_excess_add_defect
      reward minimum tail (quittingProfileLiveRoot reward profile time)
        hM hreward hminimumCarrier hminimum htailCarrier
  have hcharge' : charge ≤
      quittingSpineDebtExcess reward profile
          (quittingTerminalSemanticDebtSum minimum) (time + 1) +
        quittingSpineTotalNashDefect reward profile time := by
    simpa only [charge, tail, quittingSpineOpponentAbsorptionDebtCharge,
      quittingSpineDebtExcess, quittingSpineTotalNashDefect] using hcharge
  exact hminimumToTail.trans (hstageCharge.trans (hliveCharge.trans hcharge'))

/-- A persistent collision at one row gives an explicit dichotomy: its own
shifted tail is at least `lower * D / 2` above the minimum fiber, or its own
live root has Nash defect at least `lower * D / 2`. -/
theorem tailExcess_or_totalNashDefect_of_persistent_collision
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) (lower : ℝ) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hcollision : 1 < terminal.val.card)
    (hmass : lower ≤ quittingStageCoalitionMass reward profile time terminal) :
    lower * quittingTerminalSemanticDebtSum minimum / 2 ≤
        quittingSpineDebtExcess reward profile
          (quittingTerminalSemanticDebtSum minimum) (time + 1) ∨
      lower * quittingTerminalSemanticDebtSum minimum / 2 ≤
        quittingSpineTotalNashDefect reward profile time := by
  have hminimumNonneg : 0 ≤ quittingTerminalSemanticDebtSum minimum := by
    unfold quittingTerminalSemanticDebtSum
    exact Finset.sum_nonneg fun who _ =>
      quittingTerminalSemanticDebt_nonneg_of_mem_carrier
        reward hM hreward hminimumCarrier who
  have hscaled : lower * quittingTerminalSemanticDebtSum minimum ≤
      quittingStageCoalitionMass reward profile time terminal *
        quittingTerminalSemanticDebtSum minimum :=
    mul_le_mul_of_nonneg_right hmass hminimumNonneg
  have hbudget := hscaled.trans
    (quittingStageCollisionMass_mul_minimumDebt_le_tailExcess_add_totalNashDefect
      reward minimum profile time terminal hM hreward hminimumCarrier hminimum
        hcollision)
  by_contra hnot
  push Not at hnot
  linarith

/-! ## The full stopped budget on the same marked profile -/

/-- The marked term at `stop` is one summand of the exact stopped
defect/excess telescope through `stop + 1`.  Therefore persistent collision
forces a positive amount of that *same profile's* endpoint, killed-excess,
or local-defect occupation budget. -/
theorem minimumDebt_mul_stageCollisionMass_le_stoppedDefectExcessBudget
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (profile : (quittingGame reward).BehaviorProfile) (stop : ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (_hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hcollision : 1 < terminal.val.card) :
    quittingStageCoalitionMass reward profile stop terminal *
        quittingTerminalSemanticDebtSum minimum ≤
      quittingLiveMass reward profile (stop + 1) *
          quittingSpineDebtExcess reward profile
            (quittingTerminalSemanticDebtSum minimum) (stop + 1) -
        quittingSpineDebtExcess reward profile
          (quittingTerminalSemanticDebtSum minimum) 0 +
      (∑ time ∈ Finset.range (stop + 1),
        (quittingLiveMass reward profile time -
            quittingLiveMass reward profile (time + 1)) *
          quittingSpineDebtExcess reward profile
            (quittingTerminalSemanticDebtSum minimum) (time + 1)) +
      ∑ time ∈ Finset.range (stop + 1),
        quittingLiveMass reward profile time *
          quittingSpineTotalNashDefect reward profile time := by
  let term : ℕ → ℝ := fun time =>
    quittingStageCoalitionMass reward profile time terminal *
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward profile (time + 1)))
  have htailMin : quittingTerminalSemanticDebtSum minimum ≤
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward profile (stop + 1))) :=
    hminimum _ (quittingTerminalSemanticPair_mem_carrier reward _)
  have hstageNonneg : 0 ≤
      quittingStageCoalitionMass reward profile stop terminal :=
    quittingStageCoalitionMass_nonneg reward profile stop terminal
  have hminTerm : quittingStageCoalitionMass reward profile stop terminal *
      quittingTerminalSemanticDebtSum minimum ≤ term stop := by
    exact mul_le_mul_of_nonneg_left htailMin hstageNonneg
  have htermNonneg : ∀ time, 0 ≤ term time := by
    intro time
    exact mul_nonneg
      (quittingStageCoalitionMass_nonneg reward profile time terminal)
      (by
        unfold quittingTerminalSemanticDebtSum
        exact Finset.sum_nonneg fun who _ =>
          quittingTerminalSemanticDebt_nonneg_of_mem_carrier
            reward hM hreward
              (quittingTerminalSemanticPair_mem_carrier reward _) who)
  have htermSum : term stop ≤
      ∑ time ∈ Finset.range (stop + 1), term time := by
    exact Finset.single_le_sum
      (fun time _ => htermNonneg time) (Finset.mem_range.mpr (by omega))
  have htelescope :=
    sum_stageCollisionMass_mul_tailDebtSum_le_stoppedDefectExcess
      reward profile terminal (quittingTerminalSemanticDebtSum minimum)
        (stop + 1) hM hreward hcollision
  exact hminTerm.trans (htermSum.trans (by simpa only [term] using htelescope))

/-! ## Compact localization of the actual marked rows -/

/-- **Marked-tail localization/defect alternative.**

Start with the actual pure-time reset profiles carrying one persistent
collision atom.  The selected finite stops have a subsequence whose *own*
shifted tails converge to a semantic-carrier point.  Either that cluster is
strictly above the minimum-total-debt fiber, or it lies on the fiber and a
uniformly positive local Nash-defect charge is carried by players other than
the reset player.

The latter charge is at least half of `lower * minimumDebt`; the marked
coordinate itself tends to zero by the reset law. -/
theorem exists_markedTailCluster_escape_or_otherNashDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (who : ι) (quitTime : ℕ → Option ℕ)
    (terminal : {S : Finset ι // S.Nonempty})
    (hmem : who ∈ terminal.val)
    {lower M : ℝ} (hlower : 0 < lower) (hM : 0 ≤ M)
    (hreward : ∀ outcome player, |reward outcome player| ≤ M)
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPositive : 0 < quittingTerminalSemanticDebtSum minimum)
    (hcollision : 1 < terminal.val.card)
    (hreset : Tendsto (fun n => quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (Function.update (profiles n) who
          (quittingPureTimeBehaviorStrategy reward who (quitTime n)))) who)
      atTop (𝓝 0))
    (hpersistent : ∀ᶠ n in atTop, lower ≤
      quittingTerminalOutcomeMass reward
        (Function.update (profiles n) who
          (quittingPureTimeBehaviorStrategy reward who (quitTime n)))
        (some terminal)) :
    ∃ (stop : ℕ → ℕ) (cluster : QuittingTerminalSemanticPair ι)
        (subseq : ℕ → ℕ),
      cluster ∈ quittingTerminalSemanticCarrier reward ∧
      StrictMono subseq ∧
      (∀ᶠ rank in atTop,
        quitTime (subseq rank) = some (stop (subseq rank))) ∧
      (∀ᶠ rank in atTop, lower ≤
        quittingStageCoalitionMass reward
          (Function.update (profiles (subseq rank)) who
            (quittingPureTimeBehaviorStrategy reward who
              (quitTime (subseq rank))))
          (stop (subseq rank)) terminal) ∧
      Tendsto (fun rank => quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward
            (Function.update (profiles (subseq rank)) who
              (quittingPureTimeBehaviorStrategy reward who
                (quitTime (subseq rank))))
            (stop (subseq rank) + 1)))
        atTop (𝓝 cluster) ∧
      Tendsto (fun rank =>
        let deviated := Function.update (profiles (subseq rank)) who
          (quittingPureTimeBehaviorStrategy reward who
            (quitTime (subseq rank)))
        quittingRootCoordinateNashDefect reward
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward deviated
              (stop (subseq rank) + 1))).1
          (quittingProfileLiveRoot reward deviated (stop (subseq rank))) who)
        atTop (𝓝 0) ∧
      (quittingTerminalSemanticDebtSum minimum <
          quittingTerminalSemanticDebtSum cluster ∨
        quittingTerminalSemanticDebtSum cluster =
            quittingTerminalSemanticDebtSum minimum ∧
          ∀ᶠ rank in atTop,
            lower * quittingTerminalSemanticDebtSum minimum / 2 ≤
              ∑ other ∈ Finset.univ.erase who,
                let deviated := Function.update (profiles (subseq rank)) who
                  (quittingPureTimeBehaviorStrategy reward who
                    (quitTime (subseq rank)))
                quittingRootCoordinateNashDefect reward
                  (quittingTerminalSemanticPair reward
                    (quittingAllContinueProfileSpine reward deviated
                      (stop (subseq rank) + 1))).1
                  (quittingProfileLiveRoot reward deviated
                    (stop (subseq rank))) other) := by
  obtain ⟨stop, hfinite, hstage, hmarkedDefect⟩ :=
    exists_stops_tendsto_coordinateNashDefect_zero_of_persistent_collision
      reward profiles who quitTime terminal hmem hlower hM hreward hreset
        hpersistent
  let deviated : ℕ → (quittingGame reward).BehaviorProfile := fun n =>
    Function.update (profiles n) who
      (quittingPureTimeBehaviorStrategy reward who (quitTime n))
  let tail : ℕ → QuittingTerminalSemanticPair ι := fun n =>
    quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward (deviated n) (stop n + 1))
  have htailMem : ∀ n, tail n ∈ quittingTerminalSemanticCarrier reward := by
    intro n
    exact quittingTerminalSemanticPair_mem_carrier reward _
  obtain ⟨cluster, hcluster, subseq, hsubseq, htailLimit⟩ :=
    (quittingTerminalSemanticCarrier_isCompact reward hM hreward).tendsto_subseq
      htailMem
  have hfiniteSub : ∀ᶠ rank in atTop,
      quitTime (subseq rank) = some (stop (subseq rank)) :=
    hsubseq.tendsto_atTop hfinite
  have hstageSub : ∀ᶠ rank in atTop, lower ≤
      quittingStageCoalitionMass reward (deviated (subseq rank))
        (stop (subseq rank)) terminal :=
    hsubseq.tendsto_atTop hstage
  have hmarkedSub : Tendsto (fun rank =>
      quittingRootCoordinateNashDefect reward
        (tail (subseq rank)).1
        (quittingProfileLiveRoot reward (deviated (subseq rank))
          (stop (subseq rank))) who) atTop (𝓝 0) :=
    hmarkedDefect.comp hsubseq.tendsto_atTop
  refine ⟨stop, cluster, subseq, hcluster, hsubseq, hfiniteSub, ?_, ?_, ?_, ?_⟩
  · simpa only [deviated] using hstageSub
  · change Tendsto (tail ∘ subseq) atTop (𝓝 cluster)
    exact htailLimit
  · simpa only [tail, deviated] using hmarkedSub
  have hclusterMin : quittingTerminalSemanticDebtSum minimum ≤
      quittingTerminalSemanticDebtSum cluster := hminimum cluster hcluster
  rcases hclusterMin.lt_or_eq with hescape | hfiber
  · exact Or.inl hescape
  · refine Or.inr ⟨hfiber.symm, ?_⟩
    let excess : ℕ → ℝ := fun rank =>
      quittingSpineDebtExcess reward (deviated (subseq rank))
        (quittingTerminalSemanticDebtSum minimum) (stop (subseq rank) + 1)
    let markedDefect : ℕ → ℝ := fun rank =>
      quittingRootCoordinateNashDefect reward
        (tail (subseq rank)).1
        (quittingProfileLiveRoot reward (deviated (subseq rank))
          (stop (subseq rank))) who
    let otherDefect : ℕ → ℝ := fun rank =>
      ∑ other ∈ Finset.univ.erase who,
        quittingRootCoordinateNashDefect reward
          (tail (subseq rank)).1
          (quittingProfileLiveRoot reward (deviated (subseq rank))
            (stop (subseq rank))) other
    have hdebtLimit : Tendsto
        (fun rank => quittingTerminalSemanticDebtSum (tail (subseq rank)))
        atTop (𝓝 (quittingTerminalSemanticDebtSum cluster)) :=
      continuous_quittingTerminalSemanticDebtSum.continuousAt.tendsto.comp
        htailLimit
    have hexcess : Tendsto excess atTop (𝓝 0) := by
      have hsub := hdebtLimit.sub_const
        (quittingTerminalSemanticDebtSum minimum)
      rw [← hfiber] at hsub
      simpa only [excess, quittingSpineDebtExcess, tail, sub_self] using hsub
    have hmarked : Tendsto markedDefect atTop (𝓝 0) := by
      simpa only [markedDefect] using hmarkedSub
    have hchargePositive :
        0 < lower * quittingTerminalSemanticDebtSum minimum :=
      mul_pos hlower hminimumPositive
    have hexcessSmall : ∀ᶠ rank in atTop,
        excess rank < lower * quittingTerminalSemanticDebtSum minimum / 4 :=
      hexcess.eventually (Iio_mem_nhds (by linarith))
    have hmarkedSmall : ∀ᶠ rank in atTop,
        markedDefect rank <
          lower * quittingTerminalSemanticDebtSum minimum / 4 :=
      hmarked.eventually (Iio_mem_nhds (by linarith))
    have hother : ∀ᶠ rank in atTop,
        lower * quittingTerminalSemanticDebtSum minimum / 2 ≤
          otherDefect rank := by
      filter_upwards [hstageSub, hexcessSmall, hmarkedSmall] with rank
          hmass hexcessBound hmarkedBound
      have hrow :=
        quittingStageCollisionMass_mul_minimumDebt_le_tailExcess_add_totalNashDefect
          reward minimum (deviated (subseq rank)) (stop (subseq rank))
            terminal hM hreward hminimumCarrier hminimum hcollision
      have hscaled : lower * quittingTerminalSemanticDebtSum minimum ≤
          quittingStageCoalitionMass reward (deviated (subseq rank))
              (stop (subseq rank)) terminal *
            quittingTerminalSemanticDebtSum minimum :=
        mul_le_mul_of_nonneg_right hmass hminimumPositive.le
      have hbudget : lower * quittingTerminalSemanticDebtSum minimum ≤
          excess rank +
            quittingSpineTotalNashDefect reward (deviated (subseq rank))
              (stop (subseq rank)) := by
        exact hscaled.trans (by simpa only [excess] using hrow)
      have hsplit :
          quittingSpineTotalNashDefect reward (deviated (subseq rank))
              (stop (subseq rank)) =
            otherDefect rank + markedDefect rank := by
        unfold quittingSpineTotalNashDefect quittingRootTotalNashDefect
        rw [Finset.sum_erase_add _ _ (Finset.mem_univ who)]
      rw [hsplit] at hbudget
      linarith
    simpa only [otherDefect, tail, deviated] using hother

end GameTheory
