/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticLawCarrierCausalNashDispatch

/-!
# Near-minimum transfer forced by a causal collision gain

The profitable branch of the causal-collision dispatch is not a total-debt
descent at a near-minimum source.  The resetting player's exact payoff gain
is an exact loss of that player's behavioral best-response debt.  Global
minimality therefore forces all but the source excess into the other debt
coordinates.

This file keeps the two co-realized labels separate.  The Boolean-cube edge
routes the marked terminal coalition, while the selected debt recipient is
obtained from semantic transfer.  No theorem identifies that recipient with
a member, joiner, or leaver of the routed coalition.  That missing incidence
match is precisely what the punishment and atomic consumers require.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {iota : Type} [Fintype iota] [DecidableEq iota] [Nonempty iota]

/-- **Causal collision dispatch with a quantitative near-minimum transfer.**

Assume that the literal profile carrying the causal collision is within
`epsilon` of the global minimum total debt.  In the local-defect branch, the
same legal best-endpoint deviation has all of the following properties:

* its global payoff gain has a uniform lower bound on the collision scale;
* the mover's semantic debt falls by exactly that gain;
* at least `gain - epsilon` is transferred to the other coordinates;
* when `epsilon < gain`, one actual distinct recipient gains positive debt;
* the original collision is routed through the corresponding cube edge
  without losing its quantitative root mass.

The recipient and routed-coalition labels are deliberately not matched.
-/
theorem causalCollision_tailEscape_or_quantitativeNearMinimumTransfer
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
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
        let targetProfile := Function.update profile who
          (quittingStagePureEndpointBehaviorDeviation
            reward profile who stage action)
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
          (epsilon < gain →
            ∃ recipient ∈ Finset.univ.erase who,
              0 < quittingTerminalSemanticDebtChange source target recipient) ∧
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
  have hdispatch := causalCollision_tailEscape_or_quantitativeBestEndpoint
    reward minimum profile stage terminal lower hM hreward hminimumCarrier
      hminimum hminimumDebt hcollision hlower hmass
  dsimp only [tail] at hdispatch ⊢
  rcases hdispatch with hescape | hgain
  · exact Or.inl hescape
  · right
    rcases hgain with ⟨who, hcoordinate, hpayoff, hpositive,
      hrouted, horientation⟩
    let root := quittingProfileLiveRoot reward profile stage
    let action := quittingRootBestEndpointAction reward tail.1 root who
    let targetProfile := Function.update profile who
      (quittingStagePureEndpointBehaviorDeviation
        reward profile who stage action)
    let source := quittingTerminalSemanticPair reward profile
    let target := quittingTerminalSemanticPair reward targetProfile
    let gain := quittingTerminalPayoff reward targetProfile who -
      quittingTerminalPayoff reward profile who
    have hlive : lower ≤ quittingLiveMass reward profile stage :=
      hmass.trans (quittingStageCoalitionMass_le_liveMass
        reward profile stage terminal)
    have hgainFormula : gain = quittingLiveMass reward profile stage *
        quittingRootCoordinateNashDefect reward tail.1 root who := by
      simpa only [root, action, targetProfile, gain] using hpayoff
    have hdefectNonneg : 0 ≤ quittingRootCoordinateNashDefect
        reward tail.1 root who :=
      quittingRootCoordinateNashDefect_nonneg reward tail.1 root who
    have hquantitative : lower ^ 2 *
          quittingTerminalSemanticDebtSum minimum / 2 ≤
        (Fintype.card iota : ℝ) * gain := by
      have hscaled := mul_le_mul_of_nonneg_right hlive hdefectNonneg
      rw [← hgainFormula] at hscaled
      have hmul := mul_le_mul_of_nonneg_left hcoordinate hlower.le
      nlinarith [hscaled, hmul]
    have htargetCarrier : target ∈
        quittingTerminalSemanticCarrier reward := by
      exact quittingTerminalSemanticPair_mem_carrier reward targetProfile
    have henvelope : quittingContinuationBestResponseValue reward
        targetProfile who =
      quittingContinuationBestResponseValue reward profile who := by
      exact quittingContinuationBestResponseValue_update_self
        reward profile who _
    have hmoverDebt : quittingTerminalSemanticDebt target who =
        quittingTerminalSemanticDebt source who - gain := by
      unfold quittingTerminalSemanticDebt
      dsimp only [target, source]
      change quittingContinuationBestResponseValue reward targetProfile who -
          quittingTerminalPayoff reward targetProfile who =
        quittingContinuationBestResponseValue reward profile who -
          quittingTerminalPayoff reward profile who - gain
      rw [henvelope]
      dsimp only [gain, targetProfile]
      ring
    have htotalLower : quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum target :=
      hminimum target htargetCarrier
    have hotherExact :
        (∑ recipient ∈ Finset.univ.erase who,
            quittingTerminalSemanticDebtChange source target recipient) =
          (quittingTerminalSemanticDebtSum target -
            quittingTerminalSemanticDebtSum source) + gain := by
      unfold quittingTerminalSemanticDebtChange
      rw [Finset.sum_sub_distrib]
      have htargetSplit := Finset.sum_erase_add Finset.univ
        (fun player ↦ quittingTerminalSemanticDebt target player)
        (Finset.mem_univ who)
      have hsourceSplit := Finset.sum_erase_add Finset.univ
        (fun player ↦ quittingTerminalSemanticDebt source player)
        (Finset.mem_univ who)
      change (∑ recipient ∈ Finset.univ.erase who,
          quittingTerminalSemanticDebt target recipient) +
            quittingTerminalSemanticDebt target who =
          quittingTerminalSemanticDebtSum target at htargetSplit
      change (∑ recipient ∈ Finset.univ.erase who,
          quittingTerminalSemanticDebt source recipient) +
            quittingTerminalSemanticDebt source who =
          quittingTerminalSemanticDebtSum source at hsourceSplit
      rw [hmoverDebt] at htargetSplit
      linarith
    have htransfer : gain - epsilon ≤
        ∑ recipient ∈ Finset.univ.erase who,
          quittingTerminalSemanticDebtChange source target recipient := by
      rw [hotherExact]
      linarith
    have hrecipient : epsilon < gain →
        ∃ recipient ∈ Finset.univ.erase who,
          0 < quittingTerminalSemanticDebtChange source target recipient := by
      intro heps
      have hsumPos : 0 < ∑ recipient ∈ Finset.univ.erase who,
          quittingTerminalSemanticDebtChange source target recipient :=
        (sub_pos.mpr heps).trans_le htransfer
      have hzero : (∑ _recipient ∈ Finset.univ.erase who, (0 : ℝ)) = 0 := by
        simp
      obtain ⟨recipient, hrecipient, hpositiveRecipient⟩ :=
        Finset.exists_lt_of_sum_lt
          (show (∑ _recipient ∈ Finset.univ.erase who, (0 : ℝ)) <
              ∑ recipient ∈ Finset.univ.erase who,
                quittingTerminalSemanticDebtChange source target recipient by
            simpa only [hzero] using hsumPos)
      exact ⟨recipient, hrecipient, hpositiveRecipient⟩
    refine ⟨who, hpositive, hquantitative, htargetCarrier,
      hmoverDebt, htransfer, ?_, hrouted, horientation⟩
    exact hrecipient

end GameTheory
