/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticCausalCollisionMinimumTransfer
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPositiveSlopeAtom

/-!
# Compile an unmatched endpoint-debt recipient into a literal atom

A positive debt recipient on a unilateral endpoint edge need not belong to a
previously marked coalition.  Matching those labels is unnecessary for the
existing positive-slope decoder: realize the endpoint as the unit-weight
complete stopping-law mixture and decode the recipient on that same edge.

The output is either a prescribed payoff-difference atom or a same-deviation
rectangle atom.  Thus semantic transfer advances to a literal terminal atom
without any recurrence or incidence assumption.  The rectangle alternative
still has the known counterfactual-externality seam.
-/

noncomputable section

namespace GameTheory

open Set

variable {iota : Type} [Fintype iota] [DecidableEq iota]

/-- At unit weight, a complete stopping-law mixture has exactly the endpoint
best-response envelope, including for players other than the mover. -/
theorem quittingContinuationBestResponseValue_stoppingLawMixture_one_eq
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : iota)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    quittingContinuationBestResponseValue reward
        (Function.update profile mover
          (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
            1 zero_le_one le_rfl)) observer =
      quittingContinuationBestResponseValue reward
        (Function.update profile mover target) observer := by
  let mixedStrategy := quittingStoppingLawMixtureBehaviorStrategy reward mover
    source target 1 zero_le_one le_rfl
  let mixed := Function.update profile mover mixedStrategy
  let endpoint := Function.update profile mover target
  apply le_antisymm
  · have hconvex :=
      quittingContinuationBestResponseValue_stoppingLawMixture_le
        reward profile mover observer source target 1 zero_le_one le_rfl
          hM hreward
    norm_num at hconvex
    exact hconvex
  · by_cases hsame : observer = mover
    · subst observer
      rw [quittingContinuationBestResponseValue_update_self,
        quittingContinuationBestResponseValue_update_self]
    · unfold quittingContinuationBestResponseValue
      apply csSup_le
      · exact Set.range_nonempty _
      · rintro payoff ⟨deviation, rfl⟩
        have haffine := quittingTerminalPayoff_stoppingLawMixture_eq
          reward (Function.update profile observer deviation) mover observer
            source target 1 zero_le_one le_rfl
        have hcommuteMixed :
            Function.update (Function.update profile observer deviation) mover
                mixedStrategy = Function.update mixed observer deviation :=
          Function.update_comm hsame deviation mixedStrategy profile
        have hcommuteTarget :
            Function.update (Function.update profile observer deviation) mover
                target = Function.update endpoint observer deviation :=
          Function.update_comm hsame deviation target profile
        rw [hcommuteMixed, hcommuteTarget] at haffine
        have heq : quittingTerminalPayoff reward
              (Function.update mixed observer deviation) observer =
            quittingTerminalPayoff reward
              (Function.update endpoint observer deviation) observer := by
          norm_num at haffine
          exact haffine
        have hbound :=
          quittingTerminalPayoff_update_le_continuationBestResponseValue
            reward mixed observer deviation hM hreward
        exact heq.symm.trans_le hbound

/-- At unit weight, the full terminal semantic pair of a complete
stopping-law mixture is exactly its endpoint semantic pair. -/
theorem quittingTerminalSemanticPair_stoppingLawMixture_one_eq
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover : iota)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    quittingTerminalSemanticPair reward
        (Function.update profile mover
          (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
            1 zero_le_one le_rfl)) =
      quittingTerminalSemanticPair reward
        (Function.update profile mover target) := by
  apply Prod.ext
  · funext observer
    change quittingTerminalPayoff reward
        (Function.update profile mover
          (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
            1 zero_le_one le_rfl)) observer =
      quittingTerminalPayoff reward (Function.update profile mover target)
        observer
    have hpayoff := quittingTerminalPayoff_stoppingLawMixture_eq
      reward profile mover observer source target 1 zero_le_one le_rfl
    norm_num at hpayoff
    exact hpayoff
  · funext observer
    exact quittingContinuationBestResponseValue_stoppingLawMixture_one_eq
      reward profile mover observer source target hM hreward

/-- Literal atom output attached to one positive endpoint-debt recipient.
The terminal label is selected by the payoff decoder, not inherited from an
independently marked collision. -/
def HasQuittingEndpointDebtRecipientAtom
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover recipient : iota)
    (target : (quittingGame reward).BehaviorStrategy mover) : Prop :=
  let endpoint := Function.update profile mover target
  let charge := quittingTerminalSemanticDebtChange
    (quittingTerminalSemanticPair reward profile)
    (quittingTerminalSemanticPair reward endpoint) recipient
  0 < charge ∧
    ((∃ terminal : {S : Finset iota // S.Nonempty},
        charge / 2 ≤
          (Fintype.card (QuittingTerminalOutcome iota) : ℝ) *
            quittingTerminalPayoffDifferenceAtom reward profile endpoint
              recipient (some terminal)) ∨
      ∃ deviation : (quittingGame reward).BehaviorStrategy recipient,
        ∃ terminal : {S : Finset iota // S.Nonempty},
          charge / 4 ≤
            (Fintype.card (QuittingTerminalOutcome iota) : ℝ) *
              quittingTerminalPayoffDifferenceAtom reward
                (Function.update endpoint recipient deviation)
                (Function.update profile recipient deviation) recipient
                (some terminal))

/-- Any positive recipient on a unilateral endpoint edge enters the existing
positive-slope atom decoder, with no incidence or label-match hypothesis. -/
theorem hasQuittingEndpointDebtRecipientAtom_of_pos
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover recipient : iota)
    (target : (quittingGame reward).BehaviorStrategy mover)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpositive : 0 < quittingTerminalSemanticDebtChange
      (quittingTerminalSemanticPair reward profile)
      (quittingTerminalSemanticPair reward
        (Function.update profile mover target)) recipient) :
    HasQuittingEndpointDebtRecipientAtom reward profile mover recipient
      target := by
  let mixed := Function.update profile mover
    (quittingStoppingLawMixtureBehaviorStrategy reward mover (profile mover)
      target 1 zero_le_one le_rfl)
  have hpair := quittingTerminalSemanticPair_stoppingLawMixture_one_eq
    reward profile mover (profile mover) target hM hreward
  have hslope : 1 * quittingTerminalSemanticDebtChange
        (quittingTerminalSemanticPair reward profile)
        (quittingTerminalSemanticPair reward
          (Function.update profile mover target)) recipient ≤
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward mixed) recipient -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) recipient := by
    rw [hpair]
    simp [quittingTerminalSemanticDebtChange]
  have hdecoded :=
    exists_prescribedAtom_or_deviationRectangleAtom_of_stoppingLawDebtSlope
      reward profile mover recipient target 1
        (quittingTerminalSemanticDebtChange
          (quittingTerminalSemanticPair reward profile)
          (quittingTerminalSemanticPair reward
            (Function.update profile mover target)) recipient)
        zero_lt_one le_rfl hpositive hM hreward
        (by simpa only [mixed, one_mul] using hslope)
  exact ⟨hpositive, hdecoded⟩

/-- A positive aggregate transfer from the mover can be compiled immediately:
one distinct positive recipient is selected and attached to its own literal
payoff atom or rectangle on the same endpoint edge. -/
theorem exists_endpointDebtRecipientAtom_of_positiveAggregateTransfer
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover : iota) (target : (quittingGame reward).BehaviorStrategy mover)
    (charge : ℝ)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (htransfer : charge ≤
      ∑ recipient ∈ Finset.univ.erase mover,
        quittingTerminalSemanticDebtChange
          (quittingTerminalSemanticPair reward profile)
          (quittingTerminalSemanticPair reward
            (Function.update profile mover target)) recipient)
    (hcharge : 0 < charge) :
    ∃ recipient ∈ Finset.univ.erase mover,
      HasQuittingEndpointDebtRecipientAtom reward profile mover recipient
        target := by
  have hsumPositive : 0 <
      ∑ recipient ∈ Finset.univ.erase mover,
        quittingTerminalSemanticDebtChange
          (quittingTerminalSemanticPair reward profile)
          (quittingTerminalSemanticPair reward
            (Function.update profile mover target)) recipient :=
    hcharge.trans_le htransfer
  have hzero : (∑ _recipient ∈ Finset.univ.erase mover, (0 : ℝ)) = 0 := by
    simp
  obtain ⟨recipient, hrecipient, hpositive⟩ := Finset.exists_lt_of_sum_lt
    (show (∑ _recipient ∈ Finset.univ.erase mover, (0 : ℝ)) <
        ∑ recipient ∈ Finset.univ.erase mover,
          quittingTerminalSemanticDebtChange
            (quittingTerminalSemanticPair reward profile)
            (quittingTerminalSemanticPair reward
              (Function.update profile mover target)) recipient by
      simpa only [hzero] using hsumPositive)
  refine ⟨recipient, hrecipient, ?_⟩
  exact hasQuittingEndpointDebtRecipientAtom_of_pos reward profile mover
    recipient target hM hreward hpositive

/-- **Causal collision dispatch with unmatched-recipient atom compilation.**

The profitable branch retains the original reached-row gain and routed
collision cylinder.  Whenever the near-minimum error is smaller than that
gain, its positive aggregate transfer is compiled on the same endpoint edge
into a literal atom certificate for one distinct recipient.  The recipient
is not required to occur in the routed coalition. -/
theorem causalCollision_tailEscape_or_quantitativeRecipientAtom
    [Nonempty iota]
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
        let targetStrategy := quittingStagePureEndpointBehaviorDeviation
          reward profile who stage action
        let targetProfile := Function.update profile who targetStrategy
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
              HasQuittingEndpointDebtRecipientAtom reward profile who recipient
                targetStrategy) ∧
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
  have hdispatch :=
    causalCollision_tailEscape_or_quantitativeNearMinimumTransfer
      reward minimum profile stage terminal lower epsilon hM hreward
        hminimumCarrier hminimum hminimumDebt hcollision hlower hnear hmass
  rcases hdispatch with hescape | hgain
  · exact Or.inl hescape
  · right
    rcases hgain with ⟨who, hpositive, hquantitative, htarget,
      hmover, htransfer, _hpositiveRecipient, hrouted, horientation⟩
    refine ⟨who, hpositive, hquantitative, htarget, hmover, htransfer,
      ?_, hrouted, horientation⟩
    intro hepsilon
    let tail := quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (stage + 1))
    let root := quittingProfileLiveRoot reward profile stage
    let action := quittingRootBestEndpointAction reward tail.1 root who
    let targetStrategy := quittingStagePureEndpointBehaviorDeviation
      reward profile who stage action
    let targetProfile := Function.update profile who targetStrategy
    let gain := quittingTerminalPayoff reward targetProfile who -
      quittingTerminalPayoff reward profile who
    have hepsilon' : epsilon < gain := by
      simpa only [tail, root, action, targetStrategy, targetProfile, gain] using
        hepsilon
    have hcompiled :=
      exists_endpointDebtRecipientAtom_of_positiveAggregateTransfer
        reward profile who targetStrategy (gain - epsilon) hM hreward
          (by simpa only [tail, root, action, targetStrategy, targetProfile,
            gain] using htransfer)
          (sub_pos.mpr hepsilon')
    simpa only [tail, root, action, targetStrategy, targetProfile, gain] using
      hcompiled

end GameTheory
