/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauPairDropoutConsumer
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticNashDefectMobiusIncidence
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticLinearPenaltyResetConsumer

/-!
# Same-row sign at the floor-forced pair dropout

An arbitrary fractional endpoint word is unsigned.  The exact additional
hypothesis needed for a same-row sign is endpoint provenance: each recorded
action must be the better endpoint recomputed at its literal prefix root and
the fixed continuation cap.

Under that hypothesis, the pair-to-singleton full Continue overwrite forced
by the minimum-debt collision floor gains exactly the mover's local Nash
defect.  Positive mass on the pair implies that the mover was playing Quit
with positive probability.  Consequently there are exactly two branches:

* positive local defect, hence a strictly profitable same-row deviation;
* zero local defect, in which case the Quit and Continue endpoint payoffs are
  exactly tied.

The counterexample-regime capstone retains positive opponent incidence both
before and after the dropout, as well as the existing negative punishment
moat or strict overlapping-pair replacement.  It does not turn the tie branch
into a strict cycle edge.  `TerminalSemanticPairDropoutSignRegression` shows
that omitting endpoint provenance is strictly worse: the routed dropout can
then point opposite to the better endpoint.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- A positive exact coalition containing `other` contributes its full mass
to the displayed root opponent-incidence coordinate. -/
theorem quittingRootCoalitionMass_le_opponentIncidenceMass_of_other_mem
    (root : ι → PMF Bool) (coalition : Finset ι) (marked other : ι)
    (hnonempty : coalition.Nonempty) (hother : other ∈ coalition)
    (hne : other ≠ marked) :
    quittingRootCoalitionMass root coalition ≤
      quittingRootOpponentIncidenceMass marked other root := by
  let terminal : {S : Finset ι // S.Nonempty} := ⟨coalition, hnonempty⟩
  unfold quittingRootOpponentIncidenceMass
  have hterminal : terminal ∈ Finset.univ.filter
      (fun outcome : {S : Finset ι // S.Nonempty} =>
        other ∈ outcome.val ∧ other ≠ marked) := by
    simp [terminal, hother, hne]
  exact Finset.single_le_sum
    (fun outcome _ =>
      MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg
        root outcome.val)
    hterminal

/-! ## Signing the linear-penalty first full overwrite -/

/-- **Same-row sign at the linear-penalty full overwrite.**

An exact return from the supporting point to the minimum reset face forces a
first unit-weight move.  If the endpoint word retains its recomputed
best-endpoint provenance, that overwrite gains exactly the local coordinate
Nash defect at its literal prefix root.  Strict profitability is equivalent
to positive local defect; otherwise the overwrite is payoff-neutral.

This theorem supplies the signed local move but no coalition label.  The
pair-dropout consumer below adds positive routed incidence and punishment
geometry when the collision floor supplies a positive pair cylinder. -/
theorem exists_signed_firstFullMove_of_linearPenalty_exactResetFaceReturn
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (moves : List (QuittingFractionalEndpointMove ι))
    (resetOwner : ι) (penalty : ℝ)
    (hexcess : quittingTerminalSemanticDebtSum minimum <
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingRootThenContinuationProfile reward root continuation)))
    (hincidence : 0 < quittingTerminalTotalOpponentIncidenceMass resetOwner
      (quittingTerminalOutcomeMass reward
        (quittingRootThenContinuationProfile reward root continuation)))
    (hlinear : ∀ point ∈ quittingTerminalSemanticLawCarrier reward,
      ((quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward
                (quittingRootThenContinuationProfile reward root continuation)) -
            quittingTerminalSemanticDebtSum minimum) /
          quittingTerminalTotalOpponentIncidenceMass resetOwner
            (quittingTerminalOutcomeMass reward
              (quittingRootThenContinuationProfile reward root continuation))) *
          quittingTerminalTotalOpponentIncidenceMass resetOwner point.2 -
        (quittingTerminalSemanticDebtSum point.1 -
          quittingTerminalSemanticDebtSum minimum) ≤
        penalty * quittingTerminalSemanticDebt point.1 resetOwner)
    (hfinalMinimum : quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingRootThenContinuationProfile reward
            (quittingFractionalEndpointMoves moves root) continuation)) =
      quittingTerminalSemanticDebtSum minimum)
    (hfinalReset : quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingRootThenContinuationProfile reward
            (quittingFractionalEndpointMoves moves root) continuation))
        resetOwner = 0)
    (hbestEndpoint : ∀ before move after,
      moves = before ++ move :: after →
        move.action = quittingRootBestEndpointAction reward minimum.1
          (quittingFractionalEndpointMoves before root) move.who) :
    ∃ before move after beforeRoot afterRoot,
      moves = before ++ move :: after ∧
        beforeRoot = quittingFractionalEndpointMoves before root ∧
        afterRoot = move.apply beforeRoot ∧
        (∀ prior ∈ before, prior.weight < 1) ∧
        move.weight = 1 ∧
        move.action = quittingRootBestEndpointAction reward minimum.1
          beforeRoot move.who ∧
        afterRoot = Function.update beforeRoot move.who
          (PMF.pure move.action) ∧
        quittingRootSuccessorPayoff reward minimum.1 afterRoot move.who -
            quittingRootSuccessorPayoff reward minimum.1 beforeRoot move.who =
          quittingRootCoordinateNashDefect reward minimum.1
            beforeRoot move.who ∧
        ((0 < quittingRootCoordinateNashDefect reward minimum.1
                beforeRoot move.who ∧
            0 < quittingRootSuccessorPayoff reward minimum.1
                  afterRoot move.who -
                quittingRootSuccessorPayoff reward minimum.1
                  beforeRoot move.who) ∨
          (quittingRootCoordinateNashDefect reward minimum.1
                beforeRoot move.who = 0 ∧
            quittingRootSuccessorPayoff reward minimum.1
                  afterRoot move.who -
                quittingRootSuccessorPayoff reward minimum.1
                  beforeRoot move.who = 0)) := by
  obtain ⟨before, move, after, hsplit, hbeforeStrict, hfull⟩ :=
    exists_first_full_move_of_linearPenalty_exactResetFaceReturn
      reward minimum root continuation moves resetOwner penalty hexcess
        hincidence hlinear hfinalMinimum hfinalReset
  let beforeRoot := quittingFractionalEndpointMoves before root
  let afterRoot := move.apply beforeRoot
  have hbest : move.action = quittingRootBestEndpointAction reward minimum.1
      beforeRoot move.who := by
    dsimp only [beforeRoot]
    exact hbestEndpoint before move after hsplit
  have hafterUpdate : afterRoot = Function.update beforeRoot move.who
      (PMF.pure move.action) := by
    dsimp only [afterRoot]
    exact move.apply_eq_update_pure_of_weight_eq_one beforeRoot hfull
  have hgain : quittingRootSuccessorPayoff reward minimum.1
        afterRoot move.who -
      quittingRootSuccessorPayoff reward minimum.1 beforeRoot move.who =
        quittingRootCoordinateNashDefect reward minimum.1
          beforeRoot move.who := by
    rw [hafterUpdate, hbest]
    exact quittingRootSuccessorPayoff_bestEndpoint_sub_eq_coordinateNashDefect
      reward minimum.1 beforeRoot move.who
  have halternative :
      (0 < quittingRootCoordinateNashDefect reward minimum.1
            beforeRoot move.who ∧
        0 < quittingRootSuccessorPayoff reward minimum.1
              afterRoot move.who -
            quittingRootSuccessorPayoff reward minimum.1
              beforeRoot move.who) ∨
      (quittingRootCoordinateNashDefect reward minimum.1
            beforeRoot move.who = 0 ∧
        quittingRootSuccessorPayoff reward minimum.1
              afterRoot move.who -
            quittingRootSuccessorPayoff reward minimum.1
              beforeRoot move.who = 0) := by
    have hnonneg := quittingRootCoordinateNashDefect_nonneg
      reward minimum.1 beforeRoot move.who
    rcases hnonneg.eq_or_lt with hzero | hpositive
    · exact Or.inr ⟨hzero.symm, by rw [hgain, hzero.symm]⟩
    · exact Or.inl ⟨hpositive, by rw [hgain]; exact hpositive⟩
  exact ⟨before, move, after, beforeRoot, afterRoot, hsplit, rfl, rfl,
    hbeforeStrict, hfull, hbest, hafterUpdate, hgain, halternative⟩

namespace QuittingCounterexampleRegime

/-- **Floor-safe signed pair-dropout consumer.**

Suppose every move in the finite reset word records the better endpoint at
its actual prefix root.  If the word Nashifies a positive collision above a
positive minimum debt, the forced pair dropout is a weakly profitable
same-row deviation.  It is either strictly profitable, or its two endpoint
payoffs are exactly tied.  Both the pair and singleton rows retain positive
incidence from the surviving player relative to the dropout player.

The singleton then enters the existing negative punishment moat or admits a
strict positive-mass overlapping-pair replacement.  The remaining residual
is explicit: neither the minimum-debt floor nor endpoint provenance excludes
the exact endpoint-tie branch. -/
theorem exists_signed_pairDropout_negativeMoat_or_pairReplacement
    (regime : QuittingCounterexampleRegime reward)
    (minimum : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool)
    (moves : List (QuittingFractionalEndpointMove ι))
    (terminal : {S : Finset ι // S.Nonempty}) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ outcome player, |reward outcome player| ≤ M)
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hcollision : 1 < terminal.val.card)
    (hmass : 0 < quittingRootCoalitionMass root terminal.val)
    (hminimumDebt : 0 < quittingTerminalSemanticDebtSum minimum)
    (hfinalDefect : quittingRootTotalNashDefect reward minimum.1
      (quittingFractionalEndpointMoves moves root) = 0)
    (hbestEndpoint : ∀ before move after,
      moves = before ++ move :: after →
        move.action = quittingRootBestEndpointAction reward minimum.1
          (quittingFractionalEndpointMoves before root) move.who) :
    ∃ before move after beforeRoot afterRoot beforeCoalition afterCoalition
        owner,
      moves = before ++ move :: after ∧
        beforeRoot = quittingFractionalEndpointMoves before root ∧
        afterRoot = move.apply beforeRoot ∧
        beforeCoalition =
          quittingFractionalEndpointTrackedCoalition before terminal.val ∧
        afterCoalition = move.nextTrackedCoalition beforeCoalition ∧
        move.weight = 1 ∧ move.who ∈ beforeCoalition ∧
        move.action = false ∧
        move.action = quittingRootBestEndpointAction reward minimum.1
          beforeRoot move.who ∧
        beforeCoalition.card = 2 ∧
        afterCoalition = beforeCoalition.erase move.who ∧
        afterCoalition = {owner} ∧
        beforeCoalition = insert move.who {owner} ∧
        move.who ≠ owner ∧
        afterRoot = Function.update beforeRoot move.who (PMF.pure false) ∧
        0 < quittingRootCoalitionMass beforeRoot beforeCoalition ∧
        0 < quittingRootCoalitionMass afterRoot afterCoalition ∧
        0 < quittingRootOpponentIncidenceMass move.who owner beforeRoot ∧
        0 < quittingRootOpponentIncidenceMass move.who owner afterRoot ∧
        quittingRootQuitPayoff reward minimum.1 beforeRoot move.who ≤
          quittingRootContinuePayoff reward minimum.1 beforeRoot move.who ∧
        quittingRootSuccessorPayoff reward minimum.1 afterRoot move.who -
            quittingRootSuccessorPayoff reward minimum.1 beforeRoot move.who =
          quittingRootCoordinateNashDefect reward minimum.1
            beforeRoot move.who ∧
        ((0 < quittingRootCoordinateNashDefect reward minimum.1
                beforeRoot move.who ∧
            0 < quittingRootSuccessorPayoff reward minimum.1
                  afterRoot move.who -
                quittingRootSuccessorPayoff reward minimum.1
                  beforeRoot move.who) ∨
          (quittingRootCoordinateNashDefect reward minimum.1
                beforeRoot move.who = 0 ∧
            quittingRootEndpointDifference reward minimum.1
                beforeRoot move.who = 0 ∧
            quittingRootSuccessorPayoff reward minimum.1
                  afterRoot move.who -
                quittingRootSuccessorPayoff reward minimum.1
                  beforeRoot move.who = 0)) ∧
        ((quittingSoloReward reward owner owner ≤ -regime.terminalGap ∧
            quittingSoloReward reward owner owner <
              quittingPunishmentValue reward owner) ∨
          ∃ outsider replacementRoot replacementCoalition,
            outsider ≠ owner ∧
              replacementRoot =
                Function.update afterRoot outsider (PMF.pure true) ∧
              replacementCoalition = insert outsider afterCoalition ∧
              replacementCoalition = {owner, outsider} ∧
              afterCoalition ⊂ replacementCoalition ∧
              replacementCoalition.card = 2 ∧
              quittingSoloReward reward owner outsider <
                quittingSingletonCollisionReward reward owner outsider ∧
              (-regime.terminalGap <
                    quittingSoloReward reward owner owner →
                quittingSoloReward reward owner outsider +
                    regime.terminalGap ≤
                  quittingSingletonCollisionReward reward owner outsider) ∧
              0 < quittingRootCoalitionMass replacementRoot
                replacementCoalition) := by
  obtain ⟨before, move, after, beforeRoot, afterRoot, beforeCoalition,
      afterCoalition, owner, hsplit, hbeforeRoot, hafterRoot,
      hbeforeCoalition, hafterCoalition, hfull, hmember, hcontinue,
      hbeforeCard, hafterErase, hsingleton, hbeforePair, hdropperNe,
      hafterUpdate, hbeforeMass, hafterMass, hconsumer⟩ :=
    regime.exists_negativeMoat_or_pairReplacement_of_dropout
      minimum root moves terminal hM hreward hminimumCarrier hminimum
        hcollision hmass hminimumDebt hfinalDefect
  have hbest : move.action =
      quittingRootBestEndpointAction reward minimum.1 beforeRoot move.who := by
    rw [hbeforeRoot]
    exact hbestEndpoint before move after hsplit
  have hbestContinue : quittingRootBestEndpointAction reward minimum.1
      beforeRoot move.who = false := by
    rw [← hbest, hcontinue]
  have hendpointSign : quittingRootQuitPayoff reward minimum.1
      beforeRoot move.who ≤
        quittingRootContinuePayoff reward minimum.1 beforeRoot move.who := by
    by_contra hnot
    have hbestQuit : quittingRootBestEndpointAction reward minimum.1
        beforeRoot move.who = true := by
      simp [quittingRootBestEndpointAction, hnot]
    rw [hbestQuit] at hbestContinue
    contradiction
  have hgain : quittingRootSuccessorPayoff reward minimum.1
        afterRoot move.who -
      quittingRootSuccessorPayoff reward minimum.1 beforeRoot move.who =
        quittingRootCoordinateNashDefect reward minimum.1
          beforeRoot move.who := by
    rw [hafterUpdate]
    simpa [hbestContinue] using
      (quittingRootSuccessorPayoff_bestEndpoint_sub_eq_coordinateNashDefect
        reward minimum.1 beforeRoot move.who)
  have hbeforeNonempty : beforeCoalition.Nonempty :=
    Finset.card_pos.mp (by omega)
  have hownerBefore : owner ∈ beforeCoalition := by
    rw [hbeforePair]
    simp
  have hownerAfter : owner ∈ afterCoalition := by
    rw [hsingleton]
    simp
  have hbeforeIncidence : 0 <
      quittingRootOpponentIncidenceMass move.who owner beforeRoot := by
    exact hbeforeMass.trans_le
      (quittingRootCoalitionMass_le_opponentIncidenceMass_of_other_mem
        beforeRoot beforeCoalition move.who owner hbeforeNonempty
          hownerBefore hdropperNe.symm)
  have hafterIncidence : 0 <
      quittingRootOpponentIncidenceMass move.who owner afterRoot := by
    have hafterNonempty : afterCoalition.Nonempty := by
      rw [hsingleton]
      simp
    exact hafterMass.trans_le
      (quittingRootCoalitionMass_le_opponentIncidenceMass_of_other_mem
        afterRoot afterCoalition move.who owner hafterNonempty
          hownerAfter hdropperNe.symm)
  have hquitProbability : 0 < (beforeRoot move.who true).toReal := by
    exact hbeforeMass.trans_le
      (quittingRootCoalitionMass_le_quitProbability_of_mem
        beforeRoot beforeCoalition move.who hmember)
  have hsignAlternative :
      (0 < quittingRootCoordinateNashDefect reward minimum.1
            beforeRoot move.who ∧
        0 < quittingRootSuccessorPayoff reward minimum.1
              afterRoot move.who -
            quittingRootSuccessorPayoff reward minimum.1
              beforeRoot move.who) ∨
      (quittingRootCoordinateNashDefect reward minimum.1
            beforeRoot move.who = 0 ∧
        quittingRootEndpointDifference reward minimum.1
            beforeRoot move.who = 0 ∧
        quittingRootSuccessorPayoff reward minimum.1
              afterRoot move.who -
            quittingRootSuccessorPayoff reward minimum.1
              beforeRoot move.who = 0) := by
    have hdefectNonneg := quittingRootCoordinateNashDefect_nonneg
      reward minimum.1 beforeRoot move.who
    rcases hdefectNonneg.eq_or_lt with hzero | hpositive
    · right
      have hzero' : quittingRootCoordinateNashDefect reward minimum.1
          beforeRoot move.who = 0 := hzero.symm
      have hdiffNonpos : quittingRootEndpointDifference reward minimum.1
          beforeRoot move.who ≤ 0 := by
        unfold quittingRootEndpointDifference
        linarith
      have hformula :=
        quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart
          (reward := reward) minimum.1 beforeRoot move.who
      rw [hzero', max_eq_right hdiffNonpos,
        max_eq_left (neg_nonneg.mpr hdiffNonpos)] at hformula
      simp only [mul_zero, zero_add] at hformula
      have hnegativeDifference :
          -quittingRootEndpointDifference reward minimum.1
              beforeRoot move.who = 0 := by
        rcases mul_eq_zero.mp hformula.symm with hquitZero | hdifferenceZero
        · exact False.elim (hquitProbability.ne' hquitZero)
        · exact hdifferenceZero
      exact ⟨hzero',
        neg_eq_zero.mp hnegativeDifference,
        by rw [hgain, hzero']⟩
    · exact Or.inl ⟨hpositive, by rw [hgain]; exact hpositive⟩
  exact ⟨before, move, after, beforeRoot, afterRoot, beforeCoalition,
    afterCoalition, owner, hsplit, hbeforeRoot, hafterRoot,
    hbeforeCoalition, hafterCoalition, hfull, hmember, hcontinue, hbest,
    hbeforeCard, hafterErase, hsingleton, hbeforePair, hdropperNe,
    hafterUpdate, hbeforeMass, hafterMass, hbeforeIncidence,
    hafterIncidence, hendpointSign, hgain, hsignAlternative, hconsumer⟩

end QuittingCounterexampleRegime

end GameTheory
