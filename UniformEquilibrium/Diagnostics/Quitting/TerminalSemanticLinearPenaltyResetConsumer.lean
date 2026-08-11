/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetFaceReprojection
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauFractionalResetDropout

/-!
# Finite reset words under a linear reset-face penalty

The linear branch of reset-face reprojection gives a genuine finite-word
estimate, but not a monotone descent.  If `E = D - D_*`, `I` is the selected
opponent incidence, and `d_r` is the reset-owner debt, its content is the
global support

`slope * I <= E + penalty * d_r`.

Every fractional endpoint word retains the product of its unmoved fractions
of `I`.  Hence a word beginning at the supporting point satisfies

`retention * E_start <= E_final + penalty * d_r(final)`.

In particular, an exact return to the minimum reset face must contain a full
endpoint move.  This is the sharp finite obstruction supplied by the linear
penalty.  It does not say that the displayed augmented quantity decreases
from one move to the next: the supporting inequality is anchored at one
point and gives no sign for differences between two off-face points.  The
forced full move is also unsigned: the explicit regression in
`TerminalSemanticPairDropoutSignRegression` shows that a routed pair dropout
can point opposite to the mover's better endpoint.  A strategic consumer
must separately retain same-root payoff provenance.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Incidence retention through a finite endpoint word -/

/-- Total opponent incidence retains the unmoved fraction under one partial
endpoint move over a fixed executable continuation law. -/
theorem one_sub_mul_totalOpponentIncidence_le_partialLawPrefix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (move : QuittingFractionalEndpointMove ι) :
    (1 - move.weight) *
        quittingTerminalTotalOpponentIncidenceMass owner
          (quittingTerminalOutcomeLawPrefix root
            (quittingTerminalOutcomeMass reward continuation)) ≤
      quittingTerminalTotalOpponentIncidenceMass owner
        (quittingTerminalOutcomeLawPrefix (move.apply root)
          (quittingTerminalOutcomeMass reward continuation)) := by
  unfold quittingTerminalTotalOpponentIncidenceMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro other hother
  exact one_sub_mul_incidence_le_partialLawPrefix
    owner other root move.who move.action move.weight move.weight_nonneg
      move.weight_le_one (quittingTerminalOutcomeMass reward continuation)
      (quittingTerminalOpponentIncidenceMass_outcomeMass_nonneg
        reward continuation owner other)

/-- A finite endpoint word retains the product of all unmoved fractions of
the initial total opponent incidence, with the continuation law held fixed. -/
theorem quittingFractionalEndpointRetention_mul_totalOpponentIncidence_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (moves : List (QuittingFractionalEndpointMove ι)) :
    quittingFractionalEndpointRetention moves *
        quittingTerminalTotalOpponentIncidenceMass owner
          (quittingTerminalOutcomeLawPrefix root
            (quittingTerminalOutcomeMass reward continuation)) ≤
      quittingTerminalTotalOpponentIncidenceMass owner
        (quittingTerminalOutcomeLawPrefix
          (quittingFractionalEndpointMoves moves root)
          (quittingTerminalOutcomeMass reward continuation)) := by
  induction moves generalizing root with
  | nil =>
      simp [quittingFractionalEndpointRetention,
        quittingFractionalEndpointMoves]
  | cons move moves ih =>
      have hstep :=
        one_sub_mul_totalOpponentIncidence_le_partialLawPrefix
          reward owner root continuation move
      have hscaled := mul_le_mul_of_nonneg_left hstep
        (quittingFractionalEndpointRetention_nonneg moves)
      have htail := ih (root := move.apply root)
      rw [quittingFractionalEndpointRetention,
        quittingFractionalEndpointMoves]
      rw [mul_assoc, mul_left_comm (1 - move.weight)]
      exact hscaled.trans htail

/-! ## The augmented surface-tension floor -/

/-- **Finite linear-penalty reset floor.**

At a positive-incidence supporting point, a global linear reset-face penalty
survives an arbitrary finite word of fractional endpoint moves.  The only
ways to pay for retained surface-tension excess are final total-debt excess
and final debt on the selected reset coordinate. -/
theorem fractionalEndpointMoves_linearPenalty_augmentedFloor
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
        penalty * quittingTerminalSemanticDebt point.1 resetOwner) :
    quittingFractionalEndpointRetention moves *
        (quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward
              (quittingRootThenContinuationProfile reward root continuation)) -
          quittingTerminalSemanticDebtSum minimum) ≤
      (quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingRootThenContinuationProfile reward
              (quittingFractionalEndpointMoves moves root) continuation)) -
        quittingTerminalSemanticDebtSum minimum) +
      penalty * quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingRootThenContinuationProfile reward
            (quittingFractionalEndpointMoves moves root) continuation))
        resetOwner := by
  let initialProfile :=
    quittingRootThenContinuationProfile reward root continuation
  let finalRoot := quittingFractionalEndpointMoves moves root
  let finalProfile :=
    quittingRootThenContinuationProfile reward finalRoot continuation
  let initialExcess := quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward initialProfile) -
    quittingTerminalSemanticDebtSum minimum
  let finalExcess := quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward finalProfile) -
    quittingTerminalSemanticDebtSum minimum
  let initialIncidence := quittingTerminalTotalOpponentIncidenceMass resetOwner
    (quittingTerminalOutcomeMass reward initialProfile)
  let finalIncidence := quittingTerminalTotalOpponentIncidenceMass resetOwner
    (quittingTerminalOutcomeMass reward finalProfile)
  let slope := initialExcess / initialIncidence
  have hinitialExcess : 0 < initialExcess := by
    dsimp only [initialExcess, initialProfile]
    linarith
  have hinitialIncidence : 0 < initialIncidence := by
    exact hincidence
  have hslope : 0 ≤ slope :=
    div_nonneg hinitialExcess.le hinitialIncidence.le
  have hretention : quittingFractionalEndpointRetention moves *
      initialIncidence ≤ finalIncidence := by
    have hretain :=
      quittingFractionalEndpointRetention_mul_totalOpponentIncidence_le
        reward resetOwner root continuation moves
    rw [quittingTerminalOutcomeLawPrefix_outcomeMass,
      quittingTerminalOutcomeLawPrefix_outcomeMass] at hretain
    exact hretain
  have hscaled := mul_le_mul_of_nonneg_left hretention hslope
  have hfinalMem :
      (quittingTerminalSemanticPair reward finalProfile,
          quittingTerminalOutcomeMass reward finalProfile) ∈
        quittingTerminalSemanticLawCarrier reward :=
    quittingTerminalSemanticLawPoint_mem_carrier reward finalProfile
  have hsupport := hlinear
    (quittingTerminalSemanticPair reward finalProfile,
      quittingTerminalOutcomeMass reward finalProfile) hfinalMem
  have hslopeIdentity : slope *
      (quittingFractionalEndpointRetention moves * initialIncidence) =
        quittingFractionalEndpointRetention moves * initialExcess := by
    dsimp only [slope]
    field_simp
  change quittingFractionalEndpointRetention moves * initialExcess ≤
    finalExcess + penalty * quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward finalProfile) resetOwner
  change slope * finalIncidence - finalExcess ≤
      penalty * quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward finalProfile) resetOwner
    at hsupport
  rw [hslopeIdentity] at hscaled
  linarith

/-- **Finite opposite-face transfer with exact linear-penalty leakage.**

If the endpoint word decreases one selected debt coordinate by `gain`, the
gain is transferred to the other player coordinates except for two explicit
payments: the lost fraction of the initial surface excess, and the final
linear penalty on the reset-owner debt.  For one move of weight `lambda`, the
first payment is exactly `lambda * initialExcess`; for a word it is governed
by the full retention product. -/
theorem fractionalEndpointMoves_linearPenalty_opponentTransfer
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (moves : List (QuittingFractionalEndpointMove ι))
    (resetOwner mover : ι) (penalty gain : ℝ)
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
    (hdecrease : quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingRootThenContinuationProfile reward
            (quittingFractionalEndpointMoves moves root) continuation)) mover =
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (quittingRootThenContinuationProfile reward root continuation))
          mover - gain) :
    gain ≤
      (1 - quittingFractionalEndpointRetention moves) *
        (quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward
              (quittingRootThenContinuationProfile reward root continuation)) -
          quittingTerminalSemanticDebtSum minimum) +
      penalty * quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingRootThenContinuationProfile reward
            (quittingFractionalEndpointMoves moves root) continuation))
        resetOwner +
      ∑ recipient ∈ Finset.univ.erase mover,
        quittingTerminalSemanticDebtChange
          (quittingTerminalSemanticPair reward
            (quittingRootThenContinuationProfile reward root continuation))
          (quittingTerminalSemanticPair reward
            (quittingRootThenContinuationProfile reward
              (quittingFractionalEndpointMoves moves root) continuation))
          recipient := by
  let initial := quittingTerminalSemanticPair reward
    (quittingRootThenContinuationProfile reward root continuation)
  let final := quittingTerminalSemanticPair reward
    (quittingRootThenContinuationProfile reward
      (quittingFractionalEndpointMoves moves root) continuation)
  let initialExcess := quittingTerminalSemanticDebtSum initial -
    quittingTerminalSemanticDebtSum minimum
  let finalExcess := quittingTerminalSemanticDebtSum final -
    quittingTerminalSemanticDebtSum minimum
  have hfloor := fractionalEndpointMoves_linearPenalty_augmentedFloor
    reward minimum root continuation moves resetOwner penalty hexcess
      hincidence hlinear
  have hsum := Finset.sum_erase_add Finset.univ
    (fun player => quittingTerminalSemanticDebtChange initial final player)
    (Finset.mem_univ mover)
  have htotal : (∑ player,
      quittingTerminalSemanticDebtChange initial final player) =
      finalExcess - initialExcess := by
    dsimp only [initialExcess, finalExcess]
    unfold quittingTerminalSemanticDebtChange
      quittingTerminalSemanticDebtSum
    rw [Finset.sum_sub_distrib]
    ring
  have hmover : quittingTerminalSemanticDebtChange initial final mover =
      -gain := by
    unfold quittingTerminalSemanticDebtChange
    rw [hdecrease]
    ring
  change quittingFractionalEndpointRetention moves * initialExcess ≤
      finalExcess + penalty * quittingTerminalSemanticDebt final resetOwner
    at hfloor
  rw [htotal, hmover] at hsum
  change gain ≤
    (1 - quittingFractionalEndpointRetention moves) * initialExcess +
      penalty * quittingTerminalSemanticDebt final resetOwner +
      ∑ recipient ∈ Finset.univ.erase mover,
        quittingTerminalSemanticDebtChange initial final recipient
  nlinarith

/-- An exact return to the global-minimum reset face cannot be achieved by a
finite word of strictly fractional moves.  Some move has unit weight, and
the theorem returns the first such move together with its strict prefix.

The move has no payoff sign.  In particular this conclusion alone cannot be
fed into a strict-toggle or cycle compiler; the sign regression described in
`TerminalSemanticPairDropoutSignRegression` is sharp. -/
theorem exists_first_full_move_of_linearPenalty_exactResetFaceReturn
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
        resetOwner = 0) :
    ∃ before move after,
      moves = before ++ move :: after ∧
        (∀ prior ∈ before, prior.weight < 1) ∧ move.weight = 1 := by
  have hfloor := fractionalEndpointMoves_linearPenalty_augmentedFloor
    reward minimum root continuation moves resetOwner penalty hexcess
      hincidence hlinear
  rw [hfinalMinimum, hfinalReset] at hfloor
  norm_num at hfloor
  have hretentionNonneg := quittingFractionalEndpointRetention_nonneg moves
  have hexcessPositive : 0 <
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingRootThenContinuationProfile reward root continuation)) -
        quittingTerminalSemanticDebtSum minimum := sub_pos.mpr hexcess
  have hretentionZero : quittingFractionalEndpointRetention moves = 0 := by
    by_contra hne
    have hretentionPositive : 0 < quittingFractionalEndpointRetention moves :=
      lt_of_le_of_ne hretentionNonneg (Ne.symm hne)
    have hproductPositive := mul_pos hretentionPositive hexcessPositive
    linarith
  exact exists_first_full_fractionalEndpointMove_of_retention_eq_zero
    moves hretentionZero

end GameTheory
