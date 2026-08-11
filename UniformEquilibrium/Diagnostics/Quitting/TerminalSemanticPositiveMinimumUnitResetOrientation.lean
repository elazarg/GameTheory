/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPositiveMinimumUnitResetCycle

/-!
# Strategic orientation of positive unit resets

The debt circulation carried by a closed word is signed across players, but
its individual reset edges are not sign-ambiguous.  A full reached-row
best-endpoint move which kills a positive source debt realizes the mover's
entire behavioral best-response envelope.  Its reached-row defect and live
mass are both strictly positive, and the mover's actual payoff rises by
exactly its source debt.

Consequently a closed positive-debt unit-reset word is already a closed
strict asynchronous best-response word on the terminal-semantic carrier.
This orients the *behavioral* edges.  It does not orient the routed terminal
coalition edge: the strict gain can still combine immediate coalition payoff
with continuation value, so a punishment or joiner sign requires additional
terminal-edge data.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {reward : {S : Finset iota // S.Nonempty} → Payoff iota}

/-- **A positive unit reset is an exact strict best response.**

If the full recomputed reached-row endpoint kills the mover's positive
best-response debt, then the move has strictly positive live mass and local
Nash defect.  Its actual payoff gain is exactly the source debt, and its
target payoff equals the source behavioral best-response envelope. -/
theorem stageFullBestEndpoint_zeroFace_strictBestResponse
    (profile : (quittingGame reward).BehaviorProfile)
    (who : iota) (stage : ℕ)
    (hsource : 0 < quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) who)
    (htarget : quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (quittingStageFullBestEndpointProfile reward profile who stage)) who = 0) :
    let tail := quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (stage + 1))
    let root := quittingProfileLiveRoot reward profile stage
    let target := quittingStageFullBestEndpointProfile reward profile who stage
    0 < quittingLiveMass reward profile stage ∧
      0 < quittingRootCoordinateNashDefect reward tail.1 root who ∧
      quittingTerminalPayoff reward target who -
          quittingTerminalPayoff reward profile who =
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) who ∧
      quittingTerminalPayoff reward profile who <
        quittingTerminalPayoff reward target who ∧
      quittingTerminalPayoff reward target who =
        quittingContinuationBestResponseValue reward profile who := by
  dsimp only
  let target := quittingStageFullBestEndpointProfile reward profile who stage
  have hdecrease := quittingTerminalSemanticDebt_stagePartialBestEndpoint_eq
    reward profile who stage 1 zero_le_one le_rfl
  change quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward target) who =
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) who -
      1 * quittingLiveMass reward profile stage *
        quittingRootCoordinateNashDefect reward
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward profile
              (stage + 1))).1
          (quittingProfileLiveRoot reward profile stage) who at hdecrease
  have hproduct : quittingLiveMass reward profile stage *
        quittingRootCoordinateNashDefect reward
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward profile
              (stage + 1))).1
          (quittingProfileLiveRoot reward profile stage) who =
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) who := by
    rw [htarget] at hdecrease
    norm_num at hdecrease
    linarith
  have hproductPos : 0 < quittingLiveMass reward profile stage *
      quittingRootCoordinateNashDefect reward
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward profile
            (stage + 1))).1
        (quittingProfileLiveRoot reward profile stage) who := by
    rw [hproduct]
    exact hsource
  have hliveDefect : 0 < quittingLiveMass reward profile stage ∧
      0 < quittingRootCoordinateNashDefect reward
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward profile
            (stage + 1))).1
        (quittingProfileLiveRoot reward profile stage) who := by
    rcases mul_pos_iff.mp hproductPos with hpositive | hnegative
    · exact hpositive
    · exact (not_lt_of_ge
        (quittingLiveMass_nonneg reward profile stage) hnegative.1).elim
  have hpayoffGain :=
    quittingTerminalPayoff_stagePartialBestEndpointDeviation_sub_eq
      reward profile who stage 1 zero_le_one le_rfl
  change quittingTerminalPayoff reward target who -
      quittingTerminalPayoff reward profile who =
        1 * quittingLiveMass reward profile stage *
          quittingRootCoordinateNashDefect reward
            (quittingTerminalSemanticPair reward
              (quittingAllContinueProfileSpine reward profile
                (stage + 1))).1
            (quittingProfileLiveRoot reward profile stage) who at hpayoffGain
  have hexactGain : quittingTerminalPayoff reward target who -
        quittingTerminalPayoff reward profile who =
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) who := by
    rw [hpayoffGain]
    norm_num
    exact hproduct
  have hstrict : quittingTerminalPayoff reward profile who <
      quittingTerminalPayoff reward target who := by
    linarith
  have henvelope : quittingTerminalPayoff reward target who =
      quittingContinuationBestResponseValue reward profile who := by
    rw [quittingTerminalSemanticDebt] at hexactGain
    change quittingTerminalPayoff reward target who -
        quittingTerminalPayoff reward profile who =
      quittingContinuationBestResponseValue reward profile who -
        quittingTerminalPayoff reward profile who at hexactGain
    linarith
  exact ⟨hliveDefect.1, hliveDefect.2, hexactGain, hstrict, henvelope⟩

/-- **A closed positive unit-reset word is a strict best-response cycle.**

Every edge of the word strictly increases its mover's actual payoff and
lands exactly at that mover's source behavioral best-response value.  The
semantic endpoint closes even though the mover label may vary from edge to
edge. -/
theorem finite_stageFullBestEndpoint_cycle_strictBestResponseWord
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (mover : ℕ → iota) (stage : ℕ → ℕ)
    (length : ℕ)
    (hstep : ∀ time < length,
      profiles (time + 1) = quittingStageFullBestEndpointProfile
        reward (profiles time) (mover time) (stage time))
    (hsource : ∀ time < length, 0 < quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward (profiles time)) (mover time))
    (htarget : ∀ time < length, quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward (profiles (time + 1)))
        (mover time) = 0)
    (hclosed : quittingTerminalSemanticPair reward (profiles length) =
      quittingTerminalSemanticPair reward (profiles 0)) :
    ((∀ time < length,
      quittingTerminalPayoff reward (profiles (time + 1)) (mover time) -
          quittingTerminalPayoff reward (profiles time) (mover time) =
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward (profiles time))
          (mover time) ∧
      quittingTerminalPayoff reward (profiles time) (mover time) <
        quittingTerminalPayoff reward (profiles (time + 1)) (mover time) ∧
      quittingTerminalPayoff reward (profiles (time + 1)) (mover time) =
        quittingContinuationBestResponseValue reward (profiles time)
          (mover time) ∧
      0 < quittingLiveMass reward (profiles time) (stage time) ∧
      0 < quittingRootCoordinateNashDefect reward
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward (profiles time)
            (stage time + 1))).1
        (quittingProfileLiveRoot reward (profiles time) (stage time))
        (mover time)) ∧
      quittingTerminalSemanticPair reward (profiles length) =
        quittingTerminalSemanticPair reward (profiles 0)) := by
  refine ⟨?_, hclosed⟩
  intro time htime
  have htargetTime : quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (quittingStageFullBestEndpointProfile reward (profiles time)
          (mover time) (stage time))) (mover time) = 0 := by
    rw [← hstep time htime]
    exact htarget time htime
  have hedge := stageFullBestEndpoint_zeroFace_strictBestResponse
    (reward := reward) (profiles time) (mover time) (stage time)
      (hsource time htime) htargetTime
  rw [← hstep time htime] at hedge
  exact ⟨hedge.2.2.1, hedge.2.2.2.1, hedge.2.2.2.2,
    hedge.1, hedge.2.1⟩

/-! ## Nonnegative lift of signed debt transfer -/

/-- Debt lost by one coordinate between two semantic states. -/
def quittingDebtTransportLoss (before after : iota → ℝ) (who : iota) : ℝ :=
  max (before who - after who) 0

/-- Debt gained by one coordinate between two semantic states. -/
def quittingDebtTransportGain (before after : iota → ℝ) (who : iota) : ℝ :=
  max (after who - before who) 0

/-- Debt which stays on the same player coordinate across one step. -/
def quittingDebtTransportStorage
    (before after : iota → ℝ) (who : iota) : ℝ :=
  min (before who) (after who)

/-- Total coordinate loss across one constant-sum step. -/
def quittingDebtTransportTotalLoss (before after : iota → ℝ) : ℝ :=
  ∑ who, quittingDebtTransportLoss before after who

/-- Canonical nonnegative transport across a constant-sum debt step.

Unchanged debt travels on diagonal storage edges.  Lost debt is coupled to
gained debt by the product coupling.  The zero-loss branch is diagonal. -/
def quittingDebtTransport
    (before after : iota → ℝ) (sender recipient : iota) : ℝ :=
  if quittingDebtTransportTotalLoss before after = 0 then
    if sender = recipient then before sender else 0
  else
    (if sender = recipient then
      quittingDebtTransportStorage before after sender else 0) +
      quittingDebtTransportLoss before after sender *
        quittingDebtTransportGain before after recipient /
          quittingDebtTransportTotalLoss before after

omit [Fintype iota] [DecidableEq iota] in
theorem quittingDebtTransport_storage_add_loss
    (before after : iota → ℝ) (who : iota) :
    quittingDebtTransportStorage before after who +
        quittingDebtTransportLoss before after who = before who := by
  by_cases hle : before who ≤ after who
  · simp [quittingDebtTransportStorage, quittingDebtTransportLoss,
      min_eq_left hle, max_eq_right (sub_nonpos.mpr hle)]
  · have hle' : after who ≤ before who := le_of_not_ge hle
    simp [quittingDebtTransportStorage, quittingDebtTransportLoss,
      min_eq_right hle', max_eq_left (sub_nonneg.mpr hle')]

omit [Fintype iota] [DecidableEq iota] in
theorem quittingDebtTransport_storage_add_gain
    (before after : iota → ℝ) (who : iota) :
    quittingDebtTransportStorage before after who +
        quittingDebtTransportGain before after who = after who := by
  by_cases hle : before who ≤ after who
  · simp [quittingDebtTransportStorage, quittingDebtTransportGain,
      min_eq_left hle, max_eq_left (sub_nonneg.mpr hle)]
  · have hle' : after who ≤ before who := le_of_not_ge hle
    simp [quittingDebtTransportStorage, quittingDebtTransportGain,
      min_eq_right hle', max_eq_right (sub_nonpos.mpr hle')]

omit [Fintype iota] [DecidableEq iota] in
theorem quittingDebtTransport_loss_sub_gain
    (before after : iota → ℝ) (who : iota) :
    quittingDebtTransportLoss before after who -
        quittingDebtTransportGain before after who =
      before who - after who := by
  linarith [quittingDebtTransport_storage_add_loss before after who,
    quittingDebtTransport_storage_add_gain before after who]

omit [DecidableEq iota] in
theorem sum_quittingDebtTransportGain_eq_totalLoss
    (before after : iota → ℝ)
    (hsum : ∑ who, before who = ∑ who, after who) :
    (∑ who, quittingDebtTransportGain before after who) =
      quittingDebtTransportTotalLoss before after := by
  have hzero :
      (∑ who, quittingDebtTransportLoss before after who) -
          (∑ who, quittingDebtTransportGain before after who) = 0 := by
    rw [← Finset.sum_sub_distrib]
    calc
      (∑ who, (quittingDebtTransportLoss before after who -
        quittingDebtTransportGain before after who)) =
          ∑ who, (before who - after who) := by
            apply Finset.sum_congr rfl
            intro who _
            exact quittingDebtTransport_loss_sub_gain before after who
      _ = (∑ who, before who) - ∑ who, after who := by
        rw [Finset.sum_sub_distrib]
      _ = 0 := by rw [hsum]; ring
  unfold quittingDebtTransportTotalLoss
  linarith

omit [DecidableEq iota] in
theorem quittingDebtTransport_eq_self_of_totalLoss_eq_zero
    (before after : iota → ℝ)
    (hsum : ∑ who, before who = ∑ who, after who)
    (hzero : quittingDebtTransportTotalLoss before after = 0) :
    before = after := by
  have hgainZero : (∑ who,
      quittingDebtTransportGain before after who) = 0 := by
    rw [sum_quittingDebtTransportGain_eq_totalLoss before after hsum, hzero]
  funext who
  have hloss : quittingDebtTransportLoss before after who = 0 := by
    apply le_antisymm
    · calc
        quittingDebtTransportLoss before after who ≤
            ∑ player, quittingDebtTransportLoss before after player :=
          Finset.single_le_sum
            (fun player _ ↦ by
              exact le_max_right (before player - after player) 0)
            (Finset.mem_univ who)
        _ = 0 := hzero
    · exact le_max_right _ _
  have hgain : quittingDebtTransportGain before after who = 0 := by
    apply le_antisymm
    · calc
        quittingDebtTransportGain before after who ≤
            ∑ player, quittingDebtTransportGain before after player :=
          Finset.single_le_sum
            (fun player _ ↦ by
              exact le_max_right (after player - before player) 0)
            (Finset.mem_univ who)
        _ = 0 := hgainZero
    · exact le_max_right _ _
  linarith [quittingDebtTransport_storage_add_loss before after who,
    quittingDebtTransport_storage_add_gain before after who]

/-- The canonical lift has the source debts as its row marginals. -/
theorem sum_quittingDebtTransport_recipient
    (before after : iota → ℝ)
    (hsum : ∑ who, before who = ∑ who, after who)
    (sender : iota) :
    (∑ recipient, quittingDebtTransport before after sender recipient) =
      before sender := by
  by_cases hzero : quittingDebtTransportTotalLoss before after = 0
  · simp [quittingDebtTransport, hzero]
  · have hgain := sum_quittingDebtTransportGain_eq_totalLoss before after hsum
    simp only [quittingDebtTransport, hzero, if_false,
      Finset.sum_add_distrib]
    rw [show (∑ recipient,
        if sender = recipient then
          quittingDebtTransportStorage before after sender else 0) =
        quittingDebtTransportStorage before after sender by simp]
    have hcoupling : (∑ recipient,
        quittingDebtTransportLoss before after sender *
          quittingDebtTransportGain before after recipient /
            quittingDebtTransportTotalLoss before after) =
        quittingDebtTransportLoss before after sender := by
      rw [← Finset.sum_div, ← Finset.mul_sum, hgain]
      field_simp
    rw [hcoupling, quittingDebtTransport_storage_add_loss]

/-- The canonical lift has the target debts as its column marginals. -/
theorem sum_quittingDebtTransport_sender
    (before after : iota → ℝ)
    (hsum : ∑ who, before who = ∑ who, after who)
    (recipient : iota) :
    (∑ sender, quittingDebtTransport before after sender recipient) =
      after recipient := by
  by_cases hzero : quittingDebtTransportTotalLoss before after = 0
  · have hsame :=
      quittingDebtTransport_eq_self_of_totalLoss_eq_zero before after hsum
    simp [quittingDebtTransport, hzero, hsame]
  · have hlossGain :=
      sum_quittingDebtTransportGain_eq_totalLoss before after hsum
    simp only [quittingDebtTransport, hzero, if_false,
      Finset.sum_add_distrib]
    rw [show (∑ sender,
        if sender = recipient then
          quittingDebtTransportStorage before after sender else 0) =
        quittingDebtTransportStorage before after recipient by simp]
    have hcoupling : (∑ sender,
        quittingDebtTransportLoss before after sender *
          quittingDebtTransportGain before after recipient /
            quittingDebtTransportTotalLoss before after) =
        quittingDebtTransportGain before after recipient := by
      rw [← Finset.sum_div, ← Finset.sum_mul]
      have hden : (∑ sender,
          quittingDebtTransportLoss before after sender) ≠ 0 := by
        simpa [quittingDebtTransportTotalLoss] using hzero
      unfold quittingDebtTransportTotalLoss
      field_simp [hden]
    rw [hcoupling, quittingDebtTransport_storage_add_gain]

/-- Every lifted transport coefficient is nonnegative. -/
theorem quittingDebtTransport_nonneg
    (before after : iota → ℝ)
    (hbefore : ∀ who, 0 ≤ before who)
    (hafter : ∀ who, 0 ≤ after who)
    (sender recipient : iota) :
    0 ≤ quittingDebtTransport before after sender recipient := by
  by_cases hzero : quittingDebtTransportTotalLoss before after = 0
  · rw [quittingDebtTransport, if_pos hzero]
    split_ifs <;> simp [hbefore]
  · have htotalNonneg : 0 ≤
        quittingDebtTransportTotalLoss before after := by
      unfold quittingDebtTransportTotalLoss
      exact Finset.sum_nonneg fun who _ ↦ le_max_right _ _
    have htotalPos : 0 < quittingDebtTransportTotalLoss before after :=
      lt_of_le_of_ne htotalNonneg (Ne.symm hzero)
    simp only [quittingDebtTransport, hzero, if_false]
    exact add_nonneg
      (by split_ifs <;>
        simp [quittingDebtTransportStorage, hbefore, hafter])
      (div_nonneg
        (mul_nonneg (le_max_right _ _) (le_max_right _ _)) htotalPos.le)

/-- A coordinate which is fully reset emits positive transported debt to a
different coordinate. -/
theorem exists_quittingDebtTransport_pos_of_fullReset
    (before after : iota → ℝ)
    (hsum : ∑ who, before who = ∑ who, after who)
    (who : iota) (hsource : 0 < before who) (htarget : after who = 0) :
    ∃ recipient, recipient ≠ who ∧
      0 < quittingDebtTransport before after who recipient := by
  have hlossWho : quittingDebtTransportLoss before after who = before who := by
    simp [quittingDebtTransportLoss, htarget,
      max_eq_left hsource.le]
  have htotalPos : 0 < quittingDebtTransportTotalLoss before after := by
    unfold quittingDebtTransportTotalLoss
    exact Finset.sum_pos'
      (fun player _ ↦ le_max_right _ _)
      ⟨who, Finset.mem_univ who, by simpa [hlossWho] using hsource⟩
  have hgainTotalPos : 0 < ∑ recipient,
      quittingDebtTransportGain before after recipient := by
    rw [sum_quittingDebtTransportGain_eq_totalLoss before after hsum]
    exact htotalPos
  have hzeroSum : (∑ _recipient : iota, (0 : ℝ)) = 0 := by simp
  obtain ⟨recipient, _hmem, hgainRecipient⟩ :=
    Finset.exists_lt_of_sum_lt
      (show (∑ _recipient : iota, (0 : ℝ)) <
          ∑ recipient, quittingDebtTransportGain before after recipient by
        simpa [hzeroSum] using hgainTotalPos)
  have hrecipientNe : recipient ≠ who := by
    intro heq
    subst recipient
    have hgainWho : quittingDebtTransportGain before after who = 0 := by
      simp [quittingDebtTransportGain, htarget,
        max_eq_right (neg_nonpos.mpr hsource.le)]
    linarith
  refine ⟨recipient, hrecipientNe, ?_⟩
  rw [quittingDebtTransport, if_neg htotalPos.ne',
    if_neg (Ne.symm hrecipientNe), zero_add, hlossWho]
  exact div_pos (mul_pos hsource hgainRecipient) htotalPos

/-- **Game-facing nonnegative lift of a full reset edge.**

On a constant total-debt fiber, a full best-endpoint reset is represented by
a nonnegative player-to-player transport matrix with exact source and target
debt marginals.  Positive debt killed at the mover travels with positive
weight to a different player. -/
theorem stageFullBestEndpoint_zeroFace_nonnegativeDebtLift
    (profile : (quittingGame reward).BehaviorProfile)
    (who : iota) (stage : ℕ)
    (hsourceNonneg : ∀ player, 0 ≤ quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) player)
    (htargetNonneg : ∀ player, 0 ≤ quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (quittingStageFullBestEndpointProfile reward profile who stage)) player)
    (hsource : 0 < quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) who)
    (htarget : quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (quittingStageFullBestEndpointProfile reward profile who stage)) who = 0)
    (hfiber : quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward profile) =
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingStageFullBestEndpointProfile reward profile who stage))) :
    let before := fun player ↦ quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) player
    let after := fun player ↦ quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (quittingStageFullBestEndpointProfile reward profile who stage)) player
    (∀ sender recipient, 0 ≤
        quittingDebtTransport before after sender recipient) ∧
      (∀ sender, (∑ recipient,
          quittingDebtTransport before after sender recipient) = before sender) ∧
      (∀ recipient, (∑ sender,
          quittingDebtTransport before after sender recipient) = after recipient) ∧
      ∃ recipient, recipient ≠ who ∧
        0 < quittingDebtTransport before after who recipient := by
  dsimp only
  let before := fun player ↦ quittingTerminalSemanticDebt
    (quittingTerminalSemanticPair reward profile) player
  let after := fun player ↦ quittingTerminalSemanticDebt
    (quittingTerminalSemanticPair reward
      (quittingStageFullBestEndpointProfile reward profile who stage)) player
  have hsum : ∑ player, before player = ∑ player, after player := by
    exact hfiber
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro sender recipient
    exact quittingDebtTransport_nonneg before after
      hsourceNonneg htargetNonneg sender recipient
  · intro sender
    exact sum_quittingDebtTransport_recipient before after hsum sender
  · intro recipient
    exact sum_quittingDebtTransport_sender before after hsum recipient
  · exact exists_quittingDebtTransport_pos_of_fullReset before after hsum who
      hsource htarget

end GameTheory
