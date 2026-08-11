/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetReprojectionTwoFaceBridge

/-!
# Full reset words on a positive minimum fiber

A reached-row best-endpoint move can land on its mover's zero-debt face only
at unit weight.  This file records what a finite word of those exceptional
moves gives when every displayed semantic state stays on one total-debt
fiber.

Each literal move exhausts the mover's source debt, transfers exactly that
amount to the opposite player face, and routes every positive marked
coalition through the corresponding Boolean-cube edge.  On a closed word the
signed debt change of every fixed player telescopes to zero.  Hence the word
is an exact positive circulation of best-response debt.

The circulation is signed: the aggregate opposite-face transfer is positive,
but a recipient can later lose the same debt when it becomes a mover.  Thus
player-label recurrence plus the exact transfer account does not by itself
produce a monotone return or a punishment orientation.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {reward : {S : Finset iota // S.Nonempty} → Payoff iota}

/-- The literal profile obtained by making the full reached-row
best-endpoint move. -/
def quittingStageFullBestEndpointProfile
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : iota) (stage : ℕ) :
    (quittingGame reward).BehaviorProfile :=
  Function.update profile who
    (quittingStagePartialBestEndpointBehaviorDeviation
      reward profile who stage 1 zero_le_one le_rfl)

omit [Fintype iota] [DecidableEq iota] in
/-- At unit weight the fractional endpoint marginal is the selected pure
endpoint. -/
theorem quittingPartialEndpointMarginal_one_eq_pure
    (root : iota → PMF Bool) (who : iota) (action : Bool) :
    quittingPartialEndpointMarginal root who action 1 zero_le_one le_rfl =
      PMF.pure action := by
  apply PMF.ext
  intro value
  apply (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  cases value <;> simp

/-- The reached root of the literal full move is the pure endpoint update of
the source reached root. -/
theorem quittingProfileLiveRoot_stageFullBestEndpointProfile_self
    (profile : (quittingGame reward).BehaviorProfile)
    (who : iota) (stage : ℕ) :
    quittingProfileLiveRoot reward
        (quittingStageFullBestEndpointProfile reward profile who stage) stage =
      Function.update (quittingProfileLiveRoot reward profile stage) who
        (PMF.pure
          (quittingRootBestEndpointAction reward
            (quittingTerminalSemanticPair reward
              (quittingAllContinueProfileSpine reward profile
                (stage + 1))).1
            (quittingProfileLiveRoot reward profile stage) who)) := by
  rw [quittingStageFullBestEndpointProfile,
    quittingProfileLiveRoot_stagePartialBestEndpoint_self]
  unfold quittingPartialEndpointRoot
  rw [quittingPartialEndpointMarginal_one_eq_pure]

/-- A positive marked stage cylinder is routed with positive mass by the
literal full move. -/
theorem stageCoalitionMass_pos_routed_of_stageFullBestEndpoint
    (profile : (quittingGame reward).BehaviorProfile)
    (who : iota) (stage : ℕ)
    (terminal : {S : Finset iota // S.Nonempty})
    (hstage : 0 < quittingStageCoalitionMass reward profile stage terminal) :
    let action := quittingRootBestEndpointAction reward
      (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward profile (stage + 1))).1
      (quittingProfileLiveRoot reward profile stage) who
    let routed := quittingPureEndpointRoutedCoalition terminal.val who action
    0 < quittingRootCoalitionMass
      (quittingProfileLiveRoot reward
        (quittingStageFullBestEndpointProfile reward profile who stage) stage)
      routed := by
  dsimp only
  have hroot : 0 < quittingRootCoalitionMass
      (quittingProfileLiveRoot reward profile stage) terminal.val := by
    rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass] at hstage
    rcases mul_pos_iff.mp hstage with hpositive | hnegative
    · exact hpositive.2
    · exact (not_lt_of_ge
        (quittingLiveMass_nonneg reward profile stage) hnegative.1).elim
  rw [quittingProfileLiveRoot_stageFullBestEndpointProfile_self]
  exact hroot.trans_le
    (quittingRootCoalitionMass_le_pureEndpointRouted
      (quittingProfileLiveRoot reward profile stage) terminal.val who _)

/-- One full zero-face landing on a constant total-debt fiber has the exact
unit-reset account. -/
theorem stageFullBestEndpoint_zeroFace_exact_transfer
    (profile : (quittingGame reward).BehaviorProfile)
    (who : iota) (stage : ℕ)
    (hzero : quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (quittingStageFullBestEndpointProfile reward profile who stage)) who = 0)
    (hfiber : quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (quittingStageFullBestEndpointProfile reward profile who stage)) =
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward profile)) :
    quittingLiveMass reward profile stage *
          quittingRootCoordinateNashDefect reward
            (quittingTerminalSemanticPair reward
              (quittingAllContinueProfileSpine reward profile
                (stage + 1))).1
            (quittingProfileLiveRoot reward profile stage) who =
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) who ∧
      (∑ recipient ∈ Finset.univ.erase who,
          quittingTerminalSemanticDebtChange
            (quittingTerminalSemanticPair reward profile)
            (quittingTerminalSemanticPair reward
              (quittingStageFullBestEndpointProfile
                reward profile who stage)) recipient) =
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) who := by
  let source := quittingTerminalSemanticPair reward profile
  let target := quittingTerminalSemanticPair reward
    (quittingStageFullBestEndpointProfile reward profile who stage)
  have hdecrease := quittingTerminalSemanticDebt_stagePartialBestEndpoint_eq
    reward profile who stage 1 zero_le_one le_rfl
  dsimp only at hdecrease
  change quittingTerminalSemanticDebt target who =
      quittingTerminalSemanticDebt source who -
        1 * quittingLiveMass reward profile stage *
          quittingRootCoordinateNashDefect reward
            (quittingTerminalSemanticPair reward
              (quittingAllContinueProfileSpine reward profile
                (stage + 1))).1
            (quittingProfileLiveRoot reward profile stage) who at hdecrease
  have hgain : quittingLiveMass reward profile stage *
        quittingRootCoordinateNashDefect reward
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward profile
              (stage + 1))).1
          (quittingProfileLiveRoot reward profile stage) who =
      quittingTerminalSemanticDebt source who := by
    dsimp only [source] at hdecrease ⊢
    rw [hzero] at hdecrease
    norm_num at hdecrease
    linarith
  have htransfer :=
    sum_opponent_debtChange_eq_totalChange_add_sourceDebt_of_target_zero
      source target who hzero
  have htotal : quittingTerminalSemanticDebtSum target =
      quittingTerminalSemanticDebtSum source := by
    exact hfiber
  refine ⟨hgain, ?_⟩
  change (∑ recipient ∈ Finset.univ.erase who,
      quittingTerminalSemanticDebtChange source target recipient) =
    quittingTerminalSemanticDebt source who
  rw [htransfer, htotal]
  ring

/-! ## Closed finite words -/

omit [Fintype iota] [DecidableEq iota] in
/-- The signed change of one fixed debt coordinate telescopes along a finite
semantic word. -/
theorem sum_range_terminalSemanticDebtChange
    (pair : ℕ → QuittingTerminalSemanticPair iota)
    (length : ℕ) (who : iota) :
    (∑ time ∈ Finset.range length,
        quittingTerminalSemanticDebtChange
          (pair time) (pair (time + 1)) who) =
      quittingTerminalSemanticDebt (pair length) who -
        quittingTerminalSemanticDebt (pair 0) who := by
  unfold quittingTerminalSemanticDebtChange
  let value : ℕ → ℝ := fun time ↦
    quittingTerminalSemanticDebt (pair time) who
  have htelescope := Finset.sum_range_sub' value length
  calc
    (∑ time ∈ Finset.range length,
        (quittingTerminalSemanticDebt (pair (time + 1)) who -
          quittingTerminalSemanticDebt (pair time) who)) =
        -(∑ time ∈ Finset.range length,
          (value time - value (time + 1))) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro time _
      dsimp only [value]
      ring
    _ = -(value 0 - value length) := by rw [htelescope]
    _ = quittingTerminalSemanticDebt (pair length) who -
        quittingTerminalSemanticDebt (pair 0) who := by
      dsimp only [value]
      ring

/-- **Positive-minimum unit-reset circulation.**

Consider a finite literal word of full reached-row best-endpoint moves.  If
every target kills the mover's positive source debt, all displayed states
stay on the same total-debt fiber `D`, and the word closes semantically, then

* every row's full gain exhausts its source debt;
* every row transfers exactly that debt to the opposite player face;
* the aggregate transferred amount is strictly positive; and
* every fixed player's signed debt change around the word is zero.

The last two conclusions coexist: positive reset transfers form a signed
circulation and can be canceled by later losses of their recipients.  This is
the precise algebraic obstruction to treating repeated mover labels as a
monotone reset return. -/
theorem finite_stageFullBestEndpoint_cycle_signedCirculation
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (mover : ℕ → iota) (stage : ℕ → ℕ)
    (terminal : ℕ → {S : Finset iota // S.Nonempty})
    (length : ℕ) (D : ℝ)
    (hlength : 0 < length) (_hD : 0 < D)
    (hstep : ∀ time < length,
      profiles (time + 1) = quittingStageFullBestEndpointProfile
        reward (profiles time) (mover time) (stage time))
    (hsource : ∀ time < length, 0 < quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward (profiles time)) (mover time))
    (htarget : ∀ time < length, quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward (profiles (time + 1)))
        (mover time) = 0)
    (hmarked : ∀ time < length, 0 < quittingStageCoalitionMass reward
      (profiles time) (stage time) (terminal time))
    (hfiber : ∀ time ≤ length, quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward (profiles time)) = D)
    (hclosed : quittingTerminalSemanticPair reward (profiles length) =
      quittingTerminalSemanticPair reward (profiles 0)) :
    (∀ time < length,
      quittingLiveMass reward (profiles time) (stage time) *
            quittingRootCoordinateNashDefect reward
              (quittingTerminalSemanticPair reward
                (quittingAllContinueProfileSpine reward (profiles time)
                  (stage time + 1))).1
              (quittingProfileLiveRoot reward (profiles time) (stage time))
              (mover time) =
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward (profiles time))
            (mover time) ∧
        (∑ recipient ∈ Finset.univ.erase (mover time),
            quittingTerminalSemanticDebtChange
              (quittingTerminalSemanticPair reward (profiles time))
              (quittingTerminalSemanticPair reward (profiles (time + 1)))
              recipient) =
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward (profiles time))
            (mover time)) ∧
      (∀ time < length,
        let action := quittingRootBestEndpointAction reward
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward (profiles time)
              (stage time + 1))).1
          (quittingProfileLiveRoot reward (profiles time) (stage time))
          (mover time)
        let routed := quittingPureEndpointRoutedCoalition
          (terminal time).val (mover time) action
        0 < quittingRootCoalitionMass
          (quittingProfileLiveRoot reward (profiles (time + 1)) (stage time))
          routed) ∧
      0 < ∑ time ∈ Finset.range length,
        ∑ recipient ∈ Finset.univ.erase (mover time),
          quittingTerminalSemanticDebtChange
            (quittingTerminalSemanticPair reward (profiles time))
            (quittingTerminalSemanticPair reward (profiles (time + 1)))
            recipient ∧
      ∀ who, (∑ time ∈ Finset.range length,
        quittingTerminalSemanticDebtChange
          (quittingTerminalSemanticPair reward (profiles time))
          (quittingTerminalSemanticPair reward (profiles (time + 1))) who) = 0 := by
  let pair : ℕ → QuittingTerminalSemanticPair iota := fun time ↦
    quittingTerminalSemanticPair reward (profiles time)
  have hedge : ∀ time < length,
      quittingLiveMass reward (profiles time) (stage time) *
            quittingRootCoordinateNashDefect reward
              (quittingTerminalSemanticPair reward
                (quittingAllContinueProfileSpine reward (profiles time)
                  (stage time + 1))).1
              (quittingProfileLiveRoot reward (profiles time) (stage time))
              (mover time) =
          quittingTerminalSemanticDebt (pair time) (mover time) ∧
        (∑ recipient ∈ Finset.univ.erase (mover time),
            quittingTerminalSemanticDebtChange
              (pair time) (pair (time + 1)) recipient) =
          quittingTerminalSemanticDebt (pair time) (mover time) := by
    intro time htime
    have hstepTime := hstep time htime
    have hzero : quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingStageFullBestEndpointProfile reward (profiles time)
            (mover time) (stage time))) (mover time) = 0 := by
      rw [← hstepTime]
      exact htarget time htime
    have hfiberTime : quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingStageFullBestEndpointProfile reward (profiles time)
            (mover time) (stage time))) =
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward (profiles time)) := by
      rw [← hstepTime, hfiber (time + 1) (Nat.succ_le_iff.mpr htime),
        hfiber time (Nat.le_of_lt htime)]
    have haccount := stageFullBestEndpoint_zeroFace_exact_transfer
      (reward := reward) (profiles time) (mover time) (stage time)
        hzero hfiberTime
    simpa only [pair, hstepTime] using haccount
  refine ⟨hedge, ?_, ?_, ?_⟩
  · intro time htime
    dsimp only
    rw [hstep time htime]
    exact stageCoalitionMass_pos_routed_of_stageFullBestEndpoint
      (reward := reward) (profiles time) (mover time) (stage time)
        (terminal time) (hmarked time htime)
  · have hrewrite : (∑ time ∈ Finset.range length,
        ∑ recipient ∈ Finset.univ.erase (mover time),
          quittingTerminalSemanticDebtChange
            (pair time) (pair (time + 1)) recipient) =
      ∑ time ∈ Finset.range length,
        quittingTerminalSemanticDebt (pair time) (mover time) := by
      apply Finset.sum_congr rfl
      intro time htime
      exact (hedge time (Finset.mem_range.mp htime)).2
    rw [show (∑ time ∈ Finset.range length,
        ∑ recipient ∈ Finset.univ.erase (mover time),
          quittingTerminalSemanticDebtChange
            (quittingTerminalSemanticPair reward (profiles time))
            (quittingTerminalSemanticPair reward (profiles (time + 1)))
            recipient) =
        ∑ time ∈ Finset.range length,
          ∑ recipient ∈ Finset.univ.erase (mover time),
            quittingTerminalSemanticDebtChange
              (pair time) (pair (time + 1)) recipient by rfl,
      hrewrite]
    exact Finset.sum_pos' (fun time htime ↦
      (hsource time (Finset.mem_range.mp htime)).le)
      ⟨0, Finset.mem_range.mpr hlength,
        hsource 0 hlength⟩
  · intro who
    have htelescope := sum_range_terminalSemanticDebtChange pair length who
    have hpairClosed : pair length = pair 0 := hclosed
    rw [hpairClosed] at htelescope
    simpa only [pair, sub_self] using htelescope

end GameTheory
