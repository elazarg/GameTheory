/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauDynamicCostate
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauPositivePartSplit
import UniformEquilibrium.Quitting.Cycles.PeriodOneTangentAtlas

/-!
# Unweighted absorption at the maximum-debt scale

The dynamic-costate telescope follows a player of maximal best-response debt,
but its natural charge is debt-weighted.  The terminal positive-part split,
by contrast, produces unweighted opponent-containing mass.  This file closes
that units mismatch.

At a row whose selected current debt is at least `floor`, either the selected
tail debt is large enough to fund opponent absorption directly, or its loss
already forces local Nash defect.  Quantitatively,

`floor * opponentMass <= opponentMass * tailDebt + localDefect`.

Combining this row estimate with the switching-free maximum-debt costate
telescope bounds the entire unweighted selected-opponent clock by one
near-minimality error and twice the selected-coordinate defect occupation.
The factor two records the two logically distinct uses of the same defect:
once to replace the missing tail-debt weight and once in the stopped
costate telescope.

This is an actual-profile theorem.  It does not identify the selected player
with the fixed debtor supplied by a limiting terminal law, and it does not
silently discard singleton absorption by a changing selected owner.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A debt floor converts unweighted opponent absorption into the transported
tail-debt charge plus local Nash defect.  No minimum or Nash premise is used:
if the tail debt lies below the floor, the displayed transport inequality
forces the missing amount into the defect. -/
theorem debtFloor_mul_opponentAbsorptionMass_le_charge_add_nashDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (who : ι) (floor : ℝ)
    (hfloor : floor ≤ quittingTerminalSemanticDebt
      (quittingTerminalSemanticPrefix reward root tail) who)
    (htailDebt : 0 ≤ quittingTerminalSemanticDebt tail who) :
    floor * quittingRootOpponentAbsorptionMass root who ≤
      quittingRootOpponentAbsorptionMass root who *
          quittingTerminalSemanticDebt tail who +
        quittingRootCoordinateNashDefect reward tail.1 root who := by
  let opponent := quittingRootOpponentAbsorptionMass root who
  let tailDebt := quittingTerminalSemanticDebt tail who
  let currentDebt := quittingTerminalSemanticDebt
    (quittingTerminalSemanticPrefix reward root tail) who
  let defect := quittingRootCoordinateNashDefect reward tail.1 root who
  change floor ≤ currentDebt at hfloor
  change 0 ≤ tailDebt at htailDebt
  change floor * opponent ≤ opponent * tailDebt + defect
  have hopponentNonneg : 0 ≤ opponent :=
    quittingRootOpponentAbsorptionMass_nonneg root who
  have hopponentLe : opponent ≤ 1 :=
    quittingRootOpponentAbsorptionMass_le_one root who
  have hdefect : 0 ≤ defect :=
    quittingRootCoordinateNashDefect_nonneg reward tail.1 root who
  have hcharge : opponent * tailDebt ≤ tailDebt - currentDebt + defect := by
    exact quittingRootOpponentAbsorptionMass_mul_debt_le_drift_add_nashDefect
      reward tail root who htailDebt
  by_cases htailFloor : floor ≤ tailDebt
  · have hweighted : floor * opponent ≤ tailDebt * opponent :=
      mul_le_mul_of_nonneg_right htailFloor hopponentNonneg
    nlinarith
  · have htailLt : tailDebt < floor := lt_of_not_ge htailFloor
    have honeMinusNonneg : 0 ≤ 1 - opponent := by linarith
    have htailScaled : (1 - opponent) * tailDebt ≤
        (1 - opponent) * floor :=
      mul_le_mul_of_nonneg_left htailLt.le honeMinusNonneg
    nlinarith

/-- Opponent absorption relative to any fixed player is covered by opponent
absorption relative to a selected player together with the selected player's
own singleton atom.  The latter is the exact event discarded when the
selected coordinate is forced to Continue. -/
theorem quittingRootOpponentAbsorptionMass_le_selected_add_singleton
    (root : ι → PMF Bool) (fixed selected : ι) :
    quittingRootOpponentAbsorptionMass root fixed ≤
      quittingRootOpponentAbsorptionMass root selected +
        quittingRootCoalitionMass root {selected} := by
  have hdecomposition :
      quittingRootAbsorptionMass root =
        quittingRootOpponentAbsorptionMass root selected +
          quittingRootCoalitionMass root {selected} := by
    have hsingleton :=
      quittingRootOpponentContinue_sub_continue_eq_singletonMass root selected
    unfold quittingRootOpponentAbsorptionMass quittingRootAbsorptionMass
    linarith
  rw [← hdecomposition]
  exact quittingRootOpponentAbsorptionMass_le_absorptionMass root fixed

/-- **Unweighted maximum-debt clock.**  Along an actual profile whose shifted
tails are uniformly within `epsilon` of the minimum maximum debt, choose a
maximal debtor at every time.  Its unweighted opponent-absorption occupation,
measured at the positive reference scale, costs at most one `epsilon` plus
twice the local Nash-defect occupation on the same dynamically selected
coordinates.

Thus loss of the selected debt before an absorbing row is not a third
residual: it is already collectible local defect. -/
theorem exists_maxDebtSelector_reference_mul_sum_opponentAbsorptionMass_le
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (reference epsilon : ℝ) (cutoff : ℕ) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hfloor : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      reference ≤ quittingTerminalSemanticExploitability candidate)
    (hnear : ∀ time ≤ cutoff,
      quittingTerminalSemanticExploitability
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward profile time)) ≤
        reference + epsilon) :
    ∃ owner : ℕ → ι,
      (∀ time who,
        quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (quittingAllContinueProfileSpine reward profile time)) who ≤
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (quittingAllContinueProfileSpine reward profile time))
            (owner time)) ∧
      reference *
          (∑ time ∈ Finset.range cutoff,
            quittingLiveMass reward profile time *
              quittingRootOpponentAbsorptionMass
                (quittingProfileLiveRoot reward profile time) (owner time)) ≤
        epsilon + 2 *
          ∑ time ∈ Finset.range cutoff,
            quittingLiveMass reward profile time *
              quittingRootCoordinateNashDefect reward
                (quittingTerminalSemanticPair reward
                  (quittingAllContinueProfileSpine
                    reward profile (time + 1))).1
                (quittingProfileLiveRoot reward profile time) (owner time) := by
  obtain ⟨owner, howner, hweighted⟩ :=
    exists_maxDebtSelector_sum_liveMass_mul_charge_le_epsilon_add_defect
      reward profile reference epsilon cutoff hM hreward hfloor hnear
  refine ⟨owner, howner, ?_⟩
  have hrow : ∀ time,
      reference * quittingRootOpponentAbsorptionMass
          (quittingProfileLiveRoot reward profile time) (owner time) ≤
        quittingRootOpponentAbsorptionMass
            (quittingProfileLiveRoot reward profile time) (owner time) *
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (quittingAllContinueProfileSpine reward profile (time + 1)))
            (owner time) +
          quittingRootCoordinateNashDefect reward
            (quittingTerminalSemanticPair reward
              (quittingAllContinueProfileSpine
                reward profile (time + 1))).1
            (quittingProfileLiveRoot reward profile time) (owner time) := by
    intro time
    let tail := quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (time + 1))
    let current := quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile time)
    let root := quittingProfileLiveRoot reward profile time
    have hprefix : current = quittingTerminalSemanticPrefix reward root tail :=
      quittingTerminalSemanticPair_spine_eq_prefix
        reward profile time hM hreward
    have hcurrentFloor : reference ≤
        quittingTerminalSemanticDebt current (owner time) := by
      have hcurrentCarrier : current ∈ quittingTerminalSemanticCarrier reward :=
        quittingTerminalSemanticPair_mem_carrier reward _
      have hcurrentDebt : ∀ who,
          0 ≤ quittingTerminalSemanticDebt current who :=
        quittingTerminalSemanticDebt_nonneg_of_mem_carrier
          reward hM hreward hcurrentCarrier
      have hcurrentMax : quittingTerminalSemanticExploitability current =
          quittingTerminalSemanticDebt current (owner time) :=
        quittingTerminalSemanticExploitability_eq_debt_of_maximizer
          current (owner time) hcurrentDebt (howner time)
      rw [← hcurrentMax]
      exact hfloor current hcurrentCarrier
    have htailCarrier : tail ∈ quittingTerminalSemanticCarrier reward :=
      quittingTerminalSemanticPair_mem_carrier reward _
    have htailDebt : 0 ≤ quittingTerminalSemanticDebt tail (owner time) :=
      quittingTerminalSemanticDebt_nonneg_of_mem_carrier
        reward hM hreward htailCarrier (owner time)
    rw [hprefix] at hcurrentFloor
    exact debtFloor_mul_opponentAbsorptionMass_le_charge_add_nashDefect
      reward tail root (owner time) reference hcurrentFloor htailDebt
  have hliveRow : ∀ time,
      quittingLiveMass reward profile time *
          (reference * quittingRootOpponentAbsorptionMass
            (quittingProfileLiveRoot reward profile time) (owner time)) ≤
        quittingLiveMass reward profile time *
          (quittingRootOpponentAbsorptionMass
              (quittingProfileLiveRoot reward profile time) (owner time) *
            quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward
                (quittingAllContinueProfileSpine reward profile (time + 1)))
              (owner time) +
            quittingRootCoordinateNashDefect reward
              (quittingTerminalSemanticPair reward
                (quittingAllContinueProfileSpine
                  reward profile (time + 1))).1
              (quittingProfileLiveRoot reward profile time) (owner time)) := by
    intro time
    exact mul_le_mul_of_nonneg_left (hrow time)
      (quittingLiveMass_nonneg reward profile time)
  have hsum := Finset.sum_le_sum fun time
      (_htime : time ∈ Finset.range cutoff) => hliveRow time
  have hsum' : reference *
        (∑ time ∈ Finset.range cutoff,
          quittingLiveMass reward profile time *
            quittingRootOpponentAbsorptionMass
              (quittingProfileLiveRoot reward profile time) (owner time)) ≤
      (∑ time ∈ Finset.range cutoff,
        quittingLiveMass reward profile time *
          (quittingRootOpponentAbsorptionMass
              (quittingProfileLiveRoot reward profile time) (owner time) *
            quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward
                (quittingAllContinueProfileSpine reward profile (time + 1)))
              (owner time))) +
        ∑ time ∈ Finset.range cutoff,
          quittingLiveMass reward profile time *
            quittingRootCoordinateNashDefect reward
              (quittingTerminalSemanticPair reward
                (quittingAllContinueProfileSpine
                  reward profile (time + 1))).1
              (quittingProfileLiveRoot reward profile time) (owner time) := by
    calc
      reference *
          (∑ time ∈ Finset.range cutoff,
            quittingLiveMass reward profile time *
              quittingRootOpponentAbsorptionMass
                (quittingProfileLiveRoot reward profile time) (owner time)) =
          ∑ time ∈ Finset.range cutoff,
            quittingLiveMass reward profile time *
              (reference * quittingRootOpponentAbsorptionMass
                (quittingProfileLiveRoot reward profile time) (owner time)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro time _htime
            ring
      _ ≤ _ := hsum
      _ = _ := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib]
  linarith

/-- **Fixed-debtor/max-debt alternative.**  The opponent clock of any fixed
player is reduced, on the same actual profile, to two quantities:

* local Nash defects on the currently maximal-debt coordinate; and
* singleton absorption by that maximal-debt owner.

The first term is collectible by the maximum-debt costate telescope.  The
second is the precise unmatched event: it is not opponent absorption for the
selected owner, even when it is opponent-containing for the fixed player.
No player switch or coalition mass is dropped. -/
theorem exists_maxDebtSelector_reference_mul_fixedOpponentClock_le
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (fixed : ι) (reference epsilon : ℝ) (cutoff : ℕ) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hreference : 0 ≤ reference)
    (hfloor : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      reference ≤ quittingTerminalSemanticExploitability candidate)
    (hnear : ∀ time ≤ cutoff,
      quittingTerminalSemanticExploitability
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward profile time)) ≤
        reference + epsilon) :
    ∃ owner : ℕ → ι,
      (∀ time who,
        quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (quittingAllContinueProfileSpine reward profile time)) who ≤
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (quittingAllContinueProfileSpine reward profile time))
            (owner time)) ∧
      reference *
          (∑ time ∈ Finset.range cutoff,
            quittingLiveMass reward profile time *
              quittingRootOpponentAbsorptionMass
                (quittingProfileLiveRoot reward profile time) fixed) ≤
        epsilon + 2 *
            (∑ time ∈ Finset.range cutoff,
              quittingLiveMass reward profile time *
                quittingRootCoordinateNashDefect reward
                  (quittingTerminalSemanticPair reward
                    (quittingAllContinueProfileSpine
                      reward profile (time + 1))).1
                  (quittingProfileLiveRoot reward profile time) (owner time)) +
          reference *
            ∑ time ∈ Finset.range cutoff,
              quittingLiveMass reward profile time *
                quittingRootCoalitionMass
                  (quittingProfileLiveRoot reward profile time) {owner time} := by
  obtain ⟨owner, howner, hselected⟩ :=
    exists_maxDebtSelector_reference_mul_sum_opponentAbsorptionMass_le
      reward profile reference epsilon cutoff hM hreward hfloor hnear
  refine ⟨owner, howner, ?_⟩
  have hrow : ∀ time,
      quittingLiveMass reward profile time *
          quittingRootOpponentAbsorptionMass
            (quittingProfileLiveRoot reward profile time) fixed ≤
        quittingLiveMass reward profile time *
          (quittingRootOpponentAbsorptionMass
              (quittingProfileLiveRoot reward profile time) (owner time) +
            quittingRootCoalitionMass
              (quittingProfileLiveRoot reward profile time) {owner time}) := by
    intro time
    exact mul_le_mul_of_nonneg_left
      (quittingRootOpponentAbsorptionMass_le_selected_add_singleton
        (quittingProfileLiveRoot reward profile time) fixed (owner time))
      (quittingLiveMass_nonneg reward profile time)
  have hsum := Finset.sum_le_sum fun time
      (_htime : time ∈ Finset.range cutoff) => hrow time
  have hsplit :
      (∑ time ∈ Finset.range cutoff,
        quittingLiveMass reward profile time *
          (quittingRootOpponentAbsorptionMass
              (quittingProfileLiveRoot reward profile time) (owner time) +
            quittingRootCoalitionMass
              (quittingProfileLiveRoot reward profile time) {owner time})) =
        (∑ time ∈ Finset.range cutoff,
          quittingLiveMass reward profile time *
            quittingRootOpponentAbsorptionMass
              (quittingProfileLiveRoot reward profile time) (owner time)) +
          ∑ time ∈ Finset.range cutoff,
            quittingLiveMass reward profile time *
              quittingRootCoalitionMass
                (quittingProfileLiveRoot reward profile time) {owner time} := by
    simp_rw [mul_add]
    exact Finset.sum_add_distrib
  rw [hsplit] at hsum
  have hscaled := mul_le_mul_of_nonneg_left hsum hreference
  linarith

end GameTheory
