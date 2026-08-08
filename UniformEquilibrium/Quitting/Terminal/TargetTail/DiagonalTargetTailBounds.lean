/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Terminal.TargetTail.DiagonalTargetTailSemantics

/-!
# Diagonal target-tail pointwise bounds

A matched target coordinate has zero gain: its suffix is already closed and
its diagonal boundary is exact.  Every non-target coordinate pays at most
`4 * M` times its opponent-only survival through the finite prefix: `2 * M`
for suffix best-response debt and `2 * M` for changing from its diagonal
anchor to the selected target's actual suffix payoff.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]


/-- With a matched, closed target coordinate, the target has no profitable
deviation through the exact prefix, regardless of its opponent-survival
probability. -/
theorem quittingPhaseSwitchTargetHazardGap_le_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan tail : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (target : ι) (hazard : ℕ → PMF Bool) (switch : ℕ)
    (hpolicy : ∀ time, time < switch →
      value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (plan time))
    (hnash : ∀ time, time < switch →
      IsεQuittingRootNash reward (value (time + 1)) 0 (plan time))
    (hmatch : value switch target =
      quittingRootSequenceTerminalValue reward tail target 0)
    (hclosed : IsQuittingTargetClosedAt reward tail target 0) :
    quittingRootSequenceHazardTerminalValue reward
          (quittingPhaseSwitchRoots plan tail switch) target hazard 0 -
        quittingRootSequenceTerminalValue reward
          (quittingPhaseSwitchRoots plan tail switch) target 0 ≤ 0 := by
  let tailDeviation :=
    quittingRootSequenceHazardTerminalValue reward tail target
      (fun offset => hazard (switch + offset)) 0
  let tailPayoff := quittingRootSequenceTerminalValue reward tail target 0
  have htail : tailDeviation ≤ tailPayoff := hclosed _
  have hdeviation := quittingRootSequenceHazardTerminalValue_phaseSwitch_eq_finite
    reward plan tail switch target hazard
  have hprescribed := quittingRootSequenceTerminalValue_phaseSwitch_eq_finite
    reward plan tail switch target
  have hfinite := quittingFiniteTerminalHazardValue_le_bestResponse
    reward plan target hazard tailDeviation 0 switch
  have hmono := quittingFiniteTerminalBestResponseValue_mono_terminal
    reward plan target htail 0 switch
  have hprefix :=
    quittingFiniteTerminalBestResponseValue_le_declared_add_survival
      reward plan value target switch (terminalDebt := 0) le_rfl
      hpolicy hnash 0 switch (by omega)
  have hself := quittingFiniteTerminalHazardValue_self_eq_declared
    reward plan value target switch hpolicy 0 switch (by omega)
  simp only [Nat.zero_add, mul_zero, add_zero] at hprefix
  rw [hmatch] at hprefix
  simp only [Nat.zero_add] at hself
  rw [hmatch] at hself
  rw [hdeviation, hprescribed]
  linarith

/-- For any non-target coordinate, changing from its diagonal endpoint to the
selected target's actual suffix costs at most another `2*M` times survival.
Together with the propagated suffix best-response debt this gives
`4*M*O_who`. -/
theorem quittingPhaseSwitchHazardGap_le_four_mul_opponentSurvival
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (plan tail : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (who : ι) (hazard : ℕ → PMF Bool) (switch : ℕ)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hvalueBound : |value switch who| ≤ M)
    (hpolicy : ∀ time, time < switch →
      value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (plan time))
    (hnash : ∀ time, time < switch →
      IsεQuittingRootNash reward (value (time + 1)) 0 (plan time)) :
    quittingRootSequenceHazardTerminalValue reward
          (quittingPhaseSwitchRoots plan tail switch) who hazard 0 -
        quittingRootSequenceTerminalValue reward
          (quittingPhaseSwitchRoots plan tail switch) who 0 ≤
      4 * M * quittingOpponentSurvivalWeight plan who 0 switch := by
  let tailDeviation :=
    quittingRootSequenceHazardTerminalValue reward tail who
      (fun offset => hazard (switch + offset)) 0
  let tailPayoff := quittingRootSequenceTerminalValue reward tail who 0
  let anchor := value switch who
  let boundary := max anchor (max tailPayoff tailDeviation)
  let debt := boundary - anchor
  have htailDeviation : |tailDeviation| ≤ M := by
    dsimp only [tailDeviation]
    unfold quittingRootSequenceHazardTerminalValue
    exact abs_quittingRootSequenceTerminalValue_le reward
      (quittingRootSequenceUpdate tail who
        (fun offset => hazard (switch + offset))) who 0 hM hreward
  have htailPayoff : |tailPayoff| ≤ M := by
    dsimp only [tailPayoff]
    exact abs_quittingRootSequenceTerminalValue_le reward tail who 0 hM hreward
  rw [abs_le] at htailDeviation htailPayoff hvalueBound
  have hboundaryUpper : boundary ≤ M := by
    exact max_le hvalueBound.2 (max_le htailPayoff.2 htailDeviation.2)
  have hanchorLower : -M ≤ anchor := hvalueBound.1
  have hdebt0 : 0 ≤ debt := by
    exact sub_nonneg.mpr (le_max_left _ _)
  have hdebtBound : debt ≤ 2 * M := by
    dsimp only [debt]
    linarith
  have htailBoundary : tailDeviation ≤ boundary :=
    le_trans (le_max_right tailPayoff tailDeviation) (le_max_right anchor _)
  have hdeviation := quittingRootSequenceHazardTerminalValue_phaseSwitch_eq_finite
    reward plan tail switch who hazard
  have hprescribed := quittingRootSequenceTerminalValue_phaseSwitch_eq_finite
    reward plan tail switch who
  have hfinite := quittingFiniteTerminalHazardValue_le_bestResponse
    reward plan who hazard tailDeviation 0 switch
  have hmono := quittingFiniteTerminalBestResponseValue_mono_terminal
    reward plan who htailBoundary 0 switch
  have hprefix :=
    quittingFiniteTerminalBestResponseValue_le_declared_add_survival
      reward plan value who switch hdebt0 hpolicy hnash 0 switch (by omega)
  have hboundaryEq : anchor + debt = boundary := by
    dsimp only [debt]
    ring
  simp only [Nat.zero_add] at hprefix
  rw [hboundaryEq] at hprefix
  have hopponent0 := quittingOpponentSurvivalWeight_nonneg plan who 0 switch
  have hprefixBound :
      quittingFiniteTerminalBestResponseValue reward plan who boundary 0 switch ≤
        value 0 who +
          quittingOpponentSurvivalWeight plan who 0 switch * (2 * M) := by
    have hscaledDebt :=
      mul_le_mul_of_nonneg_left hdebtBound hopponent0
    exact hprefix.trans (by linarith)
  have hself := quittingFiniteTerminalHazardValue_self_eq_declared
    reward plan value who switch hpolicy 0 switch (by omega)
  simp only [Nat.zero_add] at hself
  have haffine := quittingFiniteTerminalHazardValue_add
    reward plan who (fun time => plan time who) anchor (tailPayoff - anchor)
      0 switch
  have htailBoundaryEq : anchor + (tailPayoff - anchor) = tailPayoff := by ring
  rw [htailBoundaryEq, hself] at haffine
  have hfull :
      quittingFiniteFullSurvivalWeight plan who
          (fun time => plan time who) 0 switch =
        quittingJointSurvivalWeight plan 0 switch := by
    rw [quittingFiniteFullSurvivalWeight_self_eq_product,
      quittingJointSurvivalWeight_eq_prod]
  rw [hfull] at haffine
  have hjoint0 := quittingJointSurvivalWeight_nonneg plan 0 switch
  have hjointOpponent :=
    quittingJointSurvivalWeight_le_quittingOpponentSurvivalWeight
      plan who 0 switch
  have hgapBound : anchor - tailPayoff ≤ 2 * M := by
    linarith
  have hloss :
      value 0 who -
          quittingFiniteTerminalHazardValue reward plan who
            (fun time => plan time who) tailPayoff 0 switch ≤
        quittingOpponentSurvivalWeight plan who 0 switch * (2 * M) := by
    have hscaled :
        quittingJointSurvivalWeight plan 0 switch * (anchor - tailPayoff) ≤
          quittingOpponentSurvivalWeight plan who 0 switch * (2 * M) := by
      calc
        quittingJointSurvivalWeight plan 0 switch * (anchor - tailPayoff) ≤
            quittingJointSurvivalWeight plan 0 switch * (2 * M) :=
          mul_le_mul_of_nonneg_left hgapBound hjoint0
        _ ≤ quittingOpponentSurvivalWeight plan who 0 switch * (2 * M) :=
          mul_le_mul_of_nonneg_right hjointOpponent (by positivity)
    rw [haffine]
    nlinarith
  rw [hdeviation, hprescribed]
  have hdev := hfinite.trans (hmono.trans hprefixBound)
  nlinarith

end GameTheory
