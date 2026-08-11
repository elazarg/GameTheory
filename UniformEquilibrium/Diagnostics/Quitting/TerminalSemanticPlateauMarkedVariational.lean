/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauDefectCharge
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauTightness

/-!
# A marked first-order row on the all-Continue semantic plateau

The pure-time terminal-law argument resets one player's best-response debt.
In the collision branch, the selected profitable terminal atom occurs exactly
at that player's deterministic Quit date.  This makes the reset quantitative
at the same chronological row:

`terminal atom mass * marked-player root defect <= reset-profile debt`.

Consequently, if the atom keeps a fixed positive mass while the reset debt
vanishes, the marked player's local root defect at the selected row vanishes.
This is a same-profile, time-local first-order bridge.  It does not assert
that the other players' root defects vanish, so the limiting marked row is
not yet an exact Nash root.
-/

noncomputable section

namespace GameTheory

open Filter StochasticGame Math.Probability Math.PMFProduct
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## A pointwise marked collision estimate -/

/-- A stage coalition mass is no larger than the probability of reaching
that live row. -/
theorem quittingStageCoalitionMass_le_liveMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) :
    quittingStageCoalitionMass reward profile time terminal ≤
      quittingLiveMass reward profile time := by
  have hrowNonneg :=
    quittingLiveRowCoalitionMass_nonneg reward profile time terminal
  have hrowLe : quittingLiveRowCoalitionMass reward profile time terminal ≤ 1 := by
    unfold quittingLiveRowCoalitionMass
    exact ENNReal.toReal_mono ENNReal.one_ne_top
      (PMF.coe_le_one
        ((quittingGame reward).stageActionDist profile
          (quittingLiveHist reward time))
        (quittingTerminalCoalitionAction terminal))
  unfold quittingStageCoalitionMass
  exact mul_le_of_le_one_right
    (quittingLiveMass_nonneg reward profile time) hrowLe

/-- At a finite pure-time Quit date, the mass of any terminal coalition
containing the deviator, multiplied by that player's local one-stage Nash
defect, is bounded by the deviated profile's initial semantic debt.

The terminal atom and the local defect belong to the very same executable
profile and the very same chronological row. -/
theorem quittingTerminalOutcomeMass_mul_coordinateNashDefect_at_pureTime_stop_le_debt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (stop : ℕ)
    (terminal : {S : Finset ι // S.Nonempty})
    (hmem : who ∈ terminal.val)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ outcome player, |reward outcome player| ≤ M) :
    let deviated := Function.update profile who
      (quittingPureTimeBehaviorStrategy reward who (some stop))
    quittingTerminalOutcomeMass reward deviated (some terminal) *
        quittingRootCoordinateNashDefect reward
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward deviated (stop + 1))).1
          (quittingProfileLiveRoot reward deviated stop) who ≤
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward deviated) who := by
  dsimp only
  let deviated := Function.update profile who
    (quittingPureTimeBehaviorStrategy reward who (some stop))
  let defect := quittingRootCoordinateNashDefect reward
    (quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward deviated (stop + 1))).1
    (quittingProfileLiveRoot reward deviated stop) who
  have hmassEq : quittingTerminalOutcomeMass reward deviated (some terminal) =
      quittingStageCoalitionMass reward deviated stop terminal := by
    exact quittingTerminalOutcomeMass_update_pureTime_some_mem_eq_at
      reward profile who stop terminal hmem
  have hmassLe : quittingStageCoalitionMass reward deviated stop terminal ≤
      quittingLiveMass reward deviated stop :=
    quittingStageCoalitionMass_le_liveMass reward deviated stop terminal
  have hdefectNonneg : 0 ≤ defect := by
    exact quittingRootCoordinateNashDefect_nonneg reward _ _ who
  have hscaled : quittingStageCoalitionMass reward deviated stop terminal *
      defect ≤ quittingLiveMass reward deviated stop * defect :=
    mul_le_mul_of_nonneg_right hmassLe hdefectNonneg
  have hdebt :=
    quittingLiveMass_mul_coordinateNashDefect_update_pureTime_some_le_initialDebt
      reward profile who stop stop le_rfl hM hreward
  rw [hmassEq]
  exact hscaled.trans hdebt

/-! ## Persistent collision mass forces a first-order row -/

/-- If one fixed coalition containing the pure-time deviator keeps positive
terminal mass while the deviated profile's selected debt tends to zero, then
the chosen Quit dates are eventually finite, the same coalition keeps that
mass at the selected stage, and the marked player's local root defect tends
to zero.

No assertion is made about the other coordinates of the root defect. -/
theorem exists_stops_tendsto_coordinateNashDefect_zero_of_persistent_collision
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (who : ι) (quitTime : ℕ → Option ℕ)
    (terminal : {S : Finset ι // S.Nonempty})
    (hmem : who ∈ terminal.val)
    {lower M : ℝ} (hlower : 0 < lower) (hM : 0 ≤ M)
    (hreward : ∀ outcome player, |reward outcome player| ≤ M)
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
    ∃ stop : ℕ → ℕ,
      (∀ᶠ n in atTop, quitTime n = some (stop n)) ∧
      (∀ᶠ n in atTop, lower ≤
        quittingStageCoalitionMass reward
          (Function.update (profiles n) who
            (quittingPureTimeBehaviorStrategy reward who (quitTime n)))
          (stop n) terminal) ∧
      Tendsto (fun n =>
        let deviated := Function.update (profiles n) who
          (quittingPureTimeBehaviorStrategy reward who (quitTime n))
        quittingRootCoordinateNashDefect reward
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward deviated (stop n + 1))).1
          (quittingProfileLiveRoot reward deviated (stop n)) who)
        atTop (𝓝 0) := by
  let stop : ℕ → ℕ := fun n => (quitTime n).getD 0
  have hfinite : ∀ᶠ n in atTop, quitTime n = some (stop n) := by
    filter_upwards [hpersistent] with n hn
    cases hchoice : quitTime n with
    | none =>
        have hzero : quittingTerminalOutcomeMass reward
            (Function.update (profiles n) who
              (quittingPureTimeBehaviorStrategy reward who (quitTime n)))
            (some terminal) = 0 := by
          rw [hchoice]
          exact quittingTerminalOutcomeMass_update_pureTime_none_mem_eq_zero
            reward (profiles n) who terminal hmem
        rw [hzero] at hn
        linarith
    | some time =>
        simp [stop, hchoice]
  have hstage : ∀ᶠ n in atTop, lower ≤
      quittingStageCoalitionMass reward
        (Function.update (profiles n) who
          (quittingPureTimeBehaviorStrategy reward who (quitTime n)))
        (stop n) terminal := by
    filter_upwards [hpersistent, hfinite] with n hn hchoice
    rw [hchoice] at hn ⊢
    rwa [← quittingTerminalOutcomeMass_update_pureTime_some_mem_eq_at
      reward (profiles n) who (stop n) terminal hmem]
  let defect : ℕ → ℝ := fun n =>
    let deviated := Function.update (profiles n) who
      (quittingPureTimeBehaviorStrategy reward who (quitTime n))
    quittingRootCoordinateNashDefect reward
      (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward deviated (stop n + 1))).1
      (quittingProfileLiveRoot reward deviated (stop n)) who
  have hdefectNonneg : ∀ n, 0 ≤ defect n := by
    intro n
    exact quittingRootCoordinateNashDefect_nonneg reward _ _ who
  have hmajor : ∀ᶠ n in atTop,
      defect n ≤
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update (profiles n) who
              (quittingPureTimeBehaviorStrategy reward who (quitTime n)))) who /
          lower := by
    filter_upwards [hfinite, hpersistent] with n hchoice hmass
    rw [hchoice] at hmass
    have hbound :=
      quittingTerminalOutcomeMass_mul_coordinateNashDefect_at_pureTime_stop_le_debt
        reward (profiles n) who (stop n) terminal hmem hM hreward
    have hbound' :
        quittingTerminalOutcomeMass reward
            (Function.update (profiles n) who
              (quittingPureTimeBehaviorStrategy reward who (some (stop n))))
            (some terminal) * defect n ≤
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (Function.update (profiles n) who
                (quittingPureTimeBehaviorStrategy reward who (some (stop n)))))
            who := by
      simpa only [defect, hchoice] using hbound
    have hscaled : lower * defect n ≤
        quittingTerminalOutcomeMass reward
          (Function.update (profiles n) who
            (quittingPureTimeBehaviorStrategy reward who (some (stop n))))
          (some terminal) * defect n :=
      mul_le_mul_of_nonneg_right hmass (hdefectNonneg n)
    apply (le_div_iff₀ hlower).2
    simpa only [hchoice, mul_comm] using hscaled.trans hbound'
  have hresetDiv : Tendsto (fun n =>
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (Function.update (profiles n) who
            (quittingPureTimeBehaviorStrategy reward who (quitTime n)))) who /
        lower) atTop (𝓝 0) := by
    simpa using hreset.div_const lower
  have hdefect : Tendsto defect atTop (𝓝 0) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hresetDiv
      (Eventually.of_forall hdefectNonneg) hmajor
  exact ⟨stop, hfinite, hstage, hdefect⟩

end GameTheory
