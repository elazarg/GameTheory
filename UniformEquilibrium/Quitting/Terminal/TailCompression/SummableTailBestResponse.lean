/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Bellman.Finite.NashBellmanQuitEndpointLimit
import UniformEquilibrium.Quitting.Cycles.PeriodicWindowEvaluation
import UniformEquilibrium.Quitting.Terminal.TailCompression.ElementaryNeverCoupling

/-!
# Best-response value of a summable quitting tail

Behavioral pure-time extremality and the Never-cap coupling already show that
the best-response value of a root word is close to `max 0 soloReward`, with
error measured by the probability that an opponent eventually quits.  This
file bounds that probability by the unweighted remaining joint-absorption
charge.

Thus a suffix whose remaining charge is below one has the explicit bound

`|bestResponse - max 0 soloReward| ≤ 2 * M * remainingCharge`.

No annotation/realized-payoff identification is used.  The companion
production bound for the prescribed terminal payoff is in
`PhantomBoundaryRestart`.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The probability that some opponent eventually quits is bounded by the
unweighted total joint-absorption charge. -/
theorem one_sub_quittingOpponentSurvivalLimit_le_totalCharge
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hcharge : Summable (fun time ↦
      quittingRootAbsorptionMass (roots time))) :
    1 - quittingOpponentSurvivalLimit roots who 0 ≤
      ∑' time : ℕ, quittingRootAbsorptionMass (roots time) := by
  let forced : ℕ → ι → PMF Bool := fun time ↦
    Function.update (roots time) who (PMF.pure false)
  have hforcedLe : ∀ time,
      quittingRootAbsorptionMass (forced time) ≤
        quittingRootAbsorptionMass (roots time) := by
    intro time
    exact quittingRootOpponentAbsorptionMass_le_absorptionMass
      (roots time) who
  have hforced : Summable (fun time ↦
      quittingRootAbsorptionMass (forced time)) := by
    apply Summable.of_nonneg_of_le
      (fun time ↦ sub_nonneg.mpr
        (quittingStationaryContinueMass_le_one (forced time)))
      hforcedLe hcharge
  have hforcedEq : forced = quittingRootSequenceUpdate roots who
      (quittingPureTimeHazard none) := by
    funext time player
    rfl
  have hlimit : quittingJointSurvivalLimit forced 0 =
      quittingOpponentSurvivalLimit roots who 0 := by
    have hforcedOpponent : Tendsto
        (quittingJointSurvivalWeight forced 0) atTop
        (nhds (quittingOpponentSurvivalLimit roots who 0)) := by
      apply (tendsto_quittingOpponentSurvivalLimit roots who 0).congr'
      apply Filter.Eventually.of_forall
      intro fuel
      rw [hforcedEq]
      exact
        (quittingJointSurvivalWeight_update_none_eq_opponentSurvivalWeight
          roots who 0 fuel).symm
    apply tendsto_nhds_unique
      (tendsto_quittingJointSurvivalLimit forced 0)
      hforcedOpponent
  have hforced0 : Summable (fun offset ↦
      quittingRootAbsorptionMass (forced (0 + offset))) := by
    simpa using hforced
  have hloss := one_sub_quittingJointSurvivalLimit_le_tailCharge
    forced 0 hforced0
  rw [hlimit] at hloss
  have hforcedLe0 : ∀ offset,
      quittingRootAbsorptionMass (forced (0 + offset)) ≤
        quittingRootAbsorptionMass (roots offset) := by
    intro offset
    simpa using hforcedLe offset
  exact hloss.trans (hforced0.tsum_le_tsum hforcedLe0 hcharge)

/-- Remaining total charge below one guarantees a positive deleted-player
survival denominator. -/
theorem quittingOpponentSurvivalLimit_pos_of_totalCharge_lt_one
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hcharge : Summable (fun time ↦
      quittingRootAbsorptionMass (roots time)))
    (hsmall : (∑' time : ℕ,
      quittingRootAbsorptionMass (roots time)) < 1) :
    0 < quittingOpponentSurvivalLimit roots who 0 := by
  have hloss := one_sub_quittingOpponentSurvivalLimit_le_totalCharge
    roots who hcharge
  linarith

/-- Explicit all-behavior best-response bound for a summable suffix with
positive deleted-player survival. -/
theorem abs_quittingRootSequenceBestResponseValue_sub_maxSolo_le_totalCharge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hcharge : Summable (fun time ↦
      quittingRootAbsorptionMass (roots time)))
    (hpositive : 0 < quittingOpponentSurvivalLimit roots who 0) :
    |quittingRootSequenceBestResponseValue reward roots who -
        max 0 (reward (quittingSingletonTerminal who) who)| ≤
      2 * M * ∑' time : ℕ,
        quittingRootAbsorptionMass (roots time) := by
  have hcoupling :=
    abs_quittingRootSequenceBestResponseValue_sub_elementaryNever_le
      reward roots who 0 hM hreward hpositive
  have hcap : quittingElementaryTailRoots roots 0 (.never) =
      quittingElementaryCapRoots (.never : QuittingElementaryTailCap ι) := by
    funext time player
    rfl
  rw [hcap,
    quittingRootSequenceBestResponseValue_elementaryCap_never
      reward who hM hreward,
    quittingOpponentSurvivalWeight] at hcoupling
  have hloss := one_sub_quittingOpponentSurvivalLimit_le_totalCharge
    roots who hcharge
  exact hcoupling.trans (mul_le_mul_of_nonneg_left hloss
    (mul_nonneg (by norm_num) hM))

/-- Late-suffix wrapper with no separate denominator hypothesis: remaining
charge below one supplies positive deleted-player survival. -/
theorem abs_quittingRootSequenceBestResponseValue_sub_maxSolo_le_totalCharge_of_lt_one
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hcharge : Summable (fun time ↦
      quittingRootAbsorptionMass (roots time)))
    (hsmall : (∑' time : ℕ,
      quittingRootAbsorptionMass (roots time)) < 1) :
    |quittingRootSequenceBestResponseValue reward roots who -
        max 0 (reward (quittingSingletonTerminal who) who)| ≤
      2 * M * ∑' time : ℕ,
        quittingRootAbsorptionMass (roots time) :=
  abs_quittingRootSequenceBestResponseValue_sub_maxSolo_le_totalCharge
    reward roots who hM hreward hcharge
      (quittingOpponentSurvivalLimit_pos_of_totalCharge_lt_one
        roots who hcharge hsmall)

end GameTheory
