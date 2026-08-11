/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeConditionedDiffuseFixedOutsider
import UniformEquilibrium.Quitting.Boundary.Repair.SupportEnlargementAlternative

/-!
# Own-marginal repair charge at a conditioned diffuse outsider

The fixed-outsider endpoint gap has a direct predecessor-payoff consequence.
At a selected source-pure-false date, any approximate endpoint-Nash repair that
changes only the outsider's own marginal gains at least the endpoint gap minus
its Nash tolerance, relative to pure Continue.  The conditioned diffuse
rescaling estimate then charges the discrepancy between pure Continue and the
selected conditioned predecessor by the existing joint absorption error.

This is intentionally a one-player repair theorem.  It does not compare two
roots that alter several marginals, and it does not provide state matching or
an actual continuation profile.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- At a source-pure-false conditioned date, an own-marginal endpoint-Nash
repair shifts the outsider's predecessor coordinate by the positive endpoint
gap minus its Nash tolerance and the diffuse joint-charge error. -/
theorem conditionedDiffuse_ownMarginalEndpointRepair_ge_jointCharge_shift
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι) (time : ℕ) (who : ι)
    (eta epsilon M rho : ℝ)
    (hpolicy : ∀ date, value date =
      quittingRootSuccessorPayoff reward (value (date + 1)) (roots date))
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hconditionedBound : ∀ date player,
      |quittingTailConditionedValue roots value boundary date player| ≤ M)
    (hcurrent : 0 < quittingTailEventualAbsorption roots time)
    (hnext : 0 < quittingTailEventualAbsorption roots (time + 1))
    (hinactive : roots time who = PMF.pure false)
    (hmesh : quittingTailConditionedAbsorptionWeight roots time ≤ rho)
    (hsmall : Fintype.card ι *
      quittingTailConditionedAbsorptionWeight roots time ≤ 1)
    (marginal : PMF Bool)
    (hnash : IsεQuittingRootEndpointNash reward
      (quittingTailConditionedValue roots value boundary (time + 1)) epsilon
      (Function.update
        (quittingTailDiffuseRescaledRoot roots time hcurrent) who marginal))
    (hgap : eta / 2 ≤ quittingRootEndpointDifference reward
      (quittingTailConditionedValue roots value boundary (time + 1))
      (quittingTailDiffuseRescaledRoot roots time hcurrent) who) :
    quittingRootExpectedPayoff reward
        (quittingTailConditionedValue roots value boundary (time + 1))
        (Function.update
          (quittingTailDiffuseRescaledRoot roots time hcurrent) who marginal)
        who ≥
      quittingTailConditionedValue roots value boundary time who +
        eta / 2 - epsilon -
          (6 * M * Fintype.card ι * rho) *
            quittingRootOpponentAbsorptionMass
              (quittingTailDiffuseRescaledRoot roots time hcurrent) who := by
  let targetRoot := quittingTailDiffuseRescaledRoot roots time hcurrent
  let next := quittingTailConditionedValue roots value boundary (time + 1)
  let current := quittingTailConditionedValue roots value boundary time
  have htargetInactive : targetRoot who = PMF.pure false := by
    exact quittingTailDiffuseRescaledRoot_eq_pure_false_of_source_eq_pure_false
      roots time who hcurrent hinactive
  have hcharge :=
    abs_conditionedValue_sub_rescaledSuccessorPayoff_le_jointCharge
      (reward := reward) roots value boundary hpolicy hM hreward
      hconditionedBound time who hcurrent hnext hmesh hsmall
  have hrepair :=
    quittingRootExpectedPayoff_update_ownMarginal_ge_pureContinue_add_gap_sub
      reward next targetRoot who marginal hnash
  have hrootEq :
      Function.update targetRoot who (PMF.pure false) = targetRoot := by
    funext player
    by_cases hplayer : player = who
    · subst player
      simp [htargetInactive]
    · simp [Function.update_of_ne hplayer]
  have hcontinue :
      quittingRootExpectedPayoff reward next
          (Function.update targetRoot who (PMF.pure false)) who =
        quittingRootExpectedPayoff reward next targetRoot who := by
    rw [hrootEq]
  have habseq : quittingRootAbsorptionMass targetRoot =
      quittingRootOpponentAbsorptionMass targetRoot who := by
    unfold quittingRootOpponentAbsorptionMass
    rw [hrootEq]
  have habseq' : quittingRootAbsorptionMass
      (quittingTailDiffuseRescaledRoot roots time hcurrent) =
      quittingRootOpponentAbsorptionMass
        (quittingTailDiffuseRescaledRoot roots time hcurrent) who := by
    simpa [targetRoot] using habseq
  have hlower :
      quittingRootExpectedPayoff reward next targetRoot who ≥
        current who -
          (6 * M * Fintype.card ι * rho) *
            quittingRootOpponentAbsorptionMass targetRoot who := by
    have hcharge' := hcharge
    dsimp [targetRoot, next, current] at hcharge' ⊢
    rw [habseq'] at hcharge'
    have hcharge'' :
        |quittingTailConditionedValue roots value boundary time who -
            quittingRootExpectedPayoff reward
              (quittingTailConditionedValue roots value boundary (time + 1))
              (quittingTailDiffuseRescaledRoot roots time hcurrent) who| ≤
          6 * M * Fintype.card ι * rho *
            quittingRootOpponentAbsorptionMass
              (quittingTailDiffuseRescaledRoot roots time hcurrent) who := by
      simpa only [quittingRootSuccessorPayoff] using hcharge'
    have habs := (abs_le.mp hcharge'').2
    linarith
  dsimp [targetRoot, next, current] at hrepair hcontinue hlower ⊢
  linarith [hrepair, hcontinue, hlower]

end GameTheory
