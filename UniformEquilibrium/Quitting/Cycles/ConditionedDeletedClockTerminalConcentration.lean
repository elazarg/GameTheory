/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.ConditionedDeletedClockMonopoly
import UniformEquilibrium.Quitting.Cycles.PhantomBoundaryRestart
import UniformEquilibrium.Quitting.Boundary.Exceptional.TailFallback

/-!
# Terminal concentration in the conditioned owner-monopoly branch

A summable deleted clock does more than make all non-owner rescaled hazards
summable.  If the rescaled joint clock is complete, every late rescaled tail
absorbs almost surely, while the probability of a non-owner terminal event is
bounded by the remaining deleted-clock charge.  Consequently its literal
terminal payoff converges coordinatewise to the exceptional owner's singleton
reward vector.

This is a semantic concentration theorem.  It deliberately makes no Nash or
punishment claim; those are the remaining strategic inputs to the approximate
solo-cycle compiler.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Remaining additive opponent-clock charge after a cutoff. -/
def quittingOpponentClockTailCharge
    (roots : ℕ → ι → PMF Bool) (owner : ι) (start : ℕ) : ℝ :=
  ∑' offset : ℕ, quittingOpponentClockCharge roots owner (start + offset)

/-- The probability that an opponent ever quits in a root-sequence tail is at
most the remaining additive opponent-clock charge. -/
theorem one_sub_opponentOnlyLiveMassLimit_le_opponentClockTailCharge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (owner : ι) (start : ℕ)
    (hsummable : Summable (fun offset =>
      quittingOpponentClockCharge roots owner (start + offset))) :
    1 - quittingLiveMassLimit reward
        (quittingOpponentOnlyProfile reward
          (quittingRootSequenceProfile reward roots start) owner) ≤
      quittingOpponentClockTailCharge roots owner start := by
  let shifted : ℕ → ι → PMF Bool := fun time => roots (start + time)
  let profile := quittingRootSequenceProfile reward shifted 0
  let opponentProfile := quittingOpponentOnlyProfile reward profile owner
  have hprofile : quittingRootSequenceProfile reward roots start = profile :=
    quittingRootSequenceProfile_eq_shift reward roots start
  have hlive : ∀ fuel,
      quittingOpponentSurvivalWeight roots owner start fuel =
        quittingLiveMass reward opponentProfile fuel := by
    intro fuel
    have hbase := quittingOpponentSurvivalWeight_profileLiveRoot_eq_liveMass
      reward profile owner fuel
    rw [quittingProfileLiveRoot_quittingRootSequenceProfile_zero] at hbase
    calc
      quittingOpponentSurvivalWeight roots owner start fuel =
          quittingOpponentSurvivalWeight shifted owner 0 fuel := by
        unfold quittingOpponentSurvivalWeight
        apply Finset.prod_congr rfl
        intro offset _
        unfold quittingFixedOpponentsContinueMass
        dsimp only [shifted]
        rw [Nat.zero_add]
      _ = quittingLiveMass reward opponentProfile fuel := hbase
  have hleft : Tendsto (fun fuel =>
      1 - quittingOpponentSurvivalWeight roots owner start fuel)
      atTop (nhds (1 - quittingLiveMassLimit reward opponentProfile)) := by
    apply (tendsto_const_nhds.sub
      (tendsto_quittingLiveMass reward opponentProfile)).congr'
    exact Filter.Eventually.of_forall fun fuel => by
      change 1 - quittingLiveMass reward opponentProfile fuel =
        1 - quittingOpponentSurvivalWeight roots owner start fuel
      rw [hlive fuel]
  have hright : Tendsto (fun fuel =>
      ∑ offset ∈ Finset.range fuel,
        quittingOpponentClockCharge roots owner (start + offset))
      atTop (nhds (quittingOpponentClockTailCharge roots owner start)) := by
    exact hsummable.hasSum.tendsto_sum_nat
  rw [hprofile]
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [] with fuel
  have hunion := one_sub_sum_quittingOpponentClockCharge_le_survival
    roots owner start fuel
  linarith

/-- Tail opponent charge tends to zero along any summable clock. -/
theorem tendsto_quittingOpponentClockTailCharge_zero
    (roots : ℕ → ι → PMF Bool) (owner : ι) (start : ℕ)
    (hsummable : Summable (fun offset =>
      quittingOpponentClockCharge roots owner (start + offset))) :
    Tendsto (fun later =>
      quittingOpponentClockTailCharge roots owner (start + later))
      atTop (nhds 0) := by
  let charge : ℕ → ℝ := fun offset =>
    quittingOpponentClockCharge roots owner (start + offset)
  have _hsummable : Summable charge := hsummable
  have htail := tendsto_sum_nat_add charge
  convert htail using 1
  funext later
  unfold quittingOpponentClockTailCharge charge
  congr 1
  funext offset
  rw [Nat.add_assoc]
  congr 1
  omega

/-- Almost-sure absorption plus a summable opponent clock gives the literal
terminal singleton-concentration estimate on every suffix. -/
theorem abs_quittingRootSequenceTerminalValue_sub_soloReward_le_tailCharge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (owner who : ι) (start : ℕ) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hjoint : Tendsto (quittingJointSurvivalWeight roots start)
      atTop (nhds 0))
    (hopponent : Summable (fun offset =>
      quittingOpponentClockCharge roots owner (start + offset))) :
    |quittingRootSequenceTerminalValue reward roots who start -
        quittingSoloReward reward owner who| ≤
      2 * M * quittingOpponentClockTailCharge roots owner start := by
  have hsurvivalZero : quittingJointSurvivalLimit roots start = 0 :=
    tendsto_nhds_unique (tendsto_quittingJointSurvivalLimit roots start) hjoint
  have habsorbs : quittingLiveMassLimit reward
      (quittingRootSequenceProfile reward roots start) = 0 := by
    rw [quittingLiveMassLimit_rootSequence_eq_jointSurvivalLimit,
      hsurvivalZero]
  have htail :=
    one_sub_opponentOnlyLiveMassLimit_le_opponentClockTailCharge
      reward roots owner start hopponent
  exact abs_quittingTerminalPayoff_sub_soloReward_le_of_opponentLiveTail
    reward (quittingRootSequenceProfile reward roots start) owner who
      hM hreward habsorbs htail

/-- **Terminal concentration of an owner-monopoly rescaled path.**  A
complete joint rescaled clock and a summable owner-deleted clock force every
late literal terminal payoff to converge to the owner's singleton vector. -/
theorem tendsto_quittingRootSequenceTerminalValue_soloReward_of_ownerMonopoly
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (owner who : ι) (start : ℕ) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (habsorption : ¬Summable (fun offset =>
      quittingRootAbsorptionMass (roots (start + offset))))
    (hopponent : Summable (fun offset =>
      quittingOpponentClockCharge roots owner (start + offset))) :
    Tendsto (fun later =>
      quittingRootSequenceTerminalValue reward roots who (start + later))
      atTop (nhds (quittingSoloReward reward owner who)) := by
  have hopponentTail : ∀ later, Summable (fun offset =>
      quittingOpponentClockCharge roots owner ((start + later) + offset)) := by
    intro later
    let charge : ℕ → ℝ := fun offset =>
      quittingOpponentClockCharge roots owner (start + offset)
    have hshift : Summable (fun offset => charge (offset + later)) :=
      (summable_nat_add_iff later).2 hopponent
    simpa only [charge, Nat.add_assoc, Nat.add_comm later] using hshift
  have habsorptionTail : ∀ later, ¬Summable (fun offset =>
      quittingRootAbsorptionMass (roots ((start + later) + offset))) := by
    intro later hsummable
    let charge : ℕ → ℝ := fun offset =>
      quittingRootAbsorptionMass (roots (start + offset))
    have hshift : Summable (fun offset => charge (offset + later)) := by
      simpa only [charge, Nat.add_assoc, Nat.add_comm later] using hsummable
    exact habsorption ((summable_nat_add_iff later).1 hshift)
  have herrorZero := tendsto_quittingOpponentClockTailCharge_zero
    roots owner start hopponent
  have hscaled : Tendsto (fun later =>
      2 * M * quittingOpponentClockTailCharge roots owner (start + later))
      atTop (nhds 0) := by
    simpa using herrorZero.const_mul (2 * M)
  apply tendsto_iff_dist_tendsto_zero.mpr
  have habs : Tendsto (fun later =>
      |quittingRootSequenceTerminalValue reward roots who (start + later) -
        quittingSoloReward reward owner who|) atTop (nhds 0) := by
    apply squeeze_zero
    · intro later
      exact abs_nonneg _
    · intro later
      apply abs_quittingRootSequenceTerminalValue_sub_soloReward_le_tailCharge
        reward roots owner who (start + later) hM hreward
      · exact tendsto_zero_quittingJointSurvivalWeight_of_not_summable_absorption
          roots (start + later) (habsorptionTail later)
      · exact hopponentTail later
    · exact hscaled
  simpa [Real.dist_eq] using habs

/-- **Conditioned deficient-clock capstone.**  A summable source deleted
clock in the complete diffuse regime produces a literal rescaled path whose
opponent clock is summable, whose joint absorption clock is nonsummable, and
whose late terminal payoff converges to the exceptional owner's singleton
reward vector.  The owner's rescaled hazard remains positive arbitrarily
late. -/
theorem conditionedDeletedClock_terminalConcentration
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (owner : ι) (start : ℕ)
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption roots time)
    (heventualZero : Tendsto
      (quittingTailEventualAbsorption roots) atTop (nhds 0))
    (hmesh : Tendsto
      (quittingTailConditionedAbsorptionWeight roots) atTop (nhds 0))
    (hsummable : Summable (fun offset =>
      quittingTailConditionedOpponentWeight roots (start + offset) owner)) :
    let targetRoots := quittingTailDiffuseRescaledRoots roots hpositive
    Summable (fun offset =>
        quittingOpponentClockCharge targetRoots owner (start + offset)) ∧
      ¬Summable (fun offset =>
        quittingRootAbsorptionMass (targetRoots (start + offset))) ∧
      (∀ who, Tendsto (fun later =>
          quittingRootSequenceTerminalValue reward targetRoots who
            (start + later))
        atTop (nhds (quittingSoloReward reward owner who))) ∧
      ∀ threshold, ∃ offset, threshold ≤ offset ∧
        0 < quittingTailDiffuseRescaledHazard
          roots (start + offset) owner := by
  dsimp only
  obtain ⟨hopponentTotal, _hother, howner, hpositiveLate⟩ :=
    conditionedDeletedClock_ownerMonopoly roots owner start hpositive
      heventualZero hmesh hsummable
  have hopponentRaw :=
    summable_quittingTailDiffuseRescaledRoot_opponentAbsorption
      roots owner start hpositive hopponentTotal
  have hopponent : Summable (fun offset =>
      quittingOpponentClockCharge
        (quittingTailDiffuseRescaledRoots roots hpositive) owner
          (start + offset)) := by
    simpa [quittingOpponentClockCharge,
      quittingTailDiffuseRescaledRoots] using hopponentRaw
  have habsorptionRaw :=
    not_summable_quittingTailDiffuseRescaledRoot_absorptionMass
      roots owner start hpositive howner
  have habsorption : ¬Summable (fun offset =>
      quittingRootAbsorptionMass
        (quittingTailDiffuseRescaledRoots roots hpositive
          (start + offset))) := by
    simpa [quittingTailDiffuseRescaledRoots] using habsorptionRaw
  refine ⟨hopponent, habsorption, ?_, hpositiveLate⟩
  intro who
  exact tendsto_quittingRootSequenceTerminalValue_soloReward_of_ownerMonopoly
    reward (quittingTailDiffuseRescaledRoots roots hpositive) owner who start
      (quittingRewardBound_nonneg reward)
      (abs_reward_le_quittingRewardBound reward) habsorption hopponent

end GameTheory
