/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Repair.FixedTailPositiveAbsorptionRoot
import UniformEquilibrium.Quitting.Paths.OutsiderNeverGluing

/-!
# Uniform absorption forced by a fixed-tail singleton gap

A positive singleton-to-target gap gives more than qualitative absorption.
Every exact endpoint-Nash root against that target absorbs with a uniform
positive probability.  The estimate uses the outsider decomposition: if the
selected player keeps positive Continue mass, endpoint optimality can cancel
the singleton gap only through opponent absorption; if that Continue mass is
zero, the joint root already absorbs surely.

The result is local to one fixed target.  It does not select roots
continuously or concatenate independently generated predecessor edges.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The outsider joining term is bounded in absolute value by the opponent
absorption probability times twice the reward bound. -/
theorem abs_quittingOutsiderJoiningContribution_le_two_mul_absorptionMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M) :
    |quittingOutsiderJoiningContribution reward root who| ≤
      2 * M * quittingRootOpponentAbsorptionMass root who := by
  let opponentRoot := Function.update root who (PMF.pure false)
  let advantage := quittingTerminalOpponentAdvantage reward who
  let indicator : (ι → Bool) → ℝ := fun action =>
    if (quittingQuitters action).Nonempty then 1 else 0
  have hpoint : ∀ action : ι → Bool,
      |advantage action| ≤ 2 * M * indicator action := by
    intro action
    by_cases hquit : (quittingQuitters action).Nonempty
    · dsimp only [advantage, indicator]
      simpa [hquit] using
        abs_quittingTerminalOpponentAdvantage_le_two_mul
          reward who action hM hreward
    · dsimp only [advantage, indicator]
      rw [quittingTerminalOpponentAdvantage_eq_zero_of_quitters_not_nonempty
        reward who action hquit]
      simp [hquit]
  have hindicator : expect (pmfPi opponentRoot) indicator =
      quittingRootAbsorptionMass opponentRoot := by
    simpa [indicator] using
      expect_quittingNonemptyIndicator_eq_absorptionMass opponentRoot
  have hupper : expect (pmfPi opponentRoot) advantage ≤
      2 * M * quittingRootAbsorptionMass opponentRoot := by
    calc
      expect (pmfPi opponentRoot) advantage ≤
          expect (pmfPi opponentRoot) (fun action => 2 * M * indicator action) :=
        expect_mono _ _ _ fun action =>
          (le_abs_self (advantage action)).trans (hpoint action)
      _ = 2 * M * quittingRootAbsorptionMass opponentRoot := by
        rw [expect_const_mul, hindicator]
  have hlower : -(2 * M * quittingRootAbsorptionMass opponentRoot) ≤
      expect (pmfPi opponentRoot) advantage := by
    have hmono : expect (pmfPi opponentRoot)
          (fun action => -(2 * M * indicator action)) ≤
        expect (pmfPi opponentRoot) advantage :=
      expect_mono _ _ _ fun action =>
        (neg_le_of_abs_le (hpoint action))
    have hleft : expect (pmfPi opponentRoot)
          (fun action => -(2 * M * indicator action)) =
        -(2 * M * quittingRootAbsorptionMass opponentRoot) := by
      rw [show (fun action => -(2 * M * indicator action)) =
          fun action => (-2 * M) * indicator action by
        funext action
        ring,
        expect_const_mul, hindicator]
      ring
    rw [hleft] at hmono
    exact hmono
  unfold quittingOutsiderJoiningContribution
  change |-expect (pmfPi opponentRoot) advantage| ≤ _
  rw [abs_neg]
  exact abs_le.mpr ⟨hlower, hupper⟩

/-- A uniform singleton gap forces a quantitative lower bound on the joint
absorption of every exact endpoint-Nash root against the fixed target. -/
theorem gap_div_le_quittingRootAbsorptionMass_of_isZeroEndpointNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    {M eta : ℝ} (hM : 0 ≤ M) (heta : 0 < eta)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hgap : tail who ≤ reward (quittingSingletonTerminal who) who - eta)
    (hnash : IsεQuittingRootEndpointNash reward tail 0 root) :
    eta / (eta + 2 * M) ≤ quittingRootAbsorptionMass root := by
  let ownContinue := (root who false).toReal
  let opponentMass := quittingRootOpponentAbsorptionMass root who
  have hdenom : 0 < eta + 2 * M := by positivity
  have hratioNonneg : 0 ≤ eta / (eta + 2 * M) := by positivity
  have hratioLeOne : eta / (eta + 2 * M) ≤ 1 := by
    apply (div_le_one hdenom).2
    linarith
  by_cases hcontinue : ownContinue = 0
  · have hjointContinue : quittingStationaryContinueMass root = 0 := by
      apply le_antisymm
      · exact (quittingStationaryContinueMass_le_ownContinueProbability
          root who).trans_eq hcontinue
      · exact quittingStationaryContinueMass_nonneg root
    unfold quittingRootAbsorptionMass
    rw [hjointContinue]
    simpa using hratioLeOne
  · have hcontinuePos : 0 < ownContinue := by
      exact lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hcontinue)
    have hendpointNonpos :
        quittingRootEndpointDifference reward tail root who ≤ 0 := by
      have hrow := (hnash who).1
      change ownContinue *
          quittingRootEndpointDifference reward tail root who ≤ 0 at hrow
      rw [mul_comm] at hrow
      exact nonpos_of_mul_nonpos_left hrow hcontinuePos
    have hopponentNonneg : 0 ≤ opponentMass := by
      unfold opponentMass quittingRootOpponentAbsorptionMass
      unfold quittingRootAbsorptionMass
      linarith [quittingStationaryContinueMass_le_one
        (Function.update root who (PMF.pure false))]
    have hopponentLeOne : opponentMass ≤ 1 := by
      unfold opponentMass quittingRootOpponentAbsorptionMass
      unfold quittingRootAbsorptionMass
      linarith [quittingStationaryContinueMass_nonneg
        (Function.update root who (PMF.pure false))]
    have hjoiningAbs :=
      abs_quittingOutsiderJoiningContribution_le_two_mul_absorptionMass
        reward root who hM hreward
    have hjoiningLower :
        -(2 * M * opponentMass) ≤
          quittingOutsiderJoiningContribution reward root who := by
      simpa [opponentMass] using neg_le_of_abs_le hjoiningAbs
    have hgapLower : eta ≤
        reward (quittingSingletonTerminal who) who - tail who := by
      linarith
    have hsurvivalNonneg : 0 ≤ 1 - opponentMass := by linarith
    have hdecomposition :=
      quittingRootEndpointDifference_eq_outsiderNever reward tail root who
    have hmassCharge : eta ≤ opponentMass * (eta + 2 * M) := by
      rw [show quittingRootAbsorptionMass
          (Function.update root who (PMF.pure false)) = opponentMass by rfl]
        at hdecomposition
      have hweightedGap : (1 - opponentMass) * eta ≤
          (1 - opponentMass) *
            (reward (quittingSingletonTerminal who) who - tail who) :=
        mul_le_mul_of_nonneg_left hgapLower hsurvivalNonneg
      nlinarith [hendpointNonpos, hjoiningLower, hweightedGap]
    have hratioLeOpponent : eta / (eta + 2 * M) ≤ opponentMass :=
      (div_le_iff₀ hdenom).2 (by simpa [mul_comm] using hmassCharge)
    exact hratioLeOpponent.trans
      (quittingRootOpponentAbsorptionMass_le_absorptionMass root who)

end GameTheory
