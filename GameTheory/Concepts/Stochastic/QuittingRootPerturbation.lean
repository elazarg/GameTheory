/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingRootContinuation
import Math.PMFProduct.TotalVariation
import Math.ProbabilityMassFunction.TotalVariation

/-!
# One-coordinate perturbations of quitting-game root actions

Replacing one player's root marginal changes the whole independent product
law by exactly the total-variation distance between the two marginals.  Thus
a root payoff bounded by `M` changes by at most `2 * M * d` when that marginal
moves by total variation at most `d`.  A different player's one-stage regret
is the difference of a deviation payoff and a prescribed payoff, so its safe
perturbation bound is `4 * M * d`.

These are root-law statements.  They do not assert a proper-path bridge or a
stationary discretization estimate.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The one-stage regret in a quitting root continuation game. -/
def quittingRootDeviationRegret
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (root : ι → PMF Bool)
    (who : ι) (deviation : PMF Bool) : ℝ :=
  quittingRootExpectedPayoff reward continuation
      (Function.update root who deviation) who -
    quittingRootExpectedPayoff reward continuation root who

omit [DecidableEq ι] in
/-- A uniform bound on terminal rewards and continuation values bounds every
pure payoff of the root continuation game. -/
theorem abs_quittingRootPayoff_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) {M : ℝ}
    (hreward : ∀ S who, |reward S who| ≤ M)
    (hcontinuation : ∀ who, |continuation who| ≤ M)
    (action : ι → Bool) (who : ι) :
    |quittingRootPayoff reward continuation action who| ≤ M := by
  by_cases hquit : (quittingQuitters action).Nonempty
  · simpa [quittingRootPayoff, hquit] using
      hreward ⟨quittingQuitters action, hquit⟩ who
  · simpa [quittingRootPayoff, hquit] using hcontinuation who

/-- Changing one player's root marginal moves every prescribed root payoff by
at most `2 M` times the marginal TV distance. -/
theorem abs_quittingRootExpectedPayoff_update_sub_le_two_mul_pmfTV
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (root : ι → PMF Bool)
    (changed : ι) (oldMarginal newMarginal : PMF Bool)
    (who : ι) {M : ℝ}
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hcontinuation : ∀ player, |continuation player| ≤ M) :
    |quittingRootExpectedPayoff reward continuation
          (Function.update root changed oldMarginal) who -
        quittingRootExpectedPayoff reward continuation
          (Function.update root changed newMarginal) who| ≤
      (2 * M) * pmfTV oldMarginal newMarginal := by
  unfold quittingRootExpectedPayoff
  exact abs_expect_pmfPi_update_sub_le_two_mul_pmfTV
    root changed oldMarginal newMarginal
    (fun action => quittingRootPayoff reward continuation action who)
    (fun action =>
      abs_quittingRootPayoff_le reward continuation
        hreward hcontinuation action who)

/-- If the changed coordinate belongs to another player, that player's root
deviation regret moves by at most `4 M` times the marginal TV distance.  Both
the deviation payoff and the prescribed payoff may move. -/
theorem abs_quittingRootDeviationRegret_update_sub_le_four_mul_pmfTV
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (root : ι → PMF Bool)
    (changed who : ι) (hother : changed ≠ who)
    (oldMarginal newMarginal deviation : PMF Bool) {M : ℝ}
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hcontinuation : ∀ player, |continuation player| ≤ M) :
    |quittingRootDeviationRegret reward continuation
          (Function.update root changed oldMarginal) who deviation -
        quittingRootDeviationRegret reward continuation
          (Function.update root changed newMarginal) who deviation| ≤
      (4 * M) * pmfTV oldMarginal newMarginal := by
  have hdev :=
    abs_quittingRootExpectedPayoff_update_sub_le_two_mul_pmfTV
      reward continuation (Function.update root who deviation) changed
      oldMarginal newMarginal who hreward hcontinuation
  have hbase :=
    abs_quittingRootExpectedPayoff_update_sub_le_two_mul_pmfTV
      reward continuation root changed oldMarginal newMarginal who
      hreward hcontinuation
  unfold quittingRootDeviationRegret
  rw [Function.update_comm (f := root) (a := changed) (b := who)
      hother oldMarginal deviation,
    Function.update_comm (f := root) (a := changed) (b := who)
      hother newMarginal deviation]
  calc
    |(quittingRootExpectedPayoff reward continuation
          (Function.update (Function.update root who deviation)
            changed oldMarginal) who -
        quittingRootExpectedPayoff reward continuation
          (Function.update root changed oldMarginal) who) -
      (quittingRootExpectedPayoff reward continuation
          (Function.update (Function.update root who deviation)
            changed newMarginal) who -
        quittingRootExpectedPayoff reward continuation
          (Function.update root changed newMarginal) who)| =
        |(quittingRootExpectedPayoff reward continuation
              (Function.update (Function.update root who deviation)
                changed oldMarginal) who -
            quittingRootExpectedPayoff reward continuation
              (Function.update (Function.update root who deviation)
                changed newMarginal) who) -
          (quittingRootExpectedPayoff reward continuation
              (Function.update root changed oldMarginal) who -
            quittingRootExpectedPayoff reward continuation
              (Function.update root changed newMarginal) who)| := by ring_nf
    _ ≤
        |quittingRootExpectedPayoff reward continuation
              (Function.update (Function.update root who deviation)
                changed oldMarginal) who -
            quittingRootExpectedPayoff reward continuation
              (Function.update (Function.update root who deviation)
                changed newMarginal) who| +
          |quittingRootExpectedPayoff reward continuation
              (Function.update root changed oldMarginal) who -
            quittingRootExpectedPayoff reward continuation
              (Function.update root changed newMarginal) who| :=
      abs_sub _ _
    _ ≤ (2 * M) * pmfTV oldMarginal newMarginal +
          (2 * M) * pmfTV oldMarginal newMarginal :=
      add_le_add hdev hbase
    _ = (4 * M) * pmfTV oldMarginal newMarginal := by ring

/-- `2 M d` form of the prescribed-payoff perturbation bound. -/
theorem abs_quittingRootExpectedPayoff_update_sub_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (root : ι → PMF Bool)
    (changed : ι) (oldMarginal newMarginal : PMF Bool)
    (who : ι) {M d : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hcontinuation : ∀ player, |continuation player| ≤ M)
    (htv : pmfTV oldMarginal newMarginal ≤ d) :
    |quittingRootExpectedPayoff reward continuation
          (Function.update root changed oldMarginal) who -
        quittingRootExpectedPayoff reward continuation
          (Function.update root changed newMarginal) who| ≤
      2 * M * d := by
  calc
    _ ≤ (2 * M) * pmfTV oldMarginal newMarginal :=
      abs_quittingRootExpectedPayoff_update_sub_le_two_mul_pmfTV
        reward continuation root changed oldMarginal newMarginal who
        hreward hcontinuation
    _ ≤ (2 * M) * d := mul_le_mul_of_nonneg_left htv (by positivity)
    _ = 2 * M * d := by ring

/-- Making one near-sure root quitter quit surely changes a prescribed payoff
by at most `2 M` times that player's former probability of continuing. -/
theorem abs_quittingRootExpectedPayoff_update_pure_true_sub_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (root : ι → PMF Bool)
    (changed : ι) (oldMarginal : PMF Bool) (who : ι) {M : ℝ}
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hcontinuation : ∀ player, |continuation player| ≤ M) :
    |quittingRootExpectedPayoff reward continuation
          (Function.update root changed oldMarginal) who -
        quittingRootExpectedPayoff reward continuation
          (Function.update root changed (PMF.pure true)) who| ≤
      2 * M * (oldMarginal false).toReal := by
  simpa [pmfTV_pure_true, mul_assoc] using
    abs_quittingRootExpectedPayoff_update_sub_le_two_mul_pmfTV
      reward continuation root changed oldMarginal (PMF.pure true) who
      hreward hcontinuation

/-- `4 M d` form of the other-player regret perturbation bound. -/
theorem abs_quittingRootDeviationRegret_update_sub_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (root : ι → PMF Bool)
    (changed who : ι) (hother : changed ≠ who)
    (oldMarginal newMarginal deviation : PMF Bool)
    {M d : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hcontinuation : ∀ player, |continuation player| ≤ M)
    (htv : pmfTV oldMarginal newMarginal ≤ d) :
    |quittingRootDeviationRegret reward continuation
          (Function.update root changed oldMarginal) who deviation -
        quittingRootDeviationRegret reward continuation
          (Function.update root changed newMarginal) who deviation| ≤
      4 * M * d := by
  calc
    _ ≤ (4 * M) * pmfTV oldMarginal newMarginal :=
      abs_quittingRootDeviationRegret_update_sub_le_four_mul_pmfTV
        reward continuation root changed who hother oldMarginal
        newMarginal deviation hreward hcontinuation
    _ ≤ (4 * M) * d := mul_le_mul_of_nonneg_left htv (by positivity)
    _ = 4 * M * d := by ring

/-- Making one near-sure root quitter quit surely changes every other player's
root deviation regret by at most `4 M` times the quitter's former probability
of continuing. -/
theorem abs_quittingRootDeviationRegret_update_pure_true_sub_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (root : ι → PMF Bool)
    (changed who : ι) (hother : changed ≠ who)
    (oldMarginal deviation : PMF Bool) {M : ℝ}
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hcontinuation : ∀ player, |continuation player| ≤ M) :
    |quittingRootDeviationRegret reward continuation
          (Function.update root changed oldMarginal) who deviation -
        quittingRootDeviationRegret reward continuation
          (Function.update root changed (PMF.pure true)) who deviation| ≤
      4 * M * (oldMarginal false).toReal := by
  simpa [pmfTV_pure_true, mul_assoc] using
    abs_quittingRootDeviationRegret_update_sub_le_four_mul_pmfTV
      reward continuation root changed who hother oldMarginal
      (PMF.pure true) deviation hreward hcontinuation

end GameTheory
