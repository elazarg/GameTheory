/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Root.FirstStageAdapter

/-!
# Forcing a near-sure quitting root to quit surely

For a finite nonempty player set, if the probability of the all-continue root
action is at most `d ^ |I|`, some player's probability of continuing is at
most `d`.  This file selects such a player and forces that player's root
marginal to `pure true`.

When terminal rewards and continuation values are bounded by `M`, the
operation changes every prescribed root payoff by at most `2 * M * d` and
every player's root-deviation regret by at most `4 * M * d`.  The latter
includes the selected player: its deviation payoff is unchanged, while only
its prescribed payoff moves.  Thus an epsilon-Nash root becomes an
`(epsilon + 4 * M * d)`-Nash root with a sure quitter.

The final corollary applies the exact `First` compiler to the forced root.
This is a finite-profile perturbation theorem.  It does not perform the
compactness or subsequence extraction needed to obtain its hypotheses from a
sequence whose absorption probabilities converge to one.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- If the all-continue product mass is at most `d ^ |I|`, some coordinate's
continue probability is at most `d`. -/
theorem exists_continueProbability_le_of_allContinue_mass_le_pow
    [Nonempty ι] (root : ι → PMF Bool) {d : ℝ} (hd : 0 < d)
    (hnear : ((pmfPi root) quittingAllContinueAction).toReal ≤
      d ^ Fintype.card ι) :
    ∃ changed, (root changed false).toReal ≤ d := by
  by_contra hnone
  push Not at hnone
  have hprod : d ^ Fintype.card ι <
      ∏ player, (root player false).toReal := by
    simpa using Finset.prod_lt_prod_of_nonempty
      (s := Finset.univ) (fun _ _ => hd)
      (fun player _ => hnone player) Finset.univ_nonempty
  have hmass : ((pmfPi root) quittingAllContinueAction).toReal =
      ∏ player, (root player false).toReal := by
    rw [pmfPi_apply, ENNReal.toReal_prod]
    simp [quittingAllContinueAction]
  rw [hmass] at hnear
  exact (not_lt_of_ge hnear) hprod

omit [Fintype ι] in
/-- Forcing one coordinate to quit produces a root with a sure quitter. -/
theorem quittingRootHasSureQuitter_update_pure_true
    (root : ι → PMF Bool) (changed : ι) :
    QuittingRootHasSureQuitter
      (Function.update root changed (PMF.pure true)) := by
  exact ⟨changed, Function.update_self changed (PMF.pure true) root⟩

/-- Direct form of the prescribed-payoff perturbation bound when a coordinate
of `root` itself is replaced by sure quitting. -/
theorem abs_quittingRootExpectedPayoff_forceQuit_sub_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (root : ι → PMF Bool)
    (changed who : ι) {M : ℝ}
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hcontinuation : ∀ player, |continuation player| ≤ M) :
    |quittingRootExpectedPayoff reward continuation root who -
        quittingRootExpectedPayoff reward continuation
          (Function.update root changed (PMF.pure true)) who| ≤
      2 * M * (root changed false).toReal := by
  simpa using
    (abs_quittingRootExpectedPayoff_update_pure_true_sub_le
      reward continuation root changed (root changed) who
      hreward hcontinuation)

/-- For the selected player, forcing its prescribed root action to quit does
not change any fixed deviation payoff.  The change in regret is exactly the
opposite change in prescribed payoff. -/
theorem quittingRootDeviationRegret_forceQuit_self_sub_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (root : ι → PMF Bool)
    (changed : ι) (deviation : PMF Bool) :
    quittingRootDeviationRegret reward continuation root changed deviation -
        quittingRootDeviationRegret reward continuation
          (Function.update root changed (PMF.pure true))
          changed deviation =
      quittingRootExpectedPayoff reward continuation
          (Function.update root changed (PMF.pure true)) changed -
        quittingRootExpectedPayoff reward continuation root changed := by
  unfold quittingRootDeviationRegret
  simp only [Function.update_idem]
  ring

/-- The selected player's regret changes by at most the `2 M d` prescribed
payoff movement. -/
theorem abs_quittingRootDeviationRegret_forceQuit_self_sub_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (root : ι → PMF Bool)
    (changed : ι) (deviation : PMF Bool) {M : ℝ}
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hcontinuation : ∀ player, |continuation player| ≤ M) :
    |quittingRootDeviationRegret reward continuation root changed deviation -
        quittingRootDeviationRegret reward continuation
          (Function.update root changed (PMF.pure true))
          changed deviation| ≤
      2 * M * (root changed false).toReal := by
  rw [quittingRootDeviationRegret_forceQuit_self_sub_eq]
  simpa [abs_sub_comm] using
    (abs_quittingRootExpectedPayoff_forceQuit_sub_le
      reward continuation root changed changed hreward hcontinuation)

/-- Direct form of the existing `4 M d` regret bound for every player other
than the coordinate forced to quit. -/
theorem abs_quittingRootDeviationRegret_forceQuit_other_sub_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (root : ι → PMF Bool)
    (changed who : ι) (hother : changed ≠ who)
    (deviation : PMF Bool) {M : ℝ}
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hcontinuation : ∀ player, |continuation player| ≤ M) :
    |quittingRootDeviationRegret reward continuation root who deviation -
        quittingRootDeviationRegret reward continuation
          (Function.update root changed (PMF.pure true)) who deviation| ≤
      4 * M * (root changed false).toReal := by
  simpa using
    (abs_quittingRootDeviationRegret_update_pure_true_sub_le
      reward continuation root changed who hother (root changed)
      deviation hreward hcontinuation)

/-- Uniform `4 M d` regret perturbation bound, including the selected player. -/
theorem abs_quittingRootDeviationRegret_forceQuit_sub_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (root : ι → PMF Bool)
    (changed who : ι) (deviation : PMF Bool) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hcontinuation : ∀ player, |continuation player| ≤ M) :
    |quittingRootDeviationRegret reward continuation root who deviation -
        quittingRootDeviationRegret reward continuation
          (Function.update root changed (PMF.pure true)) who deviation| ≤
      4 * M * (root changed false).toReal := by
  by_cases hself : changed = who
  · subst who
    calc
      _ ≤ 2 * M * (root changed false).toReal :=
        abs_quittingRootDeviationRegret_forceQuit_self_sub_le
          reward continuation root changed deviation
          hreward hcontinuation
      _ ≤ 4 * M * (root changed false).toReal := by
        apply mul_le_mul_of_nonneg_right
        · linarith
        · exact ENNReal.toReal_nonneg
  · exact abs_quittingRootDeviationRegret_forceQuit_other_sub_le
      reward continuation root changed who hself deviation
      hreward hcontinuation

/-- Increasing the allowed root-Nash error preserves the root-Nash property. -/
theorem IsεQuittingRootNash.mono
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (root : ι → PMF Bool)
    {ε ε' : ℝ} (hnash : IsεQuittingRootNash reward continuation ε root)
    (hε : ε ≤ ε') :
    IsεQuittingRootNash reward continuation ε' root := by
  intro who deviation
  apply (hnash who deviation).trans
  simpa [add_comm] using
    (add_le_add_left hε
      (quittingRootExpectedPayoff reward continuation root who))

/-- Forcing one coordinate to quit transfers a root epsilon-Nash inequality,
with the exact uniform error increment supplied by the regret bound. -/
theorem isεQuittingRootNash_update_pure_true
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (root : ι → PMF Bool)
    (changed : ι) {ε M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hcontinuation : ∀ player, |continuation player| ≤ M)
    (hnash : IsεQuittingRootNash reward continuation ε root) :
    IsεQuittingRootNash reward continuation
      (ε + 4 * M * (root changed false).toReal)
      (Function.update root changed (PMF.pure true)) := by
  intro who deviation
  have hold := hnash who deviation
  have hregret := abs_quittingRootDeviationRegret_forceQuit_sub_le
    reward continuation root changed who deviation hM
    hreward hcontinuation
  unfold quittingRootDeviationRegret at hregret
  rw [abs_le] at hregret
  linarith

/-- Quantitative near-sure-to-sure replacement at a selected coordinate. -/
theorem nearSureRootReplacement
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (root : ι → PMF Bool)
    (changed : ι) {ε M d : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hcontinuation : ∀ player, |continuation player| ≤ M)
    (hcontinue : (root changed false).toReal ≤ d)
    (hnash : IsεQuittingRootNash reward continuation ε root) :
    QuittingRootHasSureQuitter
        (Function.update root changed (PMF.pure true)) ∧
      (∀ who,
        |quittingRootExpectedPayoff reward continuation root who -
            quittingRootExpectedPayoff reward continuation
              (Function.update root changed (PMF.pure true)) who| ≤
          2 * M * d) ∧
      (∀ who deviation,
        |quittingRootDeviationRegret reward continuation root who deviation -
            quittingRootDeviationRegret reward continuation
              (Function.update root changed (PMF.pure true))
              who deviation| ≤
          4 * M * d) ∧
      IsεQuittingRootNash reward continuation (ε + 4 * M * d)
        (Function.update root changed (PMF.pure true)) := by
  have htwo : 0 ≤ 2 * M := mul_nonneg (by norm_num) hM
  have hfour : 0 ≤ 4 * M := mul_nonneg (by norm_num) hM
  refine ⟨quittingRootHasSureQuitter_update_pure_true root changed,
    ?_, ?_, ?_⟩
  · intro who
    calc
      _ ≤ 2 * M * (root changed false).toReal :=
        abs_quittingRootExpectedPayoff_forceQuit_sub_le
          reward continuation root changed who hreward hcontinuation
      _ ≤ 2 * M * d := mul_le_mul_of_nonneg_left hcontinue htwo
  · intro who deviation
    calc
      _ ≤ 4 * M * (root changed false).toReal :=
        abs_quittingRootDeviationRegret_forceQuit_sub_le
          reward continuation root changed who deviation hM
          hreward hcontinuation
      _ ≤ 4 * M * d := mul_le_mul_of_nonneg_left hcontinue hfour
  · apply (isεQuittingRootNash_update_pure_true
      reward continuation root changed hM hreward hcontinuation hnash).mono
    simpa [add_comm] using
      (add_le_add_left (mul_le_mul_of_nonneg_left hcontinue hfour) ε)

/-- Finite-player selection plus the full quantitative root replacement
packet. -/
theorem exists_nearSureRootReplacement_of_allContinue_mass_le_pow
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (root : ι → PMF Bool)
    {ε M d : ℝ} (hd : 0 < d) (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hcontinuation : ∀ player, |continuation player| ≤ M)
    (hnear : ((pmfPi root) quittingAllContinueAction).toReal ≤
      d ^ Fintype.card ι)
    (hnash : IsεQuittingRootNash reward continuation ε root) :
    ∃ changed,
      (root changed false).toReal ≤ d ∧
      QuittingRootHasSureQuitter
          (Function.update root changed (PMF.pure true)) ∧
      (∀ who,
        |quittingRootExpectedPayoff reward continuation root who -
            quittingRootExpectedPayoff reward continuation
              (Function.update root changed (PMF.pure true)) who| ≤
          2 * M * d) ∧
      (∀ who deviation,
        |quittingRootDeviationRegret reward continuation root who deviation -
            quittingRootDeviationRegret reward continuation
              (Function.update root changed (PMF.pure true))
              who deviation| ≤
          4 * M * d) ∧
      IsεQuittingRootNash reward continuation (ε + 4 * M * d)
        (Function.update root changed (PMF.pure true)) := by
  obtain ⟨changed, hcontinue⟩ :=
    exists_continueProbability_le_of_allContinue_mass_le_pow root hd hnear
  exact ⟨changed, hcontinue,
    nearSureRootReplacement reward continuation root changed hM
      hreward hcontinuation hcontinue hnash⟩

/-- A bounded quitting game has a bounded continuation best-response vector. -/
theorem abs_quittingContinuationBestResponse_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : (quittingGame reward).BehaviorProfile)
    (who : ι) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M) :
    |quittingContinuationBestResponse reward continuation who| ≤ M := by
  let values : Set ℝ := Set.range fun deviation :
      (quittingGame reward).BehaviorStrategy who =>
    quittingTerminalPayoff reward
      (Function.update continuation who deviation) who
  let alwaysContinue : (quittingGame reward).BehaviorStrategy who :=
    fun _ _ => PMF.pure false
  have hvalues : values.Nonempty :=
    ⟨quittingTerminalPayoff reward
      (Function.update continuation who alwaysContinue) who,
      ⟨alwaysContinue, rfl⟩⟩
  have hbounded : BddAbove values := by
    refine ⟨M, ?_⟩
    rintro payoff ⟨deviation, rfl⟩
    exact (le_abs_self _).trans
      (abs_quittingTerminalPayoff_le reward
        (Function.update continuation who deviation) who hM hreward)
  have hupper : sSup values ≤ M := by
    apply csSup_le hvalues
    rintro _ ⟨deviation, rfl⟩
    exact (le_abs_self _).trans
      (abs_quittingTerminalPayoff_le reward
        (Function.update continuation who deviation) who hM hreward)
  have hlowerValue : -M ≤ quittingTerminalPayoff reward
      (Function.update continuation who alwaysContinue) who :=
    (neg_le_of_abs_le (abs_quittingTerminalPayoff_le reward
      (Function.update continuation who alwaysContinue) who hM hreward))
  have hlowerSup : quittingTerminalPayoff reward
      (Function.update continuation who alwaysContinue) who ≤ sSup values :=
    le_csSup hbounded ⟨alwaysContinue, rfl⟩
  change |sSup values| ≤ M
  rw [abs_le]
  exact ⟨hlowerValue.trans hlowerSup, hupper⟩

/-- The quantitative root replacement, specialized to the continuation
best-response vector consumed by the exact `First` criterion. -/
theorem exists_sureFirst_of_nearSure_rootNash
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : (quittingGame reward).BehaviorProfile)
    (root : ι → PMF Bool) {ε M d : ℝ}
    (hd : 0 < d) (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hnear : ((pmfPi root) quittingAllContinueAction).toReal ≤
      d ^ Fintype.card ι)
    (hnash : IsεQuittingRootNash reward
      (quittingContinuationBestResponse reward continuation) ε root) :
    ∃ sureRoot : ι → PMF Bool,
      QuittingRootHasSureQuitter sureRoot ∧
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) (ε + 4 * M * d)
        (quittingRootThenContinuationProfile reward sureRoot continuation) := by
  obtain ⟨changed, -, hsure, -, -, hforced⟩ :=
    exists_nearSureRootReplacement_of_allContinue_mass_le_pow
      reward (quittingContinuationBestResponse reward continuation) root
      hd hM hreward
      (fun who => abs_quittingContinuationBestResponse_le
        reward continuation who hM hreward)
      hnear hnash
  let sureRoot := Function.update root changed (PMF.pure true)
  exact ⟨sureRoot, hsure,
    isεAsymptoticNash_quittingRootThenContinuation_of_isεQuittingRootNash
      reward sureRoot continuation hM hreward hsure hforced⟩

end GameTheory
