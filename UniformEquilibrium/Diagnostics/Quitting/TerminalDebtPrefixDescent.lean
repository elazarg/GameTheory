/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Holonomy.InfiniteBehavioralTailEvaluation
import UniformEquilibrium.Quitting.Boundary.Repair.TerminalDebtSingletonDescent
import UniformEquilibrium.Diagnostics.Uniform.NonexistenceCertificate

/-!
# Lexicographic terminal-debt descent by a literal root prefix

Prepending an exact one-stage Nash root against an actual continuation payoff
does not increase maximum terminal exploitability.  A positive singleton gap
for one player strictly decreases the sum of all playerwise terminal debts.
Consequently ties among maximal debtors require no separate treatment: maximum
debt is the primary monotone objective and total debt is a strict secondary
objective.

The profiles in this module are literal executable behavior profiles.  The
results do not identify a conditioned value, stored Bellman annotation, or
compactified boundary with the payoff of an actual continuation profile.
-/

noncomputable section

namespace GameTheory

open Math.Probability QuittingBoundaryHolonomy

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Global infimum of literal maximum terminal exploitability over all
behavior profiles. -/
def quittingTerminalExploitabilityInf [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : ℝ :=
  sInf (Set.range fun profile : (quittingGame reward).BehaviorProfile =>
    quittingTerminalExploitability reward profile)

theorem quittingTerminalExploitability_nonneg [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    0 ≤ quittingTerminalExploitability reward profile := by
  unfold quittingTerminalExploitability
  let who : ι := Classical.choice inferInstance
  exact (le_max_left 0 _).trans
    (le_finitePlayerMax
      (fun player => max 0
        (quittingContinuationBestResponseValue reward profile player -
          quittingTerminalPayoff reward profile player)) who)

theorem bddBelow_range_quittingTerminalExploitability [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    BddBelow (Set.range fun profile : (quittingGame reward).BehaviorProfile =>
      quittingTerminalExploitability reward profile) := by
  refine ⟨0, ?_⟩
  rintro value ⟨profile, rfl⟩
  exact quittingTerminalExploitability_nonneg reward profile

theorem quittingTerminalExploitabilityInf_le [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingTerminalExploitabilityInf reward ≤
      quittingTerminalExploitability reward profile := by
  exact csInf_le (bddBelow_range_quittingTerminalExploitability reward)
    ⟨profile, rfl⟩

/-- A uniform literal terminal exploitability gap lower-bounds the global
exploitability infimum. -/
theorem terminalExploitabilityGap_le_quittingTerminalExploitabilityInf
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {gap M : ℝ} (hexploit : HasTerminalExploitabilityGap reward gap)
    (hM : 0 ≤ M) (hreward : ∀ S player, |reward S player| ≤ M) :
    gap ≤ quittingTerminalExploitabilityInf reward := by
  unfold quittingTerminalExploitabilityInf
  have hprofiles : Set.Nonempty
      (Set.range fun profile : (quittingGame reward).BehaviorProfile =>
        quittingTerminalExploitability reward profile) :=
    ⟨quittingTerminalExploitability reward
        (quittingAlwaysContinueProfile reward),
      quittingAlwaysContinueProfile reward, rfl⟩
  apply le_csInf hprofiles
  rintro value ⟨profile, rfl⟩
  obtain ⟨who, deviation, hgain⟩ := hexploit profile
  have hbest := quittingTerminalPayoff_update_le_continuationBestResponseValue
    reward profile who deviation hM hreward
  have hdebt : gap ≤ quittingTerminalDeviationDebt reward profile who := by
    unfold quittingTerminalDeviationDebt
    linarith
  exact hdebt.trans ((le_max_right 0 _).trans
    (le_finitePlayerMax
      (fun player => max 0
        (quittingContinuationBestResponseValue reward profile player -
          quittingTerminalPayoff reward profile player)) who))

/-- Failure of uniform-equilibrium existence forces a positive global
literal terminal-exploitability infimum. -/
theorem quittingTerminalExploitabilityInf_pos_of_no_uniformEquilibriumPayoff
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hno : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    0 < quittingTerminalExploitabilityInf reward := by
  obtain ⟨gap, hgap, hexploit⟩ :=
    (not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap
      reward).mp hno
  exact hgap.trans_le
    (terminalExploitabilityGap_le_quittingTerminalExploitabilityInf
      reward hexploit hM hreward)

/-- Sum of playerwise literal terminal deviation debts. -/
def quittingTerminalDebtSum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) : ℝ :=
  ∑ who, quittingTerminalDeviationDebt reward profile who

/-- Exact root prefixing cannot increase literal maximum terminal
exploitability. -/
theorem quittingTerminalExploitability_rootThenContinuation_le
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hnash : IsεQuittingRootEndpointNash reward
      (fun player => quittingTerminalPayoff reward continuation player)
      0 root) :
    quittingTerminalExploitability reward
        (quittingRootThenContinuationProfile reward root continuation) ≤
      quittingTerminalExploitability reward continuation := by
  let base : Payoff ι :=
    fun player => quittingTerminalPayoff reward continuation player
  have hnashRoot : IsεQuittingRootNash reward base 0 root :=
    (isεQuittingRootEndpointNash_iff_isεQuittingRootNash
      reward base 0 root).mp hnash
  unfold quittingTerminalExploitability
  apply finitePlayerMax_le
  intro who
  have hscaled := quittingTerminalDeviationDebt_rootThenContinuation_le
    reward root continuation who hM hreward hnashRoot
  have hdebtNonneg := quittingTerminalDeviationDebt_nonneg
    reward continuation who hM hreward
  have hdebt : quittingTerminalDeviationDebt reward
      (quittingRootThenContinuationProfile reward root continuation) who ≤
      quittingTerminalDeviationDebt reward continuation who :=
    hscaled.trans (mul_le_of_le_one_left hdebtNonneg
      (quittingRootOpponentContinueMass_le_one root who))
  exact (max_le_max le_rfl hdebt).trans
    (le_finitePlayerMax
      (fun player => max 0
        (quittingContinuationBestResponseValue reward continuation player -
          quittingTerminalPayoff reward continuation player)) who)

/-- If one coordinate has a singleton gap, exact root prefixing strictly
decreases total terminal debt by the same quantitative amount as the
coordinatewise descent theorem. -/
theorem quittingTerminalDebtSum_rootThenContinuation_le_sub_min
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (who : ι) {M gap : ℝ} (hM : 0 ≤ M) (hgap : 0 < gap)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hsingleton : gap ≤ reward (quittingSingletonTerminal who) who -
      quittingTerminalPayoff reward continuation who)
    (hnash : IsεQuittingRootEndpointNash reward
      (fun player => quittingTerminalPayoff reward continuation player)
      0 root) :
    quittingTerminalDebtSum reward
        (quittingRootThenContinuationProfile reward root continuation) ≤
      quittingTerminalDebtSum reward continuation -
        min
          ((gap / (8 * M)) *
            quittingTerminalDeviationDebt reward continuation who)
          (gap / 2) := by
  let prefixed := quittingRootThenContinuationProfile reward root continuation
  let decrease := min
    ((gap / (8 * M)) *
      quittingTerminalDeviationDebt reward continuation who)
    (gap / 2)
  have hselected :
      quittingTerminalDeviationDebt reward prefixed who ≤
        quittingTerminalDeviationDebt reward continuation who - decrease := by
    simpa [prefixed, decrease] using
      quittingTerminalDeviationDebt_rootThenContinuation_le_sub_min
        reward root continuation who hM hgap hreward hsingleton hnash
  have hnashRoot : IsεQuittingRootNash reward
      (fun player => quittingTerminalPayoff reward continuation player)
      0 root :=
    (isεQuittingRootEndpointNash_iff_isεQuittingRootNash
      reward (fun player => quittingTerminalPayoff reward continuation player)
      0 root).mp hnash
  have hother : ∀ player,
      quittingTerminalDeviationDebt reward prefixed player ≤
        quittingTerminalDeviationDebt reward continuation player := by
    intro player
    have hscaled := quittingTerminalDeviationDebt_rootThenContinuation_le
      reward root continuation player hM hreward hnashRoot
    have hdebtNonneg := quittingTerminalDeviationDebt_nonneg
      reward continuation player hM hreward
    have hfactor := quittingRootOpponentContinueMass_le_one root player
    have hprefixedScaled :
        quittingTerminalDeviationDebt reward prefixed player ≤
          quittingRootOpponentContinueMass root player *
            quittingTerminalDeviationDebt reward continuation player := by
      simpa [prefixed] using hscaled
    exact hprefixedScaled.trans
      (mul_le_of_le_one_left hdebtNonneg hfactor)
  have hsumOther :
      ∑ player ∈ Finset.univ.erase who,
          quittingTerminalDeviationDebt reward prefixed player ≤
        ∑ player ∈ Finset.univ.erase who,
          quittingTerminalDeviationDebt reward continuation player := by
    exact Finset.sum_le_sum fun player _ => hother player
  unfold quittingTerminalDebtSum
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ who),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ who)]
  linarith

/-- A literal continuation with a singleton gap admits an exact Nash root
prefix that preserves maximum exploitability and strictly lowers total debt.
-/
theorem exists_exactRoot_terminalExploitability_le_and_debtSum_descent
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : (quittingGame reward).BehaviorProfile)
    (who : ι) {M gap : ℝ} (hM : 0 ≤ M) (hgap : 0 < gap)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hsingleton : gap ≤ reward (quittingSingletonTerminal who) who -
      quittingTerminalPayoff reward continuation who) :
    ∃ root : ι → PMF Bool,
      IsεQuittingRootEndpointNash reward
          (fun player => quittingTerminalPayoff reward continuation player)
          0 root ∧
      quittingTerminalExploitability reward
          (quittingRootThenContinuationProfile reward root continuation) ≤
        quittingTerminalExploitability reward continuation ∧
      quittingTerminalDebtSum reward
          (quittingRootThenContinuationProfile reward root continuation) ≤
        quittingTerminalDebtSum reward continuation -
          min
            ((gap / (8 * M)) *
              quittingTerminalDeviationDebt reward continuation who)
            (gap / 2) := by
  obtain ⟨root, hnash⟩ :=
    exists_isZeroQuittingRootEndpointNash_simplex reward
      (fun player => quittingTerminalPayoff reward continuation player)
  let root' := quittingRootOfSimplex root
  refine ⟨root', hnash, ?_, ?_⟩
  · exact quittingTerminalExploitability_rootThenContinuation_le
      reward root' continuation hM hreward hnash
  · exact quittingTerminalDebtSum_rootThenContinuation_le_sub_min
      reward root' continuation who hM hgap hreward hsingleton hnash

/-! ## Lexicographic minimality consumer -/

/-- Total-debt values realized inside a maximum-exploitability sublevel. -/
def quittingTerminalDebtSumSublevelValues [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (bound : ℝ) : Set ℝ :=
  {total | ∃ profile : (quittingGame reward).BehaviorProfile,
    quittingTerminalExploitability reward profile ≤ bound ∧
      total = quittingTerminalDebtSum reward profile}

theorem bddBelow_quittingTerminalDebtSumSublevelValues
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (bound : ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M) :
    BddBelow (quittingTerminalDebtSumSublevelValues reward bound) := by
  refine ⟨0, ?_⟩
  rintro total ⟨profile, _, rfl⟩
  unfold quittingTerminalDebtSum
  exact Finset.sum_nonneg fun player _ =>
    quittingTerminalDeviationDebt_nonneg reward profile player hM hreward

/-- Lexicographic near-minimizers of maximum terminal exploitability and then
total terminal debt exist at every positive accuracy. -/
theorem exists_lexicographicallyNearMinimal_terminalProfile
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {ε M : ℝ} (hε : 0 < ε) (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M) :
    ∃ profile : (quittingGame reward).BehaviorProfile,
      quittingTerminalExploitability reward profile ≤
          quittingTerminalExploitabilityInf reward + ε ∧
        quittingTerminalDebtSum reward profile <
          sInf (quittingTerminalDebtSumSublevelValues reward
            (quittingTerminalExploitabilityInf reward + ε)) + ε := by
  let maxValues : Set ℝ := Set.range fun profile :
      (quittingGame reward).BehaviorProfile =>
    quittingTerminalExploitability reward profile
  have hmaxNonempty : maxValues.Nonempty :=
    ⟨quittingTerminalExploitability reward
        (quittingAlwaysContinueProfile reward),
      quittingAlwaysContinueProfile reward, rfl⟩
  have hmaxBelow : BddBelow maxValues :=
    bddBelow_range_quittingTerminalExploitability reward
  have hmaxLt : sInf maxValues <
      quittingTerminalExploitabilityInf reward + ε := by
    dsimp [maxValues, quittingTerminalExploitabilityInf]
    linarith
  obtain ⟨maxValue, ⟨maxProfile, hmaxValue⟩, hmaxStrict⟩ :=
    (csInf_lt_iff hmaxBelow hmaxNonempty).mp hmaxLt
  have hmaxValue' :
      quittingTerminalExploitability reward maxProfile = maxValue := by
    simpa using hmaxValue
  have hmaxProfile : quittingTerminalExploitability reward maxProfile ≤
      quittingTerminalExploitabilityInf reward + ε := by
    rw [hmaxValue']
    exact hmaxStrict.le
  let sumValues := quittingTerminalDebtSumSublevelValues reward
    (quittingTerminalExploitabilityInf reward + ε)
  have hsumNonempty : sumValues.Nonempty :=
    ⟨quittingTerminalDebtSum reward maxProfile,
      maxProfile, hmaxProfile, rfl⟩
  have hsumBelow : BddBelow sumValues :=
    bddBelow_quittingTerminalDebtSumSublevelValues reward
      (quittingTerminalExploitabilityInf reward + ε) hM hreward
  have hsumLt : sInf sumValues < sInf sumValues + ε := by linarith
  obtain ⟨sumValue, ⟨profile, hprofileMax, hsumValue⟩, hsumStrict⟩ :=
    (csInf_lt_iff hsumBelow hsumNonempty).mp hsumLt
  refine ⟨profile, hprofileMax, ?_⟩
  dsimp [sumValues] at hsumValue hsumStrict ⊢
  rw [← hsumValue]
  exact hsumStrict

/-- Literal near-minimizers for the lexicographic objective
`(maximum terminal debt, total terminal debt)` with a positive-debt player
carrying a uniform singleton gap.  The player may depend on the accuracy. -/
def HasLexicographicallyNearMinimalSingletonGap
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (floor gap : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ (profile : (quittingGame reward).BehaviorProfile) (owner : ι),
      quittingTerminalExploitability reward profile ≤ floor + ε ∧
      quittingTerminalDebtSum reward profile <
        sInf (quittingTerminalDebtSumSublevelValues reward (floor + ε)) + ε ∧
      floor / 2 ≤ quittingTerminalDeviationDebt reward profile owner ∧
      gap ≤ reward (quittingSingletonTerminal owner) owner -
        quittingTerminalPayoff reward profile owner

/-- Fixed-player specialization of
`HasLexicographicallyNearMinimalSingletonGap`. -/
def HasLexicographicallyNearMinimalFixedOutsider
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (floor gap : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ profile : (quittingGame reward).BehaviorProfile,
      quittingTerminalExploitability reward profile ≤ floor + ε ∧
      quittingTerminalDebtSum reward profile <
        sInf (quittingTerminalDebtSumSublevelValues reward (floor + ε)) + ε ∧
      floor / 2 ≤ quittingTerminalDeviationDebt reward profile owner ∧
      gap ≤ reward (quittingSingletonTerminal owner) owner -
        quittingTerminalPayoff reward profile owner

/-- Strict root-prefix descent excludes a uniform singleton gap on any
positive-debt coordinate of a lexicographically near-minimal family.  Neither
the player nor a unique maximal debtor must persist across accuracies. -/
theorem not_hasLexicographicallyNearMinimalSingletonGap
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {M floor gap : ℝ}
    (hM : 0 < M) (hfloor : 0 < floor) (hgap : 0 < gap)
    (hreward : ∀ S player, |reward S player| ≤ M) :
    ¬ HasLexicographicallyNearMinimalSingletonGap reward floor gap := by
  intro hnear
  let scale := gap / (8 * M)
  let decrease := min (scale * (floor / 2)) (gap / 2)
  have hscale : 0 < scale := by
    dsimp [scale]
    positivity
  have hdecrease : 0 < decrease := by
    dsimp [decrease]
    exact lt_min (mul_pos hscale (half_pos hfloor)) (half_pos hgap)
  let ε := decrease / 2
  have hε : 0 < ε := half_pos hdecrease
  obtain ⟨profile, owner, hprofileMax, hprofileSum, hownerDebt, hsingleton⟩ :=
    hnear ε hε
  obtain ⟨root, hnash, hprefixedMax, hprefixedSum⟩ :=
    exists_exactRoot_terminalExploitability_le_and_debtSum_descent
      reward profile owner hM.le hgap hreward hsingleton
  let prefixed := quittingRootThenContinuationProfile reward root profile
  have hprefixedSublevel :
      quittingTerminalExploitability reward prefixed ≤ floor + ε := by
    exact hprefixedMax.trans hprofileMax
  have hinfLe :
      sInf (quittingTerminalDebtSumSublevelValues reward (floor + ε)) ≤
        quittingTerminalDebtSum reward prefixed := by
    apply csInf_le
    · exact bddBelow_quittingTerminalDebtSumSublevelValues
        reward (floor + ε) hM.le hreward
    · exact ⟨prefixed, hprefixedSublevel, rfl⟩
  have hdecreaseLe : decrease ≤
      min
        ((gap / (8 * M)) *
          quittingTerminalDeviationDebt reward profile owner)
        (gap / 2) := by
    have hmul : scale * (floor / 2) ≤
        scale * quittingTerminalDeviationDebt reward profile owner :=
      mul_le_mul_of_nonneg_left hownerDebt hscale.le
    simpa [decrease, scale] using min_le_min hmul le_rfl
  have hprefixedSum' :
      quittingTerminalDebtSum reward prefixed ≤
        quittingTerminalDebtSum reward profile - decrease := by
    dsimp [prefixed]
    exact hprefixedSum.trans (sub_le_sub_left hdecreaseLe _)
  dsimp [ε] at hprofileSum
  linarith

/-- Fixed-outsider corollary of the player-varying lexicographic no-go. -/
theorem not_hasLexicographicallyNearMinimalFixedOutsider
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) {M floor gap : ℝ}
    (hM : 0 < M) (hfloor : 0 < floor) (hgap : 0 < gap)
    (hreward : ∀ S player, |reward S player| ≤ M) :
    ¬ HasLexicographicallyNearMinimalFixedOutsider
      reward owner floor gap := by
  intro hfixed
  apply not_hasLexicographicallyNearMinimalSingletonGap
    reward hM hfloor hgap hreward
  intro ε hε
  obtain ⟨profile, hmax, hsum, hdebt, hsingleton⟩ := hfixed ε hε
  exact ⟨profile, owner, hmax, hsum, hdebt, hsingleton⟩

/-- In a putative counterexample, no player-varying uniform singleton gap can
persist on positive-debt coordinates of literal lexicographic near-minimizers.
-/
theorem no_uniformEquilibriumPayoff_implies_not_lexicographic_singletonGap
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {M gap : ℝ}
    (hM : 0 < M) (hgap : 0 < gap)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hno : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    ¬ HasLexicographicallyNearMinimalSingletonGap reward
      (quittingTerminalExploitabilityInf reward) gap := by
  apply not_hasLexicographicallyNearMinimalSingletonGap
    reward hM _ hgap hreward
  exact quittingTerminalExploitabilityInf_pos_of_no_uniformEquilibriumPayoff
    reward hM.le hreward hno

/-- In a putative counterexample, no fixed player with a positive singleton
gap can persist through literal lexicographic near-minimizers at the global
exploitability infimum. -/
theorem no_uniformEquilibriumPayoff_implies_not_lexicographic_fixedOutsider
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) {M gap : ℝ}
    (hM : 0 < M) (hgap : 0 < gap)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hno : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    ¬ HasLexicographicallyNearMinimalFixedOutsider reward owner
      (quittingTerminalExploitabilityInf reward) gap := by
  apply not_hasLexicographicallyNearMinimalFixedOutsider
    reward owner hM _ hgap hreward
  exact quittingTerminalExploitabilityInf_pos_of_no_uniformEquilibriumPayoff
    reward hM.le hreward hno

end GameTheory
