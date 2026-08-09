/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.NormalCore
import UniformEquilibrium.Quitting.Punishment.SoloQuitterEquilibrium
import UniformEquilibrium.Quitting.Punishment.ZeroSoloDisjunct

/-!
# The empty first normal-layer branch

This file proves a concrete strategic subcase of the corrected all-abnormal
regime.  Assume the first distinct-witness layer is empty.  Then every player
strictly prefers every other player's solo absorption to its own solo
absorption, after the playerwise normalization.

If every own solo reward is nonpositive, the repository's proved Never branch
applies.  Otherwise choose a player with positive own solo reward.  Strict
cross-player margins rule out the universal-joining side of the existing
solo-quitter rate dichotomy, so some positive stationary solo hazard satisfies
all inactive-player inequalities.  The landed owner-solo certification then
gives an exact terminal Nash profile, whose own terminal payoff is a
uniform-equilibrium payoff by the exact terminal-to-uniform consumer.

This is genuinely weaker than the full corrected all-abnormal lemma.  When the
first layer is nonempty but the corrected core is empty, the source proof uses
a last nonempty layer and a two-player small-hazard construction.  That
construction is not assumed here and remains the exact missing extension.
-/

noncomputable section

namespace GameTheory
namespace QuittingLCPClassification

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- Strictly positive cross-player singleton margins exclude the universal
joining-obstruction side of the solo-quitter rate dichotomy. -/
theorem exists_soloQuitterRate_of_strict_cross
    [Finite ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι)
    (hcross : ∀ other, other ≠ owner →
      quittingSoloReward reward other other <
        quittingSoloReward reward owner other) :
    ∃ p : ℝ, 0 < p ∧ p ≤ 1 ∧
      QuittingSoloQuitterCriterion reward owner p := by
  rcases exists_soloQuitterRate_or_universalJoining reward owner with
    hrate | huniversal
  · exact hrate
  · obtain ⟨other, hother, hweak⟩ :=
      exists_weak_preemptor_of_universalJoining
        reward owner huniversal
    exact False.elim ((not_le_of_gt (hcross other hother)) hweak)

/-- A positive own solo reward together with strict cross-player singleton
margins produces an exact stationary terminal Nash profile. -/
theorem exists_exact_stationary_terminalNash_of_positive_solo_strict_cross
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι)
    (howner : 0 < quittingSoloReward reward owner owner)
    (hcross : ∀ other, other ≠ owner →
      quittingSoloReward reward other other <
        quittingSoloReward reward owner other) :
    ∃ root : ι → PMF Bool,
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) 0
        (quittingStationaryProfile reward root) := by
  obtain ⟨p, hp0, hp1, hcriterion⟩ :=
    exists_soloQuitterRate_of_strict_cross reward owner hcross
  let hazard := quittingHazardCoin p hp0.le hp1
  refine ⟨quittingSoloStationaryRoot owner hazard, ?_⟩
  apply isεAsymptoticNash_soloStationary_exact
    reward owner hazard
  · simpa [hazard] using hp0
  · exact howner.le
  · intro other hother
    simpa [hazard] using hcriterion other hother

/-- Empty first corrected normal layer gives a strict normalized singleton
margin from every other player's own solo outcome to `owner`'s solo outcome. -/
theorem strict_cross_of_normalLayer_one_eq_empty
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hlayer : normalLayer (normalizedSoloMatrix reward) 1 = ∅)
    {owner other : ι} (hother : other ≠ owner) :
    quittingSoloReward reward other other <
      quittingSoloReward reward owner other := by
  have hnotle : ¬normalizedSoloMatrix reward other owner ≤ 0 := by
    intro hle
    have hmem : other ∈ normalLayer (normalizedSoloMatrix reward) 1 := by
      have hmem' : other ∈
          normalLayer (normalizedSoloMatrix reward) (0 + 1) := by
        refine (mem_normalLayer_succ
          (normalizedSoloMatrix reward) 0 other).2 ⟨by simp, ?_⟩
        exact ⟨owner, by simp, Ne.symm hother, hle⟩
      simpa using hmem'
    rw [hlayer] at hmem
    simp at hmem
  have hpositive : 0 < normalizedSoloMatrix reward other owner :=
    lt_of_not_ge hnotle
  rw [normalizedSoloMatrix_eq_projectiveLCPMatrix] at hpositive
  unfold quittingProjectiveLCPMatrix at hpositive
  have hdifference :
      0 < quittingSoloReward reward owner other -
        quittingSoloReward reward other other := by
    simpa [quittingSoloReward, quittingProjectiveSingletonTerminal] using
      hpositive
  exact sub_pos.mp hdifference

/-- **Concrete first-layer stationary theorem.**  If the first corrected
normal layer is empty, one stationary profile is an exact terminal Nash
profile.  The profile is Never in the zero-solo case and a positive-hazard
solo-quitter profile otherwise. -/
theorem exists_exact_stationary_terminalNash_of_normalLayer_one_eq_empty
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hlayer : normalLayer (normalizedSoloMatrix reward) 1 = ∅) :
    ∃ root : ι → PMF Bool,
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) 0
        (quittingStationaryProfile reward root) := by
  by_cases hzero : IsQuittingZeroSolo reward
  · refine ⟨fun _ => PMF.pure false, ?_⟩
    change (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0
      (quittingAlwaysContinueProfile reward)
    exact isZeroAsymptoticNash_quittingAlwaysContinue_of_zeroSolo
      reward hzero
  · have hpositive :
        ∃ owner : ι, 0 < quittingSoloReward reward owner owner := by
      by_contra hnone
      apply hzero
      intro owner
      have hnotpos : ¬0 < quittingSoloReward reward owner owner := by
        intro hpos
        exact hnone ⟨owner, hpos⟩
      have hnonpos : quittingSoloReward reward owner owner ≤ 0 :=
        le_of_not_gt hnotpos
      simpa [quittingSoloReward, quittingSingletonTerminal] using hnonpos
    obtain ⟨owner, howner⟩ := hpositive
    exact
      exists_exact_stationary_terminalNash_of_positive_solo_strict_cross
        reward owner howner
        (fun other hother =>
          strict_cross_of_normalLayer_one_eq_empty
            reward hlayer hother)

/-- The constructed exact stationary profile carries its own terminal payoff
directly to the uniform-payoff semantics. -/
theorem exists_exact_stationary_uniformPayoff_of_normalLayer_one_eq_empty
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hlayer : normalLayer (normalizedSoloMatrix reward) 1 = ∅) :
    ∃ root : ι → PMF Bool,
      (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) 0
          (quittingStationaryProfile reward root) ∧
        (quittingGame reward).IsUniformEquilibriumPayoff none
          (quittingTerminalPayoff reward
            (quittingStationaryProfile reward root)) := by
  obtain ⟨root, hexact⟩ :=
    exists_exact_stationary_terminalNash_of_normalLayer_one_eq_empty
      reward hlayer
  exact ⟨root, hexact,
    quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact
      reward (quittingStationaryProfile reward root) hexact⟩

/-- The exact first-layer profile supplies terminal approximate equilibria at
all positive errors, in the canonical quantifier shape. -/
theorem terminalNash_all_errors_of_normalLayer_one_eq_empty
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hlayer : normalLayer (normalizedSoloMatrix reward) 1 = ∅) :
    ∀ ε : ℝ, 0 < ε →
      ∃ profile : (quittingGame reward).BehaviorProfile,
        (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) ε profile := by
  obtain ⟨root, hexact⟩ :=
    exists_exact_stationary_terminalNash_of_normalLayer_one_eq_empty
      reward hlayer
  intro ε hε
  refine ⟨quittingStationaryProfile reward root, ?_⟩
  intro who deviation
  have h := hexact who deviation
  linarith

/-- The exact stationary profile's terminal payoff gives target-free
uniform-payoff existence. -/
theorem exists_uniformEquilibriumPayoff_of_normalLayer_one_eq_empty
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hlayer : normalLayer (normalizedSoloMatrix reward) 1 = ∅) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  obtain ⟨root, _, huniform⟩ :=
    exists_exact_stationary_uniformPayoff_of_normalLayer_one_eq_empty
      reward hlayer
  exact ⟨quittingTerminalPayoff reward
    (quittingStationaryProfile reward root), huniform⟩

end QuittingLCPClassification
end GameTheory
