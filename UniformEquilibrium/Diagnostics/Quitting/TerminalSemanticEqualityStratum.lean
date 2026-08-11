/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalDebtPrefixDescent
import UniformEquilibrium.Quitting.Root.TerminalSemanticPair

/-!
# Minimum-debt equality stratum of the literal semantic carrier

The compact closure of attainable prescribed/envelope pairs admits a minimum
of total literal debt.  Exact Nash prefixing preserves the carrier and weakly
decreases every nonnegative debt coordinate.  At a total-debt minimizer every
coordinate is therefore preserved exactly.

Every positive debt coordinate lies on the unit deleted-survival,
zero-exercise-premium face.  Two positive debt coordinates force the whole
root to all-Continue; a unique positive coordinate leaves only that player's
own marginal uncontrolled.  This is an exact finite-dimensional equality
stratum, not a realization of a conditioned boundary by one behavior profile.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.SurvivalWeightedObstruction
  QuittingBoundaryHolonomy
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Total debt of a finite-dimensional terminal semantic pair. -/
def quittingTerminalSemanticDebtSum
    (pair : QuittingTerminalSemanticPair ι) : ℝ :=
  ∑ who, quittingTerminalSemanticDebt pair who

/-- Maximum positive debt of a finite-dimensional terminal semantic pair. -/
def quittingTerminalSemanticExploitability [Nonempty ι]
    (pair : QuittingTerminalSemanticPair ι) : ℝ :=
  finitePlayerMax fun who => max 0 (quittingTerminalSemanticDebt pair who)

omit [Fintype ι] [DecidableEq ι] in
theorem continuous_quittingTerminalSemanticDebt (who : ι) :
    Continuous (fun pair : QuittingTerminalSemanticPair ι =>
      quittingTerminalSemanticDebt pair who) := by
  unfold quittingTerminalSemanticDebt
  have hfirst : Continuous
      (fun pair : QuittingTerminalSemanticPair ι => pair.1 who) := by
    fun_prop
  have hsecond : Continuous
      (fun pair : QuittingTerminalSemanticPair ι => pair.2 who) := by
    fun_prop
  exact hsecond.sub hfirst

omit [DecidableEq ι] in
theorem continuous_quittingTerminalSemanticDebtSum :
    Continuous (quittingTerminalSemanticDebtSum :
      QuittingTerminalSemanticPair ι → ℝ) := by
  unfold quittingTerminalSemanticDebtSum
  exact continuous_finsetSum
    (s := (Finset.univ : Finset ι)) fun who _ =>
      continuous_quittingTerminalSemanticDebt who

omit [DecidableEq ι] in
theorem continuous_quittingTerminalSemanticExploitability [Nonempty ι] :
    Continuous (quittingTerminalSemanticExploitability :
      QuittingTerminalSemanticPair ι → ℝ) := by
  unfold quittingTerminalSemanticExploitability finitePlayerMax
  apply Continuous.finset_sup'_apply Finset.univ_nonempty
  intro who _
  exact continuous_const.max (continuous_quittingTerminalSemanticDebt who)

/-- Actual semantic pairs have nonnegative debt in every coordinate. -/
theorem quittingTerminalSemanticDebt_nonneg_of_attainable
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {pair : QuittingTerminalSemanticPair ι}
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hpair : pair ∈ quittingAttainableTerminalSemanticPairs reward) :
    ∀ who, 0 ≤ quittingTerminalSemanticDebt pair who := by
  rintro who
  obtain ⟨profile, rfl⟩ := hpair
  exact quittingTerminalDeviationDebt_nonneg reward profile who hM hreward

/-- Nonnegative debt extends to the compact attainable-semantic closure. -/
theorem quittingTerminalSemanticDebt_nonneg_of_mem_carrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {pair : QuittingTerminalSemanticPair ι}
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward) :
    ∀ who, 0 ≤ quittingTerminalSemanticDebt pair who := by
  have hclosed : IsClosed {candidate : QuittingTerminalSemanticPair ι |
      ∀ who, 0 ≤ quittingTerminalSemanticDebt candidate who} := by
    rw [show {candidate : QuittingTerminalSemanticPair ι |
        ∀ who, 0 ≤ quittingTerminalSemanticDebt candidate who} =
      ⋂ who, {candidate | 0 ≤ quittingTerminalSemanticDebt candidate who} by
        ext candidate
        simp]
    exact isClosed_iInter fun who =>
      isClosed_le continuous_const
        (continuous_quittingTerminalSemanticDebt who)
  exact (closure_minimal
    (fun candidate hcandidate =>
      quittingTerminalSemanticDebt_nonneg_of_attainable
        reward hM hreward hcandidate)
    hclosed) hpair

/-- On actual pairs, semantic exploitability is literal terminal
exploitability. -/
theorem quittingTerminalSemanticExploitability_pair
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingTerminalSemanticExploitability
        (quittingTerminalSemanticPair reward profile) =
      quittingTerminalExploitability reward profile := rfl

/-- The global literal exploitability infimum lower-bounds every pair in the
attainable-semantic closure. -/
theorem quittingTerminalExploitabilityInf_le_semanticCarrier
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {pair : QuittingTerminalSemanticPair ι}
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward) :
    quittingTerminalExploitabilityInf reward ≤
      quittingTerminalSemanticExploitability pair := by
  have hclosed : IsClosed {candidate : QuittingTerminalSemanticPair ι |
      quittingTerminalExploitabilityInf reward ≤
        quittingTerminalSemanticExploitability candidate} :=
    isClosed_le continuous_const
      continuous_quittingTerminalSemanticExploitability
  apply (closure_minimal ?_ hclosed) hpair
  rintro candidate ⟨profile, rfl⟩
  change quittingTerminalExploitabilityInf reward ≤
    quittingTerminalSemanticExploitability
      (quittingTerminalSemanticPair reward profile)
  rw [quittingTerminalSemanticExploitability_pair]
  exact quittingTerminalExploitabilityInf_le reward profile

/-- Total semantic debt attains a minimum on the compact literal carrier. -/
theorem exists_minimum_quittingTerminalSemanticDebtSum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M) :
    ∃ pair ∈ quittingTerminalSemanticCarrier reward,
      ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum pair ≤
          quittingTerminalSemanticDebtSum candidate := by
  obtain ⟨pair, hpair, hmin⟩ :=
    (quittingTerminalSemanticCarrier_isCompact reward hM hreward).exists_isMinOn
      (quittingTerminalSemanticCarrier_nonempty reward)
      continuous_quittingTerminalSemanticDebtSum.continuousOn
  exact ⟨pair, hpair, fun candidate hcandidate => hmin hcandidate⟩

/-- A minimum-total-debt carrier point has an executable realizing sequence,
and both finite-dimensional debt objectives converge along that sequence. -/
theorem exists_profile_sequence_tendsto_minimumTerminalSemanticDebt
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M) :
    ∃ (pair : QuittingTerminalSemanticPair ι)
        (profiles : ℕ → (quittingGame reward).BehaviorProfile),
      pair ∈ quittingTerminalSemanticCarrier reward ∧
      (∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum pair ≤
          quittingTerminalSemanticDebtSum candidate) ∧
      Tendsto (fun n => quittingTerminalSemanticPair reward (profiles n))
        atTop (𝓝 pair) ∧
      Tendsto (fun n => quittingTerminalDebtSum reward (profiles n))
        atTop (𝓝 (quittingTerminalSemanticDebtSum pair)) ∧
      Tendsto (fun n => quittingTerminalExploitability reward (profiles n))
        atTop (𝓝 (quittingTerminalSemanticExploitability pair)) := by
  obtain ⟨pair, hpair, hmin⟩ :=
    exists_minimum_quittingTerminalSemanticDebtSum reward hM hreward
  obtain ⟨profiles, hprofiles⟩ :=
    exists_terminalProfile_sequence_tendsto_semanticPair reward pair hpair
  have hsum : Tendsto
      (fun n => quittingTerminalDebtSum reward (profiles n)) atTop
      (𝓝 (quittingTerminalSemanticDebtSum pair)) := by
    have hcontinuous :=
      continuous_quittingTerminalSemanticDebtSum.continuousAt.tendsto.comp
        hprofiles
    have hfunction :
        (quittingTerminalSemanticDebtSum ∘ fun n =>
          quittingTerminalSemanticPair reward (profiles n)) =
        (fun n => quittingTerminalDebtSum reward (profiles n)) := by
      funext n
      rfl
    rw [hfunction] at hcontinuous
    exact hcontinuous
  have hmax : Tendsto
      (fun n => quittingTerminalExploitability reward (profiles n)) atTop
      (𝓝 (quittingTerminalSemanticExploitability pair)) := by
    have hcontinuous :=
      continuous_quittingTerminalSemanticExploitability.continuousAt.tendsto.comp
        hprofiles
    have hfunction :
        (quittingTerminalSemanticExploitability ∘ fun n =>
          quittingTerminalSemanticPair reward (profiles n)) =
        (fun n => quittingTerminalExploitability reward (profiles n)) := by
      funext n
      exact quittingTerminalSemanticExploitability_pair reward (profiles n)
    rw [hfunction] at hcontinuous
    exact hcontinuous
  exact ⟨pair, profiles, hpair, hmin, hprofiles, hsum, hmax⟩

/-- At a minimum-total-debt semantic pair, every exact Nash prefix preserves
every debt coordinate. -/
theorem quittingTerminalSemanticDebt_prefix_eq_of_minimum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hmin : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hnash : IsεQuittingRootNash reward pair.1 0 root) :
    ∀ who,
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPrefix reward root pair) who =
        quittingTerminalSemanticDebt pair who := by
  let prefixed := quittingTerminalSemanticPrefix reward root pair
  have hprefixed : prefixed ∈ quittingTerminalSemanticCarrier reward :=
    quittingTerminalSemanticPrefix_mem_carrier
      reward root pair hM hreward hpair
  have hnonneg : ∀ who, 0 ≤ quittingTerminalSemanticDebt pair who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hM hreward hpair
  have hcoordinate : ∀ who,
      quittingTerminalSemanticDebt prefixed who ≤
        quittingTerminalSemanticDebt pair who := fun who =>
    quittingTerminalSemanticDebt_prefix_le
      reward pair root who (hnonneg who) hnash
  have hsum_le : quittingTerminalSemanticDebtSum prefixed ≤
      quittingTerminalSemanticDebtSum pair := by
    unfold quittingTerminalSemanticDebtSum
    exact Finset.sum_le_sum fun who _ => hcoordinate who
  have hsum_eq : quittingTerminalSemanticDebtSum prefixed =
      quittingTerminalSemanticDebtSum pair :=
    le_antisymm hsum_le (hmin prefixed hprefixed)
  have hdiff_sum :
      ∑ who, (quittingTerminalSemanticDebt pair who -
        quittingTerminalSemanticDebt prefixed who) = 0 := by
    rw [Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr hsum_eq.symm
  have hdiff_nonneg : ∀ who ∈ (Finset.univ : Finset ι),
      0 ≤ quittingTerminalSemanticDebt pair who -
        quittingTerminalSemanticDebt prefixed who := fun who _ =>
    sub_nonneg.mpr (hcoordinate who)
  have hzero :=
    (Finset.sum_eq_zero_iff_of_nonneg hdiff_nonneg).mp hdiff_sum
  intro who
  have := hzero who (Finset.mem_univ who)
  linarith

/-- Every positive debt coordinate at a minimum-total-debt semantic pair lies
on the exact unit-survival, zero-premium face of every exact Nash root. -/
theorem quittingTerminalSemantic_minimum_positiveDebt_face
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hmin : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hnash : IsεQuittingRootNash reward pair.1 0 root)
    (who : ι) (hpositive : 0 < quittingTerminalSemanticDebt pair who) :
    quittingRootOpponentContinueMass root who = 1 ∧
      quittingRootExercisePremium reward pair.1 root who = 0 := by
  have heq := quittingTerminalSemanticDebt_prefix_eq_of_minimum
    reward pair root hM hreward hpair hmin hnash who
  rw [quittingTerminalSemanticDebt_prefix_eq_blockAct
    reward pair root who hpositive.le hnash] at heq
  simpa [quittingTerminalSemanticDebtBlock] using
    (Block.act_eq_self_iff_of_pos
      (quittingTerminalSemanticDebtBlock reward pair root who)
      () hpositive).mp heq

/-- A positive debtor at the semantic minimum forces every opponent's Quit
mass to vanish exactly. -/
theorem quittingTerminalSemantic_minimum_positiveDebt_opponents_quit_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hmin : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hnash : IsεQuittingRootNash reward pair.1 0 root)
    {who other : ι} (hpositive : 0 < quittingTerminalSemanticDebt pair who)
    (hne : other ≠ who) :
    (root other true).toReal = 0 := by
  have hface := quittingTerminalSemantic_minimum_positiveDebt_face
    reward pair root hM hreward hpair hmin hnash who hpositive
  have habs : quittingRootOpponentAbsorptionMass root who = 0 := by
    have hcomplement :=
      quittingRootOpponentContinueMass_eq_one_sub_absorptionMass root who
    linarith [hface.1]
  have hle :=
    quittingRoot_quitProbability_le_opponentAbsorptionMass_of_ne root hne
  rw [habs] at hle
  exact le_antisymm hle ENNReal.toReal_nonneg

/-- Two distinct positive debts at the semantic minimum force every displayed
Quit mass to vanish. -/
theorem quittingTerminalSemantic_minimum_twoPositiveDebt_all_quit_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hmin : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hnash : IsεQuittingRootNash reward pair.1 0 root)
    {first second : ι} (hdistinct : first ≠ second)
    (hfirst : 0 < quittingTerminalSemanticDebt pair first)
    (hsecond : 0 < quittingTerminalSemanticDebt pair second) :
    ∀ player, (root player true).toReal = 0 := by
  intro player
  by_cases hplayer : player = first
  · subst player
    exact quittingTerminalSemantic_minimum_positiveDebt_opponents_quit_eq_zero
      reward pair root hM hreward hpair hmin hnash hsecond hdistinct
  · exact quittingTerminalSemantic_minimum_positiveDebt_opponents_quit_eq_zero
      reward pair root hM hreward hpair hmin hnash hfirst hplayer

/-- In the absence of a uniform payoff, a minimum-total-debt semantic pair
has a positive debt coordinate and every exact Nash root lies on that
coordinate's unit-survival, zero-premium face. -/
theorem exists_positive_minimumTerminalSemanticDebt_face_of_no_uniformPayoff
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hno : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    ∃ (pair : QuittingTerminalSemanticPair ι) (root : ι → PMF Bool),
      pair ∈ quittingTerminalSemanticCarrier reward ∧
      IsεQuittingRootNash reward pair.1 0 root ∧
      (∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum pair ≤
          quittingTerminalSemanticDebtSum candidate) ∧
      (∃ who, 0 < quittingTerminalSemanticDebt pair who) ∧
      ∀ who, 0 < quittingTerminalSemanticDebt pair who →
        quittingRootOpponentContinueMass root who = 1 ∧
          quittingRootExercisePremium reward pair.1 root who = 0 := by
  obtain ⟨pair, hpair, hmin⟩ :=
    exists_minimum_quittingTerminalSemanticDebtSum reward hM hreward
  obtain ⟨simplexRoot, hnash⟩ :=
    exists_isZeroQuittingRootEndpointNash_simplex reward pair.1
  let root := quittingRootOfSimplex simplexRoot
  have hnash' : IsεQuittingRootNash reward pair.1 0 root :=
    (isεQuittingRootEndpointNash_iff_isεQuittingRootNash
      reward pair.1 0 root).mp hnash
  have hfloor : 0 < quittingTerminalExploitabilityInf reward :=
    quittingTerminalExploitabilityInf_pos_of_no_uniformEquilibriumPayoff
      reward hM hreward hno
  have hpositive : ∃ who, 0 < quittingTerminalSemanticDebt pair who := by
    by_contra hnot
    have hnot' : ∀ who, quittingTerminalSemanticDebt pair who ≤ 0 := by
      intro who
      exact le_of_not_gt fun hpositive => hnot ⟨who, hpositive⟩
    have hzero : ∀ who, quittingTerminalSemanticDebt pair who = 0 := by
      intro who
      exact le_antisymm (hnot' who)
        (quittingTerminalSemanticDebt_nonneg_of_mem_carrier
          reward hM hreward hpair who)
    have hexploitZero : quittingTerminalSemanticExploitability pair = 0 := by
      unfold quittingTerminalSemanticExploitability finitePlayerMax
      simp [hzero]
    have hcarrierFloor :=
      quittingTerminalExploitabilityInf_le_semanticCarrier reward hpair
    rw [hexploitZero] at hcarrierFloor
    linarith
  refine ⟨pair, root, hpair, hnash', hmin, hpositive, ?_⟩
  intro who hwho
  exact quittingTerminalSemantic_minimum_positiveDebt_face
    reward pair root hM hreward hpair hmin hnash' who hwho

end GameTheory
