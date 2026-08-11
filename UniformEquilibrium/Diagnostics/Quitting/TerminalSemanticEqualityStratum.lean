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

omit [Fintype ι] in
/-- If every displayed opponent has zero Quit mass, forcing the selected
player to Continue produces the all-Continue root. -/
theorem quittingRoot_update_pureContinue_eq_allContinue_of_opponents_quit_eq_zero
    (root : ι → PMF Bool) (who : ι)
    (hzero : ∀ other, other ≠ who → (root other true).toReal = 0) :
    Function.update root who (PMF.pure false) =
      (quittingAllContinueRoot : ι → PMF Bool) := by
  funext player
  by_cases hplayer : player = who
  · subst player
    simp [quittingAllContinueRoot]
  · rw [Function.update_of_ne hplayer]
    exact (pmf_eq_pure_false_of_apply_true_toReal_eq_zero
      (root player) (hzero player hplayer)).trans rfl

/-- On the deleted all-Continue face, the selected player's two endpoints
are exactly its singleton reward and its declared continuation coordinate.
-/
theorem quittingRoot_endpoints_eq_singleton_tail_of_opponents_quit_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (hzero : ∀ other, other ≠ who → (root other true).toReal = 0) :
    quittingRootQuitPayoff reward tail root who =
        reward (quittingSingletonTerminal who) who ∧
      quittingRootContinuePayoff reward tail root who = tail who := by
  have hupdate :=
    quittingRoot_update_pureContinue_eq_allContinue_of_opponents_quit_eq_zero
      root who hzero
  constructor
  · unfold quittingRootQuitPayoff
    have hroot : Function.update root who (PMF.pure true) =
        Function.update (quittingAllContinueRoot : ι → PMF Bool) who
          (PMF.pure true) := by
      funext player
      by_cases hplayer : player = who
      · subst player
        simp
      · simp only [Function.update_of_ne hplayer]
        have hpure := pmf_eq_pure_false_of_apply_true_toReal_eq_zero
          (root player) (hzero player hplayer)
        simpa [quittingAllContinueRoot] using hpure
    rw [hroot]
    exact quittingRootQuitPayoff_allContinueRoot reward tail who
  · unfold quittingRootContinuePayoff
    rw [hupdate]
    have hself :
        Function.update (quittingAllContinueRoot : ι → PMF Bool) who
            (PMF.pure false) = quittingAllContinueRoot := by
      exact Function.update_eq_self who quittingAllContinueRoot
    rw [← hself]
    simpa only [quittingRootContinuePayoff] using
      (quittingRootContinuePayoff_allContinueRoot reward tail who)

/-- A positive minimum-debt coordinate dominates its singleton quitting
reward.  This conclusion uses the exact Nash root supplied at that semantic
point; it does not extend to arbitrary carrier coordinates. -/
theorem quittingTerminalSemantic_minimum_positiveDebt_singleton_le
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
    reward (quittingSingletonTerminal who) who ≤ pair.1 who := by
  have hface := quittingTerminalSemantic_minimum_positiveDebt_face
    reward pair root hM hreward hpair hmin hnash who hpositive
  have hzero : ∀ other, other ≠ who →
      (root other true).toReal = 0 := by
    intro other hne
    exact quittingTerminalSemantic_minimum_positiveDebt_opponents_quit_eq_zero
      reward pair root hM hreward hpair hmin hnash hpositive hne
  have hendpoints :=
    quittingRoot_endpoints_eq_singleton_tail_of_opponents_quit_eq_zero
      reward pair.1 root who hzero
  have hpremium : quittingRootEndpointDifference reward pair.1 root who ≤ 0 :=
    max_eq_left_iff.mp (by
      simpa [quittingRootExercisePremium] using hface.2.symm)
  simpa [quittingRootEndpointDifference, hendpoints.1, hendpoints.2] using
    hpremium

/-- If a positive minimum-debt coordinate itself Quits with positive mass at
an exact Nash root, then its singleton reward equals its prescribed value.
The root's only possible absorption is that player's singleton event. -/
theorem quittingTerminalSemantic_minimum_positiveDebt_singleton_eq_of_quit_pos
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
    (who : ι) (hpositive : 0 < quittingTerminalSemanticDebt pair who)
    (hquit : 0 < (root who true).toReal) :
    reward (quittingSingletonTerminal who) who = pair.1 who := by
  have hzero : ∀ other, other ≠ who →
      (root other true).toReal = 0 := by
    intro other hne
    exact quittingTerminalSemantic_minimum_positiveDebt_opponents_quit_eq_zero
      reward pair root hM hreward hpair hmin hnash hpositive hne
  have hendpoints :=
    quittingRoot_endpoints_eq_singleton_tail_of_opponents_quit_eq_zero
      reward pair.1 root who hzero
  have hendpoint : IsεQuittingRootEndpointNash reward pair.1 0 root :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward pair.1 root).mpr hnash
  have hdiff_nonneg :
      0 ≤ quittingRootEndpointDifference reward pair.1 root who := by
    have hproduct := (hendpoint who).2
    simp only [neg_zero] at hproduct
    exact nonneg_of_mul_nonneg_left (by simpa [mul_comm] using hproduct) hquit
  have hprescribed_le_singleton :
      pair.1 who ≤ reward (quittingSingletonTerminal who) who := by
    simpa [quittingRootEndpointDifference, hendpoints.1, hendpoints.2] using
      hdiff_nonneg
  exact le_antisymm
    (quittingTerminalSemantic_minimum_positiveDebt_singleton_le
      reward pair root hM hreward hpair hmin hnash who hpositive)
    hprescribed_le_singleton

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

/-- **Minimum-stratum alternative.**  Given a positive debt coordinate and
an exact Nash root at a minimum semantic pair, either all-Continue is itself
an exact Nash semantic self-loop, or the positive-debt set has a unique owner
and the selected root is a genuine solo-owner deterrence row.

In the deterrence branch the owner Quits with positive mass and is exactly
singleton-tight.  Every outsider Continues purely and satisfies the exact
Quit-versus-Continue endpoint inequality.  At least one outsider has a
singleton reward strictly above its declared continuation, so that inequality
cannot be explained by the all-Continue row: the owner's possible exit and
the associated collision outcomes are essential. -/
theorem quittingTerminalSemantic_minimum_stratum_alternative
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
    (first : ι) (hfirst : 0 < quittingTerminalSemanticDebt pair first) :
    (IsεQuittingRootNash reward pair.1 0
          (quittingAllContinueRoot : ι → PMF Bool) ∧
        quittingTerminalSemanticPrefix reward quittingAllContinueRoot pair =
          pair) ∨
      ∃ owner other,
        0 < quittingTerminalSemanticDebt pair owner ∧
        (∀ player, 0 < quittingTerminalSemanticDebt pair player →
          player = owner) ∧
        other ≠ owner ∧
        pair.1 other < reward (quittingSingletonTerminal other) other ∧
        0 < (root owner true).toReal ∧
        reward (quittingSingletonTerminal owner) owner = pair.1 owner ∧
        (∀ player, player ≠ owner → root player = PMF.pure false) ∧
        ∀ player, player ≠ owner →
          quittingRootQuitPayoff reward pair.1 root player ≤
            quittingRootContinuePayoff reward pair.1 root player := by
  have hdebt : ∀ who, 0 ≤ quittingTerminalSemanticDebt pair who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hM hreward hpair
  by_cases hsecond : ∃ second, second ≠ first ∧
      0 < quittingTerminalSemanticDebt pair second
  · obtain ⟨second, hdistinct, hsecondPositive⟩ := hsecond
    have hzero :=
      quittingTerminalSemantic_minimum_twoPositiveDebt_all_quit_eq_zero
        reward pair root hM hreward hpair hmin hnash
          (first := first) (second := second) hdistinct.symm hfirst
            hsecondPositive
    have hroot : root = (quittingAllContinueRoot : ι → PMF Bool) := by
      funext player
      have hpure := pmf_eq_pure_false_of_apply_true_toReal_eq_zero
        (root player) (hzero player)
      simpa [quittingAllContinueRoot] using hpure
    have hnashAll : IsεQuittingRootNash reward pair.1 0
        (quittingAllContinueRoot : ι → PMF Bool) := by
      simpa [hroot] using hnash
    exact Or.inl ⟨hnashAll,
      quittingTerminalSemanticPrefix_allContinue_eq_of_isZeroNash
        reward pair hdebt hnashAll⟩
  · have hunique : ∀ player,
        0 < quittingTerminalSemanticDebt pair player → player = first := by
      intro player hplayer
      by_contra hne
      exact hsecond ⟨player, hne, hplayer⟩
    by_cases hnashAll : IsεQuittingRootNash reward pair.1 0
        (quittingAllContinueRoot : ι → PMF Bool)
    · exact Or.inl ⟨hnashAll,
        quittingTerminalSemanticPrefix_allContinue_eq_of_isZeroNash
          reward pair hdebt hnashAll⟩
    · have hnotDominate : ¬ ∀ player,
          reward (quittingSingletonTerminal player) player ≤ pair.1 player :=
        fun hdominate => hnashAll
          ((isZeroQuittingRootNash_allContinue_iff_singleton_le
            reward pair.1).mpr hdominate)
      push Not at hnotDominate
      obtain ⟨other, hotherGain⟩ := hnotDominate
      have hfirstDominate :
          reward (quittingSingletonTerminal first) first ≤ pair.1 first :=
        quittingTerminalSemantic_minimum_positiveDebt_singleton_le
          reward pair root hM hreward hpair hmin hnash first hfirst
      have hotherNe : other ≠ first := by
        intro heq
        subst other
        exact (not_lt_of_ge hfirstDominate) hotherGain
      have hzeroOpponent : ∀ player, player ≠ first →
          (root player true).toReal = 0 := by
        intro player hne
        exact
          quittingTerminalSemantic_minimum_positiveDebt_opponents_quit_eq_zero
            reward pair root hM hreward hpair hmin hnash hfirst hne
      have hpureOpponent : ∀ player, player ≠ first →
          root player = PMF.pure false := by
        intro player hne
        exact pmf_eq_pure_false_of_apply_true_toReal_eq_zero
          (root player) (hzeroOpponent player hne)
      have hownerQuit : 0 < (root first true).toReal := by
        by_contra hnot
        have hownerZero : (root first true).toReal = 0 :=
          le_antisymm (le_of_not_gt hnot) ENNReal.toReal_nonneg
        have hroot : root =
            (quittingAllContinueRoot : ι → PMF Bool) := by
          funext player
          by_cases hplayer : player = first
          · subst player
            have hpure := pmf_eq_pure_false_of_apply_true_toReal_eq_zero
              (root first) hownerZero
            simpa [quittingAllContinueRoot] using hpure
          · simpa [quittingAllContinueRoot] using
              (hpureOpponent player hplayer)
        apply hnashAll
        simpa [hroot] using hnash
      have hownerTight :=
        quittingTerminalSemantic_minimum_positiveDebt_singleton_eq_of_quit_pos
          reward pair root hM hreward hpair hmin hnash first hfirst hownerQuit
      have houtsiderEndpoint : ∀ player, player ≠ first →
          quittingRootQuitPayoff reward pair.1 root player ≤
            quittingRootContinuePayoff reward pair.1 root player := by
        intro player hne
        have hendpoint : IsεQuittingRootEndpointNash reward pair.1 0 root :=
          (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
            reward pair.1 root).mpr hnash
        have hdiff :=
          quittingRootEndpointDifference_nonpos_of_quitProbability_eq_zero
            reward pair.1 root player hendpoint (hzeroOpponent player hne)
        simpa [quittingRootEndpointDifference] using hdiff
      exact Or.inr ⟨first, other, hfirst, hunique, hotherNe, hotherGain,
        hownerQuit, hownerTight, hpureOpponent, houtsiderEndpoint⟩

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
