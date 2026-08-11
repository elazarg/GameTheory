/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Bellman.Finite.NashBellmanSpine
import UniformEquilibrium.Quitting.Root.TerminalDebtBlock

/-!
# Compact carrier of literal terminal semantic pairs

An actual behavior profile determines a finite-dimensional pair consisting of
its prescribed terminal payoff and its all-behavior best-response envelope.
The closure of these attainable pairs is compact under a uniform reward bound.

Prefixing by any fixed product root is an explicit continuous map on semantic
pairs.  The map agrees exactly with literal root/profile splicing and therefore
preserves the attainable closure.  No conditioned payoff, stored Bellman
annotation, or externally prescribed cap is used.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.ProbabilityMassFunction
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Finite-dimensional prescribed/envelope pair of terminal semantics. -/
abbrev QuittingTerminalSemanticPair (ι : Type) := Payoff ι × Payoff ι

/-- Literal prescribed payoff and all-behavior envelope of one executable
behavior profile. -/
def quittingTerminalSemanticPair
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    QuittingTerminalSemanticPair ι :=
  (fun who => quittingTerminalPayoff reward profile who,
    fun who => quittingContinuationBestResponseValue reward profile who)

/-- Explicit finite-dimensional action of one root prefix on a terminal
semantic pair. -/
def quittingTerminalSemanticPrefix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (pair : QuittingTerminalSemanticPair ι) :
    QuittingTerminalSemanticPair ι :=
  (quittingRootSuccessorPayoff reward pair.1 root,
    fun who =>
      max
        (quittingRootQuitPayoff reward pair.1 root who)
        (quittingRootContinuePayoff reward
          (Function.update pair.1 who (pair.2 who)) root who))

/-- Playerwise debt coordinate of a terminal semantic pair. -/
def quittingTerminalSemanticDebt
    (pair : QuittingTerminalSemanticPair ι) (who : ι) : ℝ :=
  pair.2 who - pair.1 who

/-- Survival block induced by a finite-dimensional semantic pair and one
root. -/
def quittingTerminalSemanticDebtBlock
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (who : ι) :
    Math.SurvivalWeightedObstruction.Block Unit where
  survival := quittingRootOpponentContinueMass root who
  survival_nonneg := quittingRootOpponentContinueMass_nonneg root who
  survival_le_one := quittingRootOpponentContinueMass_le_one root who
  charge :=
    { value := fun _ => quittingRootExercisePremium reward pair.1 root who
      nonneg := fun _ => quittingRootExercisePremium_nonneg
        reward pair.1 root who }

/-- Exact positive-part debt action on an abstract semantic pair.  The only
semantic hypotheses are nonnegative input debt and exact root Nash against the
prescribed coordinate. -/
theorem quittingTerminalSemanticDebt_prefix_eq_blockAct
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (who : ι)
    (hdebt : 0 ≤ quittingTerminalSemanticDebt pair who)
    (hnash : IsεQuittingRootNash reward pair.1 0 root) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPrefix reward root pair) who =
      (quittingTerminalSemanticDebtBlock reward pair root who).act ()
        (quittingTerminalSemanticDebt pair who) := by
  let debt := quittingTerminalSemanticDebt pair who
  let quitValue := quittingRootQuitPayoff reward pair.1 root who
  let continueValue := quittingRootContinuePayoff reward pair.1 root who
  let survived := quittingRootOpponentContinueMass root who * debt
  have hsurvived : 0 ≤ survived :=
    mul_nonneg (quittingRootOpponentContinueMass_nonneg root who) hdebt
  have hbest : pair.2 who = pair.1 who + debt := by
    dsimp [debt, quittingTerminalSemanticDebt]
    ring
  unfold quittingTerminalSemanticDebt quittingTerminalSemanticPrefix
  dsimp only
  rw [quittingRootSuccessorPayoff_eq_max_of_isZeroNash
    reward pair.1 root who hnash, hbest,
    quittingRootContinuePayoff_update_add]
  dsimp [Math.SurvivalWeightedObstruction.Block.act,
    quittingTerminalSemanticDebtBlock, quittingRootExercisePremium]
  rw [show pair.1 who + debt - pair.1 who = debt by ring]
  change max quitValue (continueValue + survived) -
      max quitValue continueValue =
    max 0 (survived - max 0 (quitValue - continueValue))
  exact Math.SurvivalWeightedObstruction.Block.max_add_sub_max_eq_posPart_sub_posPart
    quitValue continueValue survived hsurvived

/-- Exact Nash prefixing weakly decreases a nonnegative semantic debt
coordinate. -/
theorem quittingTerminalSemanticDebt_prefix_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (who : ι)
    (hdebt : 0 ≤ quittingTerminalSemanticDebt pair who)
    (hnash : IsεQuittingRootNash reward pair.1 0 root) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPrefix reward root pair) who ≤
      quittingTerminalSemanticDebt pair who := by
  rw [quittingTerminalSemanticDebt_prefix_eq_blockAct
    reward pair root who hdebt hnash]
  exact Math.SurvivalWeightedObstruction.Block.act_le_debt
    (quittingTerminalSemanticDebtBlock reward pair root who) () hdebt

/-- The semantic prefix action is exactly literal profile splicing. -/
theorem quittingTerminalSemanticPair_rootThenContinuation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M) :
    quittingTerminalSemanticPair reward
        (quittingRootThenContinuationProfile reward root continuation) =
      quittingTerminalSemanticPrefix reward root
        (quittingTerminalSemanticPair reward continuation) := by
  apply Prod.ext
  · funext who
    exact quittingTerminalPayoff_rootThenContinuation_eq
      reward root continuation who
  · funext who
    exact quittingContinuationBestResponseValue_rootThenContinuation_eq_max
      reward root continuation who hM hreward

/-- The all-behavior terminal envelope obeys the same reward bound as every
terminal payoff. -/
theorem abs_quittingContinuationBestResponseValue_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M) :
    |quittingContinuationBestResponseValue reward profile who| ≤ M := by
  let values : Set ℝ := Set.range fun deviation :
      (quittingGame reward).BehaviorStrategy who =>
    quittingTerminalPayoff reward (Function.update profile who deviation) who
  have hnonempty : values.Nonempty :=
    ⟨quittingTerminalPayoff reward
        (Function.update profile who (profile who)) who,
      profile who, rfl⟩
  have hbounded : BddAbove values := by
    refine ⟨M, ?_⟩
    rintro value ⟨deviation, rfl⟩
    exact (le_abs_self _).trans
      (abs_quittingTerminalPayoff_le reward
        (Function.update profile who deviation) who hM hreward)
  have hupper : sSup values ≤ M := by
    apply csSup_le hnonempty
    rintro value ⟨deviation, rfl⟩
    exact le_of_abs_le (abs_quittingTerminalPayoff_le reward
      (Function.update profile who deviation) who hM hreward)
  have hlower : -M ≤ sSup values := by
    have hmember : quittingTerminalPayoff reward profile who ∈ values := by
      refine ⟨profile who, ?_⟩
      simp
    have hpayoff : -M ≤ quittingTerminalPayoff reward profile who :=
      neg_le_of_abs_le
        (abs_quittingTerminalPayoff_le reward profile who hM hreward)
    exact hpayoff.trans (le_csSup hbounded hmember)
  change |sSup values| ≤ M
  exact abs_le.mpr ⟨hlower, hupper⟩

/-- Uniform coordinate box for terminal semantic pairs. -/
def quittingTerminalSemanticBox (ι : Type) [Fintype ι] (M : ℝ) :
    Set (QuittingTerminalSemanticPair ι) :=
  Set.Icc (fun _ => -M) (fun _ => M) ×ˢ
    Set.Icc (fun _ => -M) (fun _ => M)

omit [DecidableEq ι] in
theorem quittingTerminalSemanticBox_isCompact (M : ℝ) :
    IsCompact (quittingTerminalSemanticBox ι M) :=
  isCompact_Icc.prod isCompact_Icc

/-- Every literal semantic pair lies in the reward box. -/
theorem quittingTerminalSemanticPair_mem_box
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M) :
    quittingTerminalSemanticPair reward profile ∈
      quittingTerminalSemanticBox ι M := by
  constructor <;> constructor
  · intro who
    exact neg_le_of_abs_le
      (abs_quittingTerminalPayoff_le reward profile who hM hreward)
  · intro who
    exact le_of_abs_le
      (abs_quittingTerminalPayoff_le reward profile who hM hreward)
  · intro who
    exact neg_le_of_abs_le
      (abs_quittingContinuationBestResponseValue_le
        reward profile who hM hreward)
  · intro who
    exact le_of_abs_le
      (abs_quittingContinuationBestResponseValue_le
        reward profile who hM hreward)

/-- Set of finite-dimensional terminal semantic pairs realized by executable
behavior profiles. -/
def quittingAttainableTerminalSemanticPairs
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Set (QuittingTerminalSemanticPair ι) :=
  Set.range (quittingTerminalSemanticPair reward)

/-- Compactified carrier of attainable terminal semantic pairs. -/
def quittingTerminalSemanticCarrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Set (QuittingTerminalSemanticPair ι) :=
  closure (quittingAttainableTerminalSemanticPairs reward)

theorem quittingTerminalSemanticCarrier_nonempty
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (quittingTerminalSemanticCarrier reward).Nonempty := by
  apply Set.Nonempty.mono subset_closure
  exact ⟨quittingTerminalSemanticPair reward
      (quittingAlwaysContinueProfile reward),
    quittingAlwaysContinueProfile reward, rfl⟩

/-- Every point of the semantic carrier is the sequential limit of literal
semantic pairs of executable behavior profiles. -/
theorem exists_terminalProfile_sequence_tendsto_semanticPair
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward) :
    ∃ profiles : ℕ → (quittingGame reward).BehaviorProfile,
      Tendsto (fun n => quittingTerminalSemanticPair reward (profiles n))
        atTop (𝓝 pair) := by
  obtain ⟨pairs, hpairs, htendsto⟩ := mem_closure_iff_seq_limit.mp hpair
  choose profiles hprofiles using hpairs
  refine ⟨profiles, ?_⟩
  simpa only [hprofiles] using htendsto

/-- The attainable semantic closure is compact under a uniform reward bound.
-/
theorem quittingTerminalSemanticCarrier_isCompact
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M) :
    IsCompact (quittingTerminalSemanticCarrier reward) := by
  apply (quittingTerminalSemanticBox_isCompact (ι := ι) M).of_isClosed_subset
    isClosed_closure
  apply closure_minimal
  · rintro pair ⟨profile, rfl⟩
    exact quittingTerminalSemanticPair_mem_box reward profile hM hreward
  · exact (quittingTerminalSemanticBox_isCompact (ι := ι) M).isClosed

/-- Prefixing by a fixed root is continuous on finite-dimensional semantic
pairs. -/
theorem continuous_quittingTerminalSemanticPrefix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) :
    Continuous (quittingTerminalSemanticPrefix reward root) := by
  let simplexRoot : QuittingRootSimplex ι :=
    fun who => stdSimplexEquiv (root who)
  have hroot : quittingRootOfSimplex simplexRoot = root := by
    funext who
    exact (stdSimplexEquiv (α := Bool)).symm_apply_apply (root who)
  have hprescribed : Continuous (fun pair : QuittingTerminalSemanticPair ι =>
      quittingRootSuccessorPayoff reward pair.1 root) := by
    have hmap : Continuous (fun pair : QuittingTerminalSemanticPair ι =>
        (pair.1, simplexRoot)) := continuous_fst.prodMk continuous_const
    have hcontinuous :=
      (continuous_quittingRootSuccessorPayoff_simplex reward).comp hmap
    change Continuous (fun pair : QuittingTerminalSemanticPair ι =>
      quittingRootSuccessorPayoff reward pair.1
        (quittingRootOfSimplex simplexRoot)) at hcontinuous
    rw [hroot] at hcontinuous
    exact hcontinuous
  have henvelope : Continuous (fun pair : QuittingTerminalSemanticPair ι =>
      fun who =>
        max
          (quittingRootQuitPayoff reward pair.1 root who)
          (quittingRootContinuePayoff reward
            (Function.update pair.1 who (pair.2 who)) root who)) := by
    apply continuous_pi
    intro who
    have hquitMap : Continuous (fun pair : QuittingTerminalSemanticPair ι =>
        (pair.1, simplexRoot)) := continuous_fst.prodMk continuous_const
    have hquit : Continuous (fun pair : QuittingTerminalSemanticPair ι =>
        quittingRootQuitPayoff reward pair.1 root who) := by
      have hcontinuous :=
        (continuous_quittingRootQuitPayoff_simplex reward who).comp hquitMap
      change Continuous (fun pair : QuittingTerminalSemanticPair ι =>
        quittingRootQuitPayoff reward pair.1
          (quittingRootOfSimplex simplexRoot) who) at hcontinuous
      rw [hroot] at hcontinuous
      exact hcontinuous
    have htail : Continuous (fun pair : QuittingTerminalSemanticPair ι =>
        Function.update pair.1 who (pair.2 who)) := by
      apply continuous_pi
      intro player
      by_cases hplayer : player = who
      · subst player
        have hsnd : Continuous
            (fun pair : QuittingTerminalSemanticPair ι => pair.2) :=
          continuous_snd
        have hcoordinate := (continuous_apply who).comp hsnd
        change Continuous
          (fun pair : QuittingTerminalSemanticPair ι => pair.2 who) at hcoordinate
        simpa [Function.update_self] using hcoordinate
      · have hfst : Continuous
            (fun pair : QuittingTerminalSemanticPair ι => pair.1) :=
          continuous_fst
        have hcoordinate := (continuous_apply player).comp hfst
        change Continuous
          (fun pair : QuittingTerminalSemanticPair ι => pair.1 player) at hcoordinate
        simpa [Function.update_of_ne hplayer] using hcoordinate
    have hcontinueMap : Continuous
        (fun pair : QuittingTerminalSemanticPair ι =>
          (Function.update pair.1 who (pair.2 who), simplexRoot)) :=
      htail.prodMk continuous_const
    have hcontinue : Continuous (fun pair : QuittingTerminalSemanticPair ι =>
        quittingRootContinuePayoff reward
          (Function.update pair.1 who (pair.2 who)) root who) := by
      have hcontinuous :=
        (continuous_quittingRootContinuePayoff_simplex reward who).comp
          hcontinueMap
      change Continuous (fun pair : QuittingTerminalSemanticPair ι =>
        quittingRootContinuePayoff reward
          (Function.update pair.1 who (pair.2 who))
          (quittingRootOfSimplex simplexRoot) who) at hcontinuous
      rw [hroot] at hcontinuous
      exact hcontinuous
    exact hquit.max hcontinue
  unfold quittingTerminalSemanticPrefix
  exact hprescribed.prodMk henvelope

/-- The compact attainable-semantic carrier is invariant under every fixed
root prefix. -/
theorem quittingTerminalSemanticPrefix_mem_carrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (pair : QuittingTerminalSemanticPair ι)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward) :
    quittingTerminalSemanticPrefix reward root pair ∈
      quittingTerminalSemanticCarrier reward := by
  apply map_mem_closure (continuous_quittingTerminalSemanticPrefix reward root)
    hpair
  rintro source ⟨profile, rfl⟩
  refine ⟨quittingRootThenContinuationProfile reward root profile, ?_⟩
  exact quittingTerminalSemanticPair_rootThenContinuation
    reward root profile hM hreward

end GameTheory
