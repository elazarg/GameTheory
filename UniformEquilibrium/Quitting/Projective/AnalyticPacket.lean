/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Projective.AnalyticFirstEvent
import UniformEquilibrium.Quitting.Projective.SingletonLCP
import UniformEquilibrium.Quitting.Bellman.Finite.HazardRowBridge
import Math.PMFProduct.CoalitionMass

/-!
# Analytic construction of the projective singleton packet

This module completes the game-facing part of matching-order analytic
first-event extraction.  The mass limits live in
`QuittingProjectiveAnalyticFirstEvent`.  Here the exact Bellman recursion
identifies the endpoint value with the limiting singleton-reward mixture, and
the exact endpoint-Nash inequalities on the genuine discount domain
`0 < t < min g.radius 1` pass to the limit.

The output is a `QuittingProjectiveSingletonPacket`.  It is still an analytic
packet extracted from a supplied matching germ; it is not an arbitrary-game
producer, chart-coverage theorem, or chronological realization.
-/

noncomputable section

namespace GameTheory

open Filter Set Topology
open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Extend a nonempty-coalition reward by zero at the empty coalition. -/
def quittingProjectiveCoalitionReward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (S : Finset ι) (who : ι) : ℝ :=
  if hS : S.Nonempty then reward ⟨S, hS⟩ who else 0

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem quittingProjectiveCoalitionReward_empty
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    quittingProjectiveCoalitionReward reward ∅ who = 0 := by
  simp [quittingProjectiveCoalitionReward]

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem quittingProjectiveCoalitionReward_singleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner who : ι) :
    quittingProjectiveCoalitionReward reward {owner} who =
      reward (quittingProjectiveSingletonTerminal owner) who := by
  simp [quittingProjectiveCoalitionReward,
    quittingProjectiveSingletonTerminal]

/-- First-event weight of one specified real quitting coalition. -/
def quittingGermCoalitionFirstEventWeight
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm)
    (S : Finset ι) (t : ℝ) : ℝ :=
  (1 - t ^ g.ramification) *
      coalitionMass (fun owner => quittingGermQuitRate g owner t) S /
    quittingGermFirstEventDenominator g t

/-- Normalized reward contribution of all coalitions with at least two
quitters. -/
def quittingGermNonsingletonRewardFirstEventWeight
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm)
    (who : ι) (t : ℝ) : ℝ :=
  ∑ S ∈ (Finset.univ.filter fun S : Finset ι => 2 ≤ S.card),
    quittingGermCoalitionFirstEventWeight g S t *
      quittingProjectiveCoalitionReward reward S who

/-- Singleton coalition weights agree with the named first-event weights. -/
theorem quittingGermCoalitionFirstEventWeight_singleton
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm)
    (owner : ι) (t : ℝ) :
    quittingGermCoalitionFirstEventWeight g {owner} t =
      quittingGermSingletonFirstEventWeight g owner t := by
  simp only [quittingGermCoalitionFirstEventWeight,
    quittingGermSingletonFirstEventWeight,
    quittingGermSingletonProbability, coalitionMass]
  have hcompl : ({owner} : Finset ι)ᶜ = Finset.univ.erase owner := by
    ext other
    simp [Finset.mem_compl]
  rw [hcompl]
  simp

/-- The absorbing root expectation is the coalition-mass reward sum. -/
theorem quittingRootAbsorbingContribution_eq_sum_coalitionMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) :
    quittingRootAbsorbingContribution reward root who =
      ∑ S : Finset ι,
        coalitionMass (fun owner => (root owner true).toReal) S *
          quittingProjectiveCoalitionReward reward S who := by
  classical
  unfold quittingRootAbsorbingContribution quittingRootExpectedPayoff
  have hroot :
      (fun i => if i ∈ Finset.univ then root i else PMF.pure false) = root := by
    funext i
    simp
  rw [← hroot]
  rw [expect_pmfPi_boolFamily_eq_sum_powerset'
    (t := Finset.univ) (q := root)
    (rest := fun _ => false)
    (k := fun action => quittingRootPayoff reward 0 action who)]
  simp only [Finset.mem_univ, if_true, Finset.powerset_univ]
  apply Finset.sum_congr rfl
  intro S _
  have hquitters :
      quittingQuitters (fun i => decide (i ∈ S)) = S := by
    ext i
    simp [quittingQuitters]
  by_cases hS : S.Nonempty
  · have hreward :
        quittingRootPayoff reward 0 (fun i => decide (i ∈ S)) who =
          quittingProjectiveCoalitionReward reward S who := by
      unfold quittingRootPayoff quittingProjectiveCoalitionReward
      rw [dif_pos (hquitters.symm ▸ hS), dif_pos hS]
      apply congrArg (fun terminal => reward terminal who)
      exact Subtype.ext hquitters
    have haction :
        (fun i => if i ∈ S then true else false) =
          (fun i => decide (i ∈ S)) := by
      funext i
      by_cases hi : i ∈ S <;> simp [hi]
    rw [haction, hreward]
    rfl
  · have hEmpty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    simp [quittingRootPayoff, quittingProjectiveCoalitionReward,
      coalitionMass]

/-- Nonempty coalitions split exactly into singleton coalitions and coalitions
of cardinality at least two. -/
theorem sum_nonemptyFinset_eq_sum_singleton_add_sum_card_ge_two
    (f : Finset ι → ℝ) :
    ∑ S ∈ Finset.univ.erase (∅ : Finset ι), f S =
      (∑ owner, f {owner}) +
        ∑ S ∈ (Finset.univ.filter fun S : Finset ι => 2 ≤ S.card), f S := by
  classical
  let nonempty : Finset (Finset ι) :=
    Finset.univ.erase (∅ : Finset ι)
  let multiple : Finset (Finset ι) :=
    nonempty.filter fun S => 2 ≤ S.card
  let single : Finset (Finset ι) :=
    nonempty.filter fun S => ¬2 ≤ S.card
  have hsplit :
      (∑ S ∈ multiple, f S) + (∑ S ∈ single, f S) =
        ∑ S ∈ nonempty, f S := by
    simpa [multiple, single] using
      (Finset.sum_filter_add_sum_filter_not nonempty
        (fun S : Finset ι => 2 ≤ S.card) f)
  have hmultiple :
      multiple = Finset.univ.filter (fun S : Finset ι => 2 ≤ S.card) := by
    ext S
    simp only [multiple, nonempty, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · exact fun h => h.2
    · intro hcard
      refine ⟨?_, hcard⟩
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      intro hEmpty
      subst S
      simp at hcard
  have hsingle :
      single = Finset.univ.image (fun owner : ι => ({owner} : Finset ι)) := by
    ext S
    simp only [single, nonempty, Finset.mem_filter, Finset.mem_erase,
      Finset.mem_univ, and_true, Finset.mem_image]
    constructor
    · rintro ⟨hne, hsmall⟩
      have hpos : 0 < S.card := Finset.card_pos.mpr
        (Finset.nonempty_iff_ne_empty.mpr hne)
      have hcard : S.card = 1 := by omega
      obtain ⟨owner, howner⟩ := Finset.card_eq_one.mp hcard
      exact ⟨owner, by simpa using howner.symm⟩
    · rintro ⟨owner, ⟨_, howner⟩⟩
      subst S
      simp
  have hsingleSum :
      ∑ S ∈ single, f S = ∑ owner, f {owner} := by
    rw [hsingle, Finset.sum_image]
    intro first _ second _ heq
    simpa using heq
  rw [← hsplit, hmultiple, hsingleSum]
  ring

/-- The normalized nonsingleton mass is the sum of the normalized weights of
all coalitions with at least two quitters. -/
theorem sum_quittingGermCoalitionFirstEventWeight_card_ge_two
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm) (t : ℝ) :
    ∑ S ∈ (Finset.univ.filter fun S : Finset ι => 2 ≤ S.card),
        quittingGermCoalitionFirstEventWeight g S t =
      quittingGermNonsingletonFirstEventWeight g t := by
  have hpartition :=
    sum_nonemptyFinset_eq_sum_singleton_add_sum_card_ge_two
      (ι := ι) (fun S => quittingGermCoalitionFirstEventWeight g S t)
  have hcoalition := sum_coalitionMass_nonempty
    (fun owner => quittingGermQuitRate g owner t)
  have hnonempty :
      ∑ S ∈ Finset.univ.erase (∅ : Finset ι),
          quittingGermCoalitionFirstEventWeight g S t =
        quittingGermRealAbsorptionFirstEventWeight g t := by
    simp only [quittingGermCoalitionFirstEventWeight,
      quittingGermRealAbsorptionFirstEventWeight]
    rw [← Finset.sum_div, ← Finset.mul_sum, hcoalition]
    unfold quittingGermAbsorption continueMass
    rfl
  rw [hnonempty] at hpartition
  simp_rw [quittingGermCoalitionFirstEventWeight_singleton] at hpartition
  unfold quittingGermNonsingletonFirstEventWeight
  linarith

/-- Exact discounted first-event reward decomposition on the intended
discount domain.  The explicit `t < 1` premise is what makes the physical
first-event weights nonnegative. -/
theorem quittingGermValue_eq_singleton_sum_add_nonsingletonReward
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) g.radius) (ht1 : t < 1) (who : ι) :
    quittingGermValue g t who =
      (∑ owner, quittingGermSingletonFirstEventWeight g owner t *
        reward (quittingProjectiveSingletonTerminal owner) who) +
      quittingGermNonsingletonRewardFirstEventWeight g who t := by
  have hfactorNonneg : 0 ≤ 1 - t ^ g.ramification :=
    (quittingGerm_discountFactor_pos g ht ht1).le
  have habsNonneg : 0 ≤ quittingGermAbsorption g t := by
    rw [quittingGermAbsorption_eq g ht]
    exact sub_nonneg.mpr (quittingStationaryContinueMass_le_one _)
  have hdenomPos : 0 < quittingGermFirstEventDenominator g t := by
    unfold quittingGermFirstEventDenominator
    exact add_pos_of_pos_of_nonneg (pow_pos ht.1 _) (mul_nonneg hfactorNonneg habsNonneg)
  have hdenom :
      1 - (1 - t ^ g.ramification) *
          quittingStationaryContinueMass (quittingGermRoot g ht) =
        quittingGermFirstEventDenominator g t := by
    rw [quittingStationaryContinueMass_quittingGermRoot g ht]
    unfold quittingGermFirstEventDenominator quittingGermAbsorption
    ring
  have hbalance := quittingGermValue_mul_one_sub g ht who
  rw [hdenom,
    quittingRootAbsorbingContribution_eq_sum_coalitionMass] at hbalance
  simp_rw [quittingGermRoot_apply_true_toReal g ht] at hbalance
  have hvalue :
      quittingGermValue g t who =
        ∑ S : Finset ι,
          quittingGermCoalitionFirstEventWeight g S t *
            quittingProjectiveCoalitionReward reward S who := by
    calc
      quittingGermValue g t who =
          ((1 - t ^ g.ramification) *
            ∑ S : Finset ι,
              coalitionMass (fun owner => quittingGermQuitRate g owner t) S *
                quittingProjectiveCoalitionReward reward S who) /
            quittingGermFirstEventDenominator g t :=
        (eq_div_iff hdenomPos.ne').2 hbalance
      _ = ∑ S : Finset ι,
          quittingGermCoalitionFirstEventWeight g S t *
            quittingProjectiveCoalitionReward reward S who := by
        simp only [quittingGermCoalitionFirstEventWeight]
        rw [Finset.mul_sum, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro S _
        ring
  rw [hvalue]
  have hpartition :=
    sum_nonemptyFinset_eq_sum_singleton_add_sum_card_ge_two
      (ι := ι)
      (fun S => quittingGermCoalitionFirstEventWeight g S t *
        quittingProjectiveCoalitionReward reward S who)
  have hempty :
      quittingGermCoalitionFirstEventWeight g ∅ t *
          quittingProjectiveCoalitionReward reward ∅ who = 0 := by simp
  have hall :
      ∑ S : Finset ι,
          quittingGermCoalitionFirstEventWeight g S t *
            quittingProjectiveCoalitionReward reward S who =
        ∑ S ∈ Finset.univ.erase (∅ : Finset ι),
          quittingGermCoalitionFirstEventWeight g S t *
            quittingProjectiveCoalitionReward reward S who := by
    rw [← Finset.add_sum_erase Finset.univ
      (fun S => quittingGermCoalitionFirstEventWeight g S t *
        quittingProjectiveCoalitionReward reward S who)
      (Finset.mem_univ ∅), hempty, zero_add]
  rw [hall, hpartition]
  simp_rw [quittingGermCoalitionFirstEventWeight_singleton,
    quittingProjectiveCoalitionReward_singleton]
  rfl

/-- Coalition mass is continuous under pointwise convergence of its finitely
many hazard coordinates. -/
theorem coalitionMass_tendsto
    {α : Type*} {l : Filter α} (x : ι → α → ℝ) (limit : ι → ℝ)
    (S : Finset ι)
    (h : ∀ owner, Tendsto (x owner) l (𝓝 (limit owner))) :
    Tendsto (fun a => coalitionMass (fun owner => x owner a) S) l
      (𝓝 (coalitionMass limit S)) := by
  unfold coalitionMass
  apply Tendsto.mul
  · exact tendsto_finsetProd S fun owner _ => h owner
  · exact tendsto_finsetProd Sᶜ fun owner _ =>
      tendsto_const_nhds.sub (h owner)

/-- The coalition expansion of the pure-Quit endpoint, written directly in
the germ's real quit-rate coordinates. -/
def quittingGermPureQuitCoalitionValue
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm)
    (owner who : ι) (t : ℝ) : ℝ :=
  ∑ S : Finset ι,
    coalitionMass
        (Function.update
          (fun other => quittingGermQuitRate g other t) owner 1) S *
      quittingProjectiveCoalitionReward reward S who

/-- On the punctured germ domain, the real-coordinate pure-Quit expansion is
exactly the game-facing pure-Quit endpoint. -/
theorem quittingGermRootQuitPayoff_eq_pureQuitCoalitionValue
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) g.radius) (owner : ι) :
    quittingRootQuitPayoff reward (quittingGermValue g t)
        (quittingGermRoot g ht) owner =
      quittingGermPureQuitCoalitionValue g owner owner t := by
  classical
  unfold quittingRootQuitPayoff
  rw [quittingRootExpectedPayoff_eq_absorbingContribution_add,
    quittingStationaryContinueMass_update_pure_true_eq_zero]
  simp only [zero_mul, add_zero]
  rw [quittingRootAbsorbingContribution_eq_sum_coalitionMass]
  unfold quittingGermPureQuitCoalitionValue
  apply Finset.sum_congr rfl
  intro S _
  congr 1
  apply congrArg (fun rates : ι → ℝ => coalitionMass rates S)
  funext other
  by_cases hother : other = owner
  · subst other
    simp
  · simp [Function.update, hother,
      quittingGermRoot_apply_true_toReal g ht]

/-- The germ value is continuous at the analytic endpoint. -/
theorem quittingGermValue_tendsto_zero
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm) (who : ι) :
    Tendsto (fun t => quittingGermValue g t who)
      (𝓝[>] (0 : ℝ)) (𝓝 (quittingGermValue g 0 who)) := by
  have h := (g.analytic_coordinate
    (StochasticGame.BellmanVar.val none who)).continuousAt.tendsto
  exact h.mono_left nhdsWithin_le_nhds

/-- The pure-Quit endpoint converges to the singleton terminal reward. -/
theorem quittingGermPureQuitCoalitionValue_tendsto_singleton
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {g : (quittingGame reward).AnalyticBellmanGerm}
    (data : QuittingGermMatchingLeadingData reward g)
    (owner who : ι) :
    Tendsto (quittingGermPureQuitCoalitionValue g owner who)
      (𝓝[>] (0 : ℝ))
      (𝓝 (reward (quittingProjectiveSingletonTerminal owner) who)) := by
  let pureRates : ι → ℝ := Function.update (fun _ => 0) owner 1
  have hrates : ∀ other,
      Tendsto
        (fun t => Function.update
          (fun player => quittingGermQuitRate g player t) owner 1 other)
        (𝓝[>] (0 : ℝ)) (𝓝 (pureRates other)) := by
    intro other
    by_cases hother : other = owner
    · subst other
      simp [pureRates]
    · simpa [pureRates, Function.update, hother] using
        data.quitRate_tendsto_zero other
  have hsum :
      Tendsto
        (fun t => ∑ S : Finset ι,
          coalitionMass
              (Function.update
                (fun other => quittingGermQuitRate g other t) owner 1) S *
            quittingProjectiveCoalitionReward reward S who)
        (𝓝[>] (0 : ℝ))
        (𝓝 (∑ S : Finset ι,
          coalitionMass pureRates S *
            quittingProjectiveCoalitionReward reward S who)) := by
    apply tendsto_finsetSum Finset.univ
    intro S _
    exact (coalitionMass_tendsto
      (fun other t => Function.update
        (fun player => quittingGermQuitRate g player t) owner 1 other)
      pureRates S hrates).mul tendsto_const_nhds
  have hlimit :
      (∑ S : Finset ι,
          coalitionMass pureRates S *
            quittingProjectiveCoalitionReward reward S who) =
        reward (quittingProjectiveSingletonTerminal owner) who := by
    let pureRoot : ι → PMF Bool := fun other =>
      PMF.pure (if other = owner then true else false)
    have hpureRates :
        (fun other => (pureRoot other true).toReal) = pureRates := by
      funext other
      by_cases hother : other = owner
      · subst other
        simp [pureRoot, pureRates]
      · simp [pureRoot, pureRates, hother]
    have hexpansion :=
      quittingRootAbsorbingContribution_eq_sum_coalitionMass reward pureRoot who
    rw [hpureRates] at hexpansion
    rw [← hexpansion]
    unfold quittingRootAbsorbingContribution quittingRootExpectedPayoff
    rw [pmfPi_pure, expect_pure]
    have hquitters :
        quittingQuitters (fun other => if other = owner then true else false) =
          {owner} := by
      ext other
      by_cases hother : other = owner <;>
        simp [quittingQuitters, hother]
    unfold quittingRootPayoff
    rw [dif_pos (by simp)]
    apply congrArg (fun terminal => reward terminal who)
    exact Subtype.ext hquitters
  unfold quittingGermPureQuitCoalitionValue
  rw [hlimit] at hsum
  exact hsum

/-- Coalition first-event weights are nonnegative on the genuine discounted
germ domain. -/
theorem quittingGermCoalitionFirstEventWeight_nonneg
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) g.radius) (ht1 : t < 1) (S : Finset ι) :
    0 ≤ quittingGermCoalitionFirstEventWeight g S t := by
  have hfactor : 0 ≤ 1 - t ^ g.ramification :=
    (quittingGerm_discountFactor_pos g ht ht1).le
  have hmass : 0 ≤ coalitionMass
      (fun owner => quittingGermQuitRate g owner t) S := by
    unfold coalitionMass
    apply mul_nonneg <;> apply Finset.prod_nonneg
    · intro owner _
      exact quittingGermQuitRate_nonneg g ht owner
    · intro owner _
      exact sub_nonneg.mpr (quittingGermQuitRate_le_one g ht owner)
  have habs : 0 ≤ quittingGermAbsorption g t := by
    rw [quittingGermAbsorption_eq g ht]
    exact sub_nonneg.mpr (quittingStationaryContinueMass_le_one _)
  have hdenom : 0 ≤ quittingGermFirstEventDenominator g t := by
    unfold quittingGermFirstEventDenominator
    exact add_nonneg (pow_nonneg ht.1.le _) (mul_nonneg hfactor habs)
  exact div_nonneg (mul_nonneg hfactor hmass) hdenom

/-- The nonsingleton reward remainder is controlled by the nonsingleton
first-event mass. -/
theorem abs_quittingGermNonsingletonRewardFirstEventWeight_le
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (g : (quittingGame reward).AnalyticBellmanGerm) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) g.radius) (ht1 : t < 1) (who : ι) :
    |quittingGermNonsingletonRewardFirstEventWeight g who t| ≤
      quittingRewardBound reward *
        quittingGermNonsingletonFirstEventWeight g t := by
  let multiple := Finset.univ.filter fun S : Finset ι => 2 ≤ S.card
  have hreward : ∀ S : Finset ι,
      |quittingProjectiveCoalitionReward reward S who| ≤
        quittingRewardBound reward := by
    intro S
    by_cases hS : S.Nonempty
    · simpa [quittingProjectiveCoalitionReward, hS] using
        abs_reward_le_quittingRewardBound reward ⟨S, hS⟩ who
    · simp [quittingProjectiveCoalitionReward, hS,
        quittingRewardBound_nonneg]
  calc
    |quittingGermNonsingletonRewardFirstEventWeight g who t| ≤
        ∑ S ∈ multiple,
          |quittingGermCoalitionFirstEventWeight g S t *
            quittingProjectiveCoalitionReward reward S who| := by
      unfold quittingGermNonsingletonRewardFirstEventWeight multiple
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ S ∈ multiple,
        quittingRewardBound reward *
          quittingGermCoalitionFirstEventWeight g S t := by
      apply Finset.sum_le_sum
      intro S hS
      rw [abs_mul, abs_of_nonneg
        (quittingGermCoalitionFirstEventWeight_nonneg g ht ht1 S), mul_comm]
      exact mul_le_mul_of_nonneg_right (hreward S)
        (quittingGermCoalitionFirstEventWeight_nonneg g ht ht1 S)
    _ = quittingRewardBound reward *
        quittingGermNonsingletonFirstEventWeight g t := by
      rw [← Finset.mul_sum,
        sum_quittingGermCoalitionFirstEventWeight_card_ge_two]

/-- The normalized nonsingleton reward contribution vanishes. -/
theorem quittingGermNonsingletonRewardFirstEventWeight_tendsto_zero
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {g : (quittingGame reward).AnalyticBellmanGerm}
    (data : QuittingGermMatchingLeadingData reward g) (who : ι) :
    Tendsto (quittingGermNonsingletonRewardFirstEventWeight g who)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hscaled : Tendsto
      (fun t => quittingRewardBound reward *
        quittingGermNonsingletonFirstEventWeight g t)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using data.nonsingletonFirstEventWeight_tendsto_zero.const_mul
      (quittingRewardBound reward)
  have hltOne : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 :=
    (show ∀ᶠ t in 𝓝 (0 : ℝ), t < 1 from
      Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
        nhdsWithin_le_nhds
  have habs : Tendsto
      (fun t => |quittingGermNonsingletonRewardFirstEventWeight g who t|)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall fun t => abs_nonneg _
    · filter_upwards [eventually_mem_Ioo_radius g, hltOne] with t ht ht1
      exact abs_quittingGermNonsingletonRewardFirstEventWeight_le
        g ht ht1 who
    · exact hscaled
  apply tendsto_iff_norm_sub_tendsto_zero.2
  simpa [Real.norm_eq_abs] using habs

/-- The analytic endpoint value is the singleton-reward mixture selected by
the matching leading coefficients. -/
theorem QuittingGermMatchingLeadingData.value_eq_singleton_mix
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {g : (quittingGame reward).AnalyticBellmanGerm}
    (data : QuittingGermMatchingLeadingData reward g) (who : ι) :
    quittingGermValue g 0 who =
      ∑ owner,
        (data.leading owner / (1 + ∑ other, data.leading other)) *
          reward (quittingProjectiveSingletonTerminal owner) who := by
  have hsingle : Tendsto
      (fun t => ∑ owner,
        quittingGermSingletonFirstEventWeight g owner t *
          reward (quittingProjectiveSingletonTerminal owner) who)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∑ owner,
        (data.leading owner / (1 + ∑ other, data.leading other)) *
          reward (quittingProjectiveSingletonTerminal owner) who)) := by
    apply tendsto_finsetSum Finset.univ
    intro owner _
    exact (data.singletonFirstEventWeight_tendsto owner).mul
      tendsto_const_nhds
  have hright := hsingle.add
    (quittingGermNonsingletonRewardFirstEventWeight_tendsto_zero data who)
  have hltOne : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 :=
    (show ∀ᶠ t in 𝓝 (0 : ℝ), t < 1 from
      Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
        nhdsWithin_le_nhds
  have hexact :
      (fun t => quittingGermValue g t who) =ᶠ[𝓝[>] (0 : ℝ)]
        fun t =>
          (∑ owner, quittingGermSingletonFirstEventWeight g owner t *
            reward (quittingProjectiveSingletonTerminal owner) who) +
          quittingGermNonsingletonRewardFirstEventWeight g who t := by
    filter_upwards [eventually_mem_Ioo_radius g, hltOne] with t ht ht1
    exact quittingGermValue_eq_singleton_sum_add_nonsingletonReward
      g ht ht1 who
  have hfromRight : Tendsto (fun t => quittingGermValue g t who)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((∑ owner,
        (data.leading owner / (1 + ∑ other, data.leading other)) *
          reward (quittingProjectiveSingletonTerminal owner) who) + 0)) :=
    hright.congr' hexact.symm
  have hfromValue := quittingGermValue_tendsto_zero g who
  simpa using tendsto_nhds_unique hfromValue hfromRight

/-- Under exact endpoint Nash, a positive own-Quit mass pins the prescribed
root successor to the pure-Quit endpoint. -/
theorem quittingRootQuitPayoff_eq_successor_of_endpointNash_of_quit_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (hnash : IsεQuittingRootEndpointNash reward tail 0 root)
    (hquit : 0 < (root who true).toReal) :
    quittingRootQuitPayoff reward tail root who =
      quittingRootSuccessorPayoff reward tail root who := by
  have hgapNonneg : 0 ≤ quittingRootEndpointDifference reward tail root who :=
    nonneg_of_mul_nonneg_right (by simpa using (hnash who).2) hquit
  have hcontinueNonneg : 0 ≤ (root who false).toReal := ENNReal.toReal_nonneg
  have hproductNonneg : 0 ≤ (root who false).toReal *
      quittingRootEndpointDifference reward tail root who :=
    mul_nonneg hcontinueNonneg hgapNonneg
  have hproduct : (root who false).toReal *
      quittingRootEndpointDifference reward tail root who = 0 :=
    le_antisymm (by simpa using (hnash who).1) hproductNonneg
  have hsum := quittingRoot_continueProbability_add_quitProbability root who
  rw [quittingRootSuccessorPayoff_eq_endpointMix]
  unfold quittingRootEndpointDifference at hproduct
  calc
    quittingRootQuitPayoff reward tail root who =
        ((root who false).toReal + (root who true).toReal) *
          quittingRootQuitPayoff reward tail root who := by rw [hsum, one_mul]
    _ = (root who true).toReal *
          quittingRootQuitPayoff reward tail root who +
        (root who false).toReal *
          quittingRootQuitPayoff reward tail root who := by ring
    _ = (root who true).toReal *
          quittingRootQuitPayoff reward tail root who +
        (root who false).toReal *
          quittingRootContinuePayoff reward tail root who := by
      congr 1
      linarith [hproduct]

/-- Every singleton reward lies below the analytic endpoint value. -/
theorem QuittingGermMatchingLeadingData.solo_le_value
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {g : (quittingGame reward).AnalyticBellmanGerm}
    (data : QuittingGermMatchingLeadingData reward g) (who : ι) :
    reward (quittingProjectiveSingletonTerminal who) who ≤
      quittingGermValue g 0 who := by
  have hdiscount : Tendsto (fun t : ℝ => 1 - t ^ g.ramification)
      (𝓝[>] (0 : ℝ)) (𝓝 1) :=
    by
      have hone : Tendsto (fun _ : ℝ => (1 : ℝ))
          (𝓝[>] (0 : ℝ)) (𝓝 1) := tendsto_const_nhds
      simpa using hone.sub data.discountComplement_tendsto_zero
  have hquit :=
    quittingGermPureQuitCoalitionValue_tendsto_singleton data who who
  have hleft := hdiscount.mul hquit
  have hleft' : Tendsto
      (fun t : ℝ => (1 - t ^ g.ramification) *
        quittingGermPureQuitCoalitionValue g who who t)
      (𝓝[>] (0 : ℝ))
      (𝓝 (reward (quittingProjectiveSingletonTerminal who) who)) := by
    simpa using hleft
  have hright := quittingGermValue_tendsto_zero g who
  have hltOne : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 :=
    (show ∀ᶠ t in 𝓝 (0 : ℝ), t < 1 from
      Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
        nhdsWithin_le_nhds
  have hineq : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      (1 - t ^ g.ramification) *
          quittingGermPureQuitCoalitionValue g who who t ≤
        quittingGermValue g t who := by
    filter_upwards [eventually_mem_Ioo_radius g, hltOne] with t ht ht1
    rw [← quittingGermRootQuitPayoff_eq_pureQuitCoalitionValue g ht who]
    exact quittingGerm_bestResponse_quit g ht who
  exact le_of_tendsto_of_tendsto hleft' hright hineq

/-- A positive normalized singleton mass pins its owner's endpoint value to
the singleton reward. -/
theorem QuittingGermMatchingLeadingData.positive_singleton_pins
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {g : (quittingGame reward).AnalyticBellmanGerm}
    (data : QuittingGermMatchingLeadingData reward g) (who : ι)
    (hpositive : 0 < data.leading who /
      (1 + ∑ other, data.leading other)) :
    quittingGermValue g 0 who =
      reward (quittingProjectiveSingletonTerminal who) who := by
  have hdenom : 0 < 1 + ∑ other, data.leading other := by
    linarith [data.leading_sum_pos]
  have hleading : 0 < data.leading who := by
    rcases div_pos_iff.mp hpositive with hpos | hneg
    · exact hpos.1
    · exact absurd hneg.2 (not_lt_of_ge hdenom.le)
  have hratio : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      0 < quittingGermQuitRate g who t / t ^ g.ramification :=
    (data.quitRate_div_discount_tendsto who).eventually
      (Ioi_mem_nhds hleading)
  have hquitPos : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      0 < quittingGermQuitRate g who t := by
    filter_upwards [hratio, self_mem_nhdsWithin] with t hratio ht
    change 0 < t at ht
    rcases div_pos_iff.mp hratio with hpos | hneg
    · exact hpos.1
    · exact absurd hneg.2 (not_lt_of_ge (pow_nonneg ht.le _))
  have hltOne : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 :=
    (show ∀ᶠ t in 𝓝 (0 : ℝ), t < 1 from
      Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
        nhdsWithin_le_nhds
  have hexact : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      quittingGermValue g t who =
        (1 - t ^ g.ramification) *
          quittingGermPureQuitCoalitionValue g who who t := by
    filter_upwards [eventually_mem_Ioo_radius g, hltOne, hquitPos]
      with t ht ht1 hquit
    have hnash := isεQuittingRootEndpointNash_quittingGermRoot g ht ht1
    have hrootQuit : 0 < ((quittingGermRoot g ht who) true).toReal := by
      simpa [quittingGermRoot_apply_true_toReal g ht] using hquit
    have hpinned :=
      quittingRootQuitPayoff_eq_successor_of_endpointNash_of_quit_pos
        reward (quittingGermValue g t) (quittingGermRoot g ht) who
        hnash hrootQuit
    have hrec := quittingGermValue_eq_smul_rootSuccessorPayoff g ht who
    rw [← hpinned,
      quittingGermRootQuitPayoff_eq_pureQuitCoalitionValue g ht who] at hrec
    exact hrec
  have hleft := quittingGermValue_tendsto_zero g who
  have hdiscount : Tendsto (fun t : ℝ => 1 - t ^ g.ramification)
      (𝓝[>] (0 : ℝ)) (𝓝 1) :=
    by
      have hone : Tendsto (fun _ : ℝ => (1 : ℝ))
          (𝓝[>] (0 : ℝ)) (𝓝 1) := tendsto_const_nhds
      simpa using hone.sub data.discountComplement_tendsto_zero
  have hright := hdiscount.mul
    (quittingGermPureQuitCoalitionValue_tendsto_singleton data who who)
  have hexactEq :
      (fun t : ℝ => quittingGermValue g t who) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun t => (1 - t ^ g.ramification) *
          quittingGermPureQuitCoalitionValue g who who t) := hexact
  have hleftFromRight : Tendsto
      (fun t : ℝ => quittingGermValue g t who)
      (𝓝[>] (0 : ℝ))
      (𝓝 (reward (quittingProjectiveSingletonTerminal who) who)) := by
    simpa using hright.congr' hexactEq.symm
  exact tendsto_nhds_unique hleft hleftFromRight

/-- Matching analytic leading data construct the complete normalized
singleton projective packet. -/
def QuittingGermMatchingLeadingData.toProjectiveSingletonPacket
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {g : (quittingGame reward).AnalyticBellmanGerm}
    (data : QuittingGermMatchingLeadingData reward g) :
    QuittingProjectiveSingletonPacket reward where
  cemetery := 1 / (1 + ∑ owner, data.leading owner)
  singleton := fun owner =>
    data.leading owner / (1 + ∑ other, data.leading other)
  value := quittingGermValue g 0
  cemetery_nonneg := by
    exact one_div_nonneg.mpr (by linarith [data.leading_sum_pos])
  singleton_nonneg := fun owner =>
    div_nonneg (data.leading_nonneg owner)
      (by linarith [data.leading_sum_pos])
  total := by
    rw [← Finset.sum_div]
    field_simp [ne_of_gt (show 0 < 1 + ∑ owner, data.leading owner by
      linarith [data.leading_sum_pos])]
  value_eq_singleton_mix := data.value_eq_singleton_mix
  solo_le_value := data.solo_le_value
  positive_singleton_pins := data.positive_singleton_pins

end GameTheory
