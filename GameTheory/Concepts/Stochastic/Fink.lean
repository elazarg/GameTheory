/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.Discounted
import GameTheory.Concepts.Stochastic.StageGame
import GameTheory.Concepts.Stochastic.Uniform
import Math.ProbabilityMassFunction.Simplex

/-!
# Fink's Discounted Stationary-Equilibrium Interface

This file sets up the general-player discounted auxiliary games used in
Fink's fixed-point proof.  Given a continuation payoff `V`, every state has a
finite normal-form game with payoff

`(1 - β) gᵢ(s,a) + β 𝔼[Vᵢ(s')]`.

The statewise mixed Nash conditions are the best-response half of Fink's
fixed-point correspondence; the value-consistency equations are its other
half.  Together they form `IsDiscountedStationaryBellmanEq`.

The verification lemmas below translate that finite-dimensional certificate
into historywise Bellman inequalities against arbitrary behavior-strategy
deviations.  They therefore feed directly into the quantitative
discount-to-horizon results in `GameTheory.Concepts.Stochastic.Discounted`.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Filter
open Math.Probability Math.PMFProduct
open Math.ProbabilityMassFunction

variable {ι : Type}

/-- A state-dependent mixed action profile. -/
abbrev StationaryMixedProfile (G : StochasticGame ι) : Type :=
  (s : G.State) → ∀ i, PMF (G.Act i)

/-- A state-player agent indexing one mixed-action simplex in Fink's
finite-dimensional fixed-point domain. -/
abbrev FinkAgent (G : StochasticGame ι) : Type := G.State × ι

/-- The action carrier of a state-player agent. -/
abbrev FinkAction (G : StochasticGame ι) (p : G.FinkAgent) : Type :=
  G.Act p.2

/-- Ambient finite-dimensional space for Fink's fixed point: stationary
mixed-action weights together with state-contingent continuation payoffs. -/
abbrev FinkAmbient (G : StochasticGame ι) : Type :=
  (∀ p : G.FinkAgent, G.FinkAction p → ℝ) × (G.State → Payoff ι)

/-- Compact convex domain for Fink's fixed point.  The first factor is the
product of state-player action simplices; the second is a payoff cube. -/
def finkDomain (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [∀ i, Fintype (G.Act i)] (U : ℝ) : Set G.FinkAmbient :=
  mixedSimplexAsSet G.FinkAgent G.FinkAction ×ˢ
    Set.Icc (fun _ _ => -U) (fun _ _ => U)

theorem convex_finkDomain (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)] (U : ℝ) :
    Convex ℝ (G.finkDomain U) := by
  unfold finkDomain
  exact (convex_mixedSimplexAsSet
    (ι := G.FinkAgent) (A := G.FinkAction)).prod
      (convex_Icc (fun _ : G.State => fun _ : ι => -U)
        (fun _ : G.State => fun _ : ι => U))

theorem isCompact_finkDomain (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)] (U : ℝ) :
    IsCompact (G.finkDomain U) :=
  isCompact_mixedSimplexAsSet.prod isCompact_Icc

theorem nonempty_finkDomain (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    [∀ i, Nonempty (G.Act i)] {U : ℝ} (hU : 0 ≤ U) :
    (G.finkDomain U).Nonempty := by
  obtain ⟨x, hx⟩ := nonempty_mixedSimplexAsSet
    (ι := G.FinkAgent) (A := G.FinkAction)
  refine ⟨(x, 0), hx, ?_⟩
  constructor <;> intro s i <;> simp [hU]

/-- The simplex coordinate of a point in Fink's compact domain. -/
def finkSimplex (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    {U : ℝ} (z : G.finkDomain U) (p : G.FinkAgent) :
    stdSimplex ℝ (G.FinkAction p) :=
  ⟨z.1.1 p, z.2.1 p (Set.mem_univ p)⟩

/-- The mixed-action simplex at one state, extracted from a Fink-domain
point. -/
def finkStateSimplex (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    {U : ℝ} (z : G.finkDomain U) (s : G.State) : MixedSimplex ι G.Act :=
  fun i => G.finkSimplex z (s, i)

/-- Decode the stationary mixed profile represented by a Fink-domain point. -/
def finkProfile (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    {U : ℝ} (z : G.finkDomain U) : G.StationaryMixedProfile :=
  fun s i => (stdSimplexEquiv (α := G.Act i)).symm
    (G.finkSimplex z (s, i))

@[simp] theorem finkProfile_apply_toReal (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    {U : ℝ} (z : G.finkDomain U) (s : G.State) (who : ι)
    (d : G.Act who) :
    ((G.finkProfile z s who) d).toReal = z.1.1 (s, who) d := by
  simp [finkProfile, finkSimplex, stdSimplexEquiv_symm_apply]
  rfl

/-- Decode the continuation payoff represented by a Fink-domain point. -/
def finkValue (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    {U : ℝ} (z : G.finkDomain U) : G.State → Payoff ι :=
  z.1.2

theorem abs_finkValue_le (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    {U : ℝ} (z : G.finkDomain U) (s : G.State) (who : ι) :
    |G.finkValue z s who| ≤ U := by
  exact abs_le.mpr ⟨z.2.2.1 s who, z.2.2.2 s who⟩

/-- The normalized discounted auxiliary payoff for continuation vector `V`. -/
def discountedAuxPayoff (G : StochasticGame ι) (β : ℝ)
    (V : G.State → Payoff ι) (s : G.State) (a : G.JointAct)
    (who : ι) : ℝ :=
  (1 - β) * G.stagePayoff s a who +
    β * expect (G.transition s a) (fun s' => V s' who)

/-- Expected discounted auxiliary payoff under independent mixed actions. -/
def discountedAuxEU (G : StochasticGame ι) [Fintype ι] (β : ℝ)
    (V : G.State → Payoff ι) (s : G.State) (m : ∀ i, PMF (G.Act i))
    (who : ι) : ℝ :=
  expect (pmfPi m) (fun a => G.discountedAuxPayoff β V s a who)

/-- The baseline auxiliary payoff written in the real coordinates of Fink's
domain.  This finite-sum presentation is the one used for continuity. -/
def finkAuxEU (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (β : ℝ) {U : ℝ} (z : G.finkDomain U) (s : G.State) (who : ι) : ℝ :=
  ∑ a : G.JointAct,
    (∏ i, z.1.1 (s, i) (a i)) *
      G.discountedAuxPayoff β (G.finkValue z) s a who

/-- The auxiliary payoff after replacing one player's mixed action by a pure
action, again written as a finite polynomial in Fink's coordinates. -/
def finkDeviationAuxEU (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (β : ℝ) {U : ℝ}
    (z : G.finkDomain U) (s : G.State) (who : ι) (d : G.Act who) : ℝ :=
  ∑ a : G.JointAct,
    ((((PMF.pure d) (a who)).toReal) *
      (∏ i ∈ (Finset.univ.erase who), z.1.1 (s, i) (a i))) *
        G.discountedAuxPayoff β (G.finkValue z) s a who

/-- The finite-coordinate baseline payoff agrees with probabilistic
expectation under the decoded stationary profile. -/
theorem finkAuxEU_eq_discountedAuxEU (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (β : ℝ) {U : ℝ} (z : G.finkDomain U) (s : G.State) (who : ι) :
    G.finkAuxEU β z s who =
      G.discountedAuxEU β (G.finkValue z) s (G.finkProfile z s) who := by
  classical
  rw [discountedAuxEU, expect_eq_sum]
  refine Finset.sum_congr rfl ?_
  intro a ha
  congr 1
  simp [pmfPi_apply, finkProfile, finkSimplex,
    stdSimplexEquiv_symm_apply]
  rfl

/-- The finite-coordinate pure-deviation payoff agrees with probabilistic
expectation after updating the decoded mixed profile. -/
theorem finkDeviationAuxEU_eq_discountedAuxEU (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (β : ℝ) {U : ℝ}
    (z : G.finkDomain U) (s : G.State) (who : ι) (d : G.Act who) :
    G.finkDeviationAuxEU β z s who d =
      G.discountedAuxEU β (G.finkValue z) s
        (Function.update (G.finkProfile z s) who (PMF.pure d)) who := by
  classical
  rw [discountedAuxEU, expect_eq_sum]
  refine Finset.sum_congr rfl ?_
  intro a ha
  congr 1
  rw [pmfPi_apply_update_family]
  by_cases hsa : a who = d
  · subst hsa
    simp [PMF.pure_apply, finkProfile, finkSimplex,
      stdSimplexEquiv_symm_apply]
    rfl
  · simp [PMF.pure_apply, hsa]

/-- Gain from a pure action in the auxiliary game, expressed in Fink's real
coordinates. -/
def finkGain (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (β : ℝ) {U : ℝ}
    (z : G.finkDomain U) (s : G.State) (who : ι) (d : G.Act who) : ℝ :=
  G.finkDeviationAuxEU β z s who d - G.finkAuxEU β z s who

/-- Sum of positive auxiliary gains for one state-player pair. -/
def finkGainSum (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (β : ℝ) {U : ℝ}
    (z : G.finkDomain U) (s : G.State) (who : ι) : ℝ :=
  ∑ d, KernelGame.pospart (G.finkGain β z s who d)

theorem finkGainSum_nonneg (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (β : ℝ) {U : ℝ}
    (z : G.finkDomain U) (s : G.State) (who : ι) :
    0 ≤ G.finkGainSum β z s who := by
  exact Finset.sum_nonneg fun d _ => KernelGame.pospart_nonneg _

/-- One coordinate of Nash's gain-adjustment map for Fink's auxiliary game. -/
def finkStrategyWeightUpdate (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (β : ℝ) {U : ℝ}
    (z : G.finkDomain U) (s : G.State) (who : ι) (d : G.Act who) : ℝ :=
  (z.1.1 (s, who) d + KernelGame.pospart (G.finkGain β z s who d)) /
    (1 + G.finkGainSum β z s who)

/-- Nash's gain-adjustment map, state by state, as a point of the appropriate
action simplex. -/
def finkStrategyUpdate (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (β : ℝ) {U : ℝ}
    (z : G.finkDomain U) (s : G.State) (who : ι) :
    stdSimplex ℝ (G.Act who) := by
  refine ⟨G.finkStrategyWeightUpdate β z s who, ?_, ?_⟩
  · intro d
    apply div_nonneg
    · exact add_nonneg ((G.finkSimplex z (s, who)).property.1 d)
        (KernelGame.pospart_nonneg _)
    · linarith [G.finkGainSum_nonneg β z s who]
  · have hS := G.finkGainSum_nonneg β z s who
    have hden_pos : 0 < 1 + G.finkGainSum β z s who := by linarith
    have hden_ne : 1 + G.finkGainSum β z s who ≠ 0 := ne_of_gt hden_pos
    simp only [finkStrategyWeightUpdate]
    rw [← Finset.sum_div]
    rw [show ∑ d : G.Act who,
        (z.1.1 (s, who) d + KernelGame.pospart (G.finkGain β z s who d)) =
          (∑ d, z.1.1 (s, who) d) +
            ∑ d, KernelGame.pospart (G.finkGain β z s who d) from
      Finset.sum_add_distrib]
    rw [show ∑ d, z.1.1 (s, who) d = 1 by
      simpa [finkSimplex] using (G.finkSimplex z (s, who)).property.2]
    simp only [finkGainSum]
    exact div_self hden_ne

/-- Auxiliary pure payoff is continuous in the continuation-value coordinates
of Fink's domain. -/
theorem continuous_finkDiscountedAuxPayoff (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι]
    [∀ i, Fintype (G.Act i)] (β : ℝ) {U : ℝ}
    (s : G.State) (a : G.JointAct) (who : ι) :
    Continuous (fun z : G.finkDomain U =>
      G.discountedAuxPayoff β (G.finkValue z) s a who) := by
  unfold discountedAuxPayoff finkValue
  simp_rw [expect_eq_sum]
  fun_prop

/-- Baseline auxiliary expected payoff is continuous on Fink's domain. -/
theorem continuous_finkAuxEU (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (β : ℝ) {U : ℝ}
    (s : G.State) (who : ι) :
    Continuous (fun z : G.finkDomain U => G.finkAuxEU β z s who) := by
  unfold finkAuxEU
  refine continuous_finsetSum (s := (Finset.univ : Finset G.JointAct)) ?_
  intro a ha
  have hw : Continuous (fun z : G.finkDomain U =>
      ∏ i, z.1.1 (s, i) (a i)) := by
    fun_prop
  exact hw.mul (G.continuous_finkDiscountedAuxPayoff β s a who)

/-- Every pure-deviation auxiliary payoff is continuous on Fink's domain. -/
theorem continuous_finkDeviationAuxEU (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (β : ℝ) {U : ℝ}
    (s : G.State) (who : ι) (d : G.Act who) :
    Continuous (fun z : G.finkDomain U =>
      G.finkDeviationAuxEU β z s who d) := by
  unfold finkDeviationAuxEU
  refine continuous_finsetSum (s := (Finset.univ : Finset G.JointAct)) ?_
  intro a ha
  have hw : Continuous (fun z : G.finkDomain U =>
      (((PMF.pure d) (a who)).toReal) *
        (∏ i ∈ (Finset.univ.erase who), z.1.1 (s, i) (a i))) := by
    fun_prop
  exact hw.mul (G.continuous_finkDiscountedAuxPayoff β s a who)

theorem continuous_finkGain (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (β : ℝ) {U : ℝ}
    (s : G.State) (who : ι) (d : G.Act who) :
    Continuous (fun z : G.finkDomain U => G.finkGain β z s who d) := by
  exact (G.continuous_finkDeviationAuxEU β s who d).sub
    (G.continuous_finkAuxEU β s who)

theorem continuous_finkGainSum (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (β : ℝ) {U : ℝ}
    (s : G.State) (who : ι) :
    Continuous (fun z : G.finkDomain U => G.finkGainSum β z s who) := by
  unfold finkGainSum
  exact continuous_finsetSum (s := (Finset.univ : Finset (G.Act who)))
    fun d _ => KernelGame.continuous_pospart.comp
      (G.continuous_finkGain β s who d)

/-- Every coordinate of Fink's strategy update is continuous. -/
theorem continuous_finkStrategyWeightUpdate (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (β : ℝ) {U : ℝ}
    (s : G.State) (who : ι) (d : G.Act who) :
    Continuous (fun z : G.finkDomain U =>
      G.finkStrategyWeightUpdate β z s who d) := by
  have hcoord : Continuous (fun z : G.finkDomain U => z.1.1 (s, who) d) := by
    fun_prop
  have hden : ∀ z : G.finkDomain U,
      1 + G.finkGainSum β z s who ≠ 0 := by
    intro z
    linarith [G.finkGainSum_nonneg β z s who]
  exact (hcoord.add (KernelGame.continuous_pospart.comp
      (G.continuous_finkGain β s who d))).div
    (continuous_const.add (G.continuous_finkGainSum β s who)) hden

/-- The auxiliary payoff remains in the stage-payoff cube when both the
discount and continuation value lie in their natural bounds. -/
theorem abs_discountedAuxPayoff_le (G : StochasticGame ι)
    (β U : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    (V : G.State → Payoff ι) (hV : ∀ s who, |V s who| ≤ U)
    (s : G.State) (a : G.JointAct) (who : ι) :
    |G.discountedAuxPayoff β V s a who| ≤ U := by
  have hcomp : 0 ≤ 1 - β := sub_nonneg.mpr hβ1
  have hEV : |expect (G.transition s a) (fun s' => V s' who)| ≤ U :=
    abs_expect_le_of_abs_le _ _ (fun s' => hV s' who)
  calc
    |G.discountedAuxPayoff β V s a who|
        ≤ |(1 - β) * G.stagePayoff s a who| +
            |β * expect (G.transition s a) (fun s' => V s' who)| :=
          abs_add_le _ _
    _ = (1 - β) * |G.stagePayoff s a who| +
          β * |expect (G.transition s a) (fun s' => V s' who)| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hcomp, abs_of_nonneg hβ0]
    _ ≤ (1 - β) * U + β * U :=
      add_le_add (mul_le_mul_of_nonneg_left (hpay s a who) hcomp)
        (mul_le_mul_of_nonneg_left hEV hβ0)
    _ = U := by ring

/-- The value component of Fink's map is the auxiliary expected payoff of
the current stationary profile. -/
def finkValueUpdate (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (β : ℝ) {U : ℝ}
    (z : G.finkDomain U) (s : G.State) (who : ι) : ℝ :=
  G.finkAuxEU β z s who

theorem abs_finkValueUpdate_le (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (β U : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    (z : G.finkDomain U) (s : G.State) (who : ι) :
    |G.finkValueUpdate β z s who| ≤ U := by
  rw [finkValueUpdate, G.finkAuxEU_eq_discountedAuxEU]
  exact abs_expect_le_of_abs_le _ _ fun a =>
    G.abs_discountedAuxPayoff_le β U hβ0 hβ1 hpay
      (G.finkValue z) (fun s' i => G.abs_finkValue_le z s' i) s a who

/-- The ambient-coordinate formula for Fink's joint strategy/value map. -/
def finkAmbientUpdate (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (β : ℝ) {U : ℝ}
    (z : G.finkDomain U) : G.FinkAmbient :=
  (fun p d => G.finkStrategyWeightUpdate β z p.1 p.2 d,
    fun s who => G.finkValueUpdate β z s who)

theorem finkAmbientUpdate_mem (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (β U : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    (z : G.finkDomain U) : G.finkAmbientUpdate β z ∈ G.finkDomain U := by
  constructor
  · intro p hp
    exact (G.finkStrategyUpdate β z p.1 p.2).property
  · constructor <;> intro s who
    · exact (abs_le.mp (G.abs_finkValueUpdate_le β U hβ0 hβ1 hpay z s who)).1
    · exact (abs_le.mp (G.abs_finkValueUpdate_le β U hβ0 hβ1 hpay z s who)).2

/-- Fink's continuous self-map of the compact strategy/value domain. -/
def finkMap (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (β U : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U) :
    G.finkDomain U → G.finkDomain U :=
  fun z => ⟨G.finkAmbientUpdate β z,
    G.finkAmbientUpdate_mem β U hβ0 hβ1 hpay z⟩

theorem continuous_finkMap (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (β U : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U) :
    Continuous (G.finkMap β U hβ0 hβ1 hpay) := by
  apply Continuous.subtype_mk
  apply Continuous.prodMk
  · exact continuous_pi fun p => continuous_pi fun d =>
      G.continuous_finkStrategyWeightUpdate β p.1 p.2 d
  · exact continuous_pi fun s => continuous_pi fun who =>
      G.continuous_finkAuxEU β s who

/-- The value coordinate of a fixed point of Fink's map is exactly its
auxiliary expected payoff.  Kept as a standalone projection lemma so limiting
arguments need not repeatedly unfold the proof-carrying subtype map. -/
theorem finkAuxEU_eq_finkValue_of_finkMap_fixedPoint
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (β U : ℝ)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    (z : G.finkDomain U)
    (hfix : G.finkMap β U hβ0 hβ1 hpay z = z)
    (s : G.State) (who : ι) :
    G.finkAuxEU β z s who = G.finkValue z s who := by
  have hcoord := congrArg (fun q : G.finkDomain U => q.1.2 s who) hfix
  simpa [finkMap, finkAmbientUpdate, finkValueUpdate, finkValue] using hcoord

/-- The discounted auxiliary normal-form game at state `s`. -/
def discountedAuxGame (G : StochasticGame ι) (β : ℝ)
    (V : G.State → Payoff ι) (s : G.State) : KernelGame ι :=
  KernelGame.ofPureEU G.Act (G.discountedAuxPayoff β V s)

/-- The semantic mixed extension of the auxiliary game is `discountedAuxEU`. -/
theorem mixedExtension_eu_discountedAuxGame
    (G : StochasticGame ι) [Fintype ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] (β : ℝ) (V : G.State → Payoff ι)
    (s : G.State) (m : ∀ i, PMF (G.Act i)) (who : ι) :
    (G.discountedAuxGame β V s).mixedExtension.eu m who =
      G.discountedAuxEU β V s m who := by
  haveI : Finite (G.discountedAuxGame β V s).Outcome :=
    inferInstanceAs (Finite G.JointAct)
  rw [KernelGame.mixedExtension_eu]
  simp [discountedAuxGame, discountedAuxEU, KernelGame.eu_ofPureEU]

/-- Fink's finite-coordinate gain is exactly the usual pure-deviation gain
in the corresponding auxiliary normal-form game. -/
theorem finkGain_eq_mixedGain (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (β : ℝ) {U : ℝ}
    (z : G.finkDomain U) (s : G.State) (who : ι) (d : G.Act who) :
    G.finkGain β z s who d =
      (G.discountedAuxGame β (G.finkValue z) s).mixedGain
        (G.finkProfile z s) who d := by
  haveI : Finite (G.discountedAuxGame β (G.finkValue z) s).Outcome :=
    inferInstanceAs (Finite G.JointAct)
  unfold finkGain KernelGame.mixedGain
  rw [G.finkDeviationAuxEU_eq_discountedAuxEU,
    G.finkAuxEU_eq_discountedAuxEU]
  rw [← G.mixedExtension_eu_discountedAuxGame,
    ← G.mixedExtension_eu_discountedAuxGame]
  rfl

/-- Consequently, Fink's positive-gain sum is the ordinary Nash-map gain
sum of the auxiliary game. -/
theorem finkGainSum_eq_gainSum (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (β : ℝ) {U : ℝ}
    (z : G.finkDomain U) (s : G.State) (who : ι) :
    G.finkGainSum β z s who =
      @KernelGame.gainSum ι inferInstance inferInstance
        (G.discountedAuxGame β (G.finkValue z) s)
        (fun i => inferInstanceAs (Fintype (G.Act i)))
        (G.finkProfile z s) who := by
  haveI : Finite (G.discountedAuxGame β (G.finkValue z) s).Outcome :=
    inferInstanceAs (Finite G.JointAct)
  simp only [finkGainSum, KernelGame.gainSum]
  exact Finset.sum_congr rfl fun d _ => congrArg KernelGame.pospart
    (G.finkGain_eq_mixedGain β z s who d)

/-- Brouwer supplies a fixed point of Fink's joint strategy/value map. -/
theorem exists_finkMap_fixedPoint (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] [∀ i, Nonempty (G.Act i)]
    (β U : ℝ) (hU : 0 ≤ U) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U) :
    ∃ z : G.finkDomain U,
      G.finkMap β U hβ0 hβ1 hpay z = z := by
  let f : C(G.finkDomain U, G.finkDomain U) :=
    ⟨G.finkMap β U hβ0 hβ1 hpay,
      G.continuous_finkMap β U hβ0 hβ1 hpay⟩
  exact _root_.brouwer_fixed_point (G.finkDomain U)
    (G.convex_finkDomain U) (G.isCompact_finkDomain U)
    (G.nonempty_finkDomain hU) f

/-- Decompose auxiliary expected payoff into current payoff and continuation
expectation. -/
theorem discountedAuxEU_eq (G : StochasticGame ι) [Fintype ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (β : ℝ) (V : G.State → Payoff ι) (s : G.State)
    (m : ∀ i, PMF (G.Act i)) (who : ι) :
    G.discountedAuxEU β V s m who =
      (1 - β) * expect (pmfPi m) (fun a => G.stagePayoff s a who) +
        β * expect (pmfPi m) (fun a =>
          expect (G.transition s a) (fun s' => V s' who)) := by
  unfold discountedAuxEU discountedAuxPayoff
  rw [expect_add, expect_const_mul, expect_const_mul]

/-- The one-stage payoff gain from replacing one component of a decoded
Fink profile by a pure action. -/
def finkStageGain (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} (z : G.finkDomain U)
    (s : G.State) (who : ι) (d : G.Act who) : ℝ :=
  G.mixedStageEU s
      (Function.update (G.finkProfile z s) who (PMF.pure d)) who -
    G.mixedStageEU s (G.finkProfile z s) who

/-- The continuation-value gain from replacing one component of a decoded
Fink profile by a pure action. -/
def finkContinuationGain (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (W : G.State → Payoff ι)
    {U : ℝ} (z : G.finkDomain U) (s : G.State)
    (who : ι) (d : G.Act who) : ℝ :=
  expect (pmfPi (Function.update (G.finkProfile z s)
      who (PMF.pure d))) (fun a =>
    expect (G.transition s a) (fun s' => W s' who)) -
  expect (pmfPi (G.finkProfile z s)) (fun a =>
    expect (G.transition s a) (fun s' => W s' who))

/-- Continuation gain is homogeneous in its continuation vector. -/
theorem finkContinuationGain_smul (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (c : ℝ) (W : G.State → Payoff ι)
    {U : ℝ} (z : G.finkDomain U) (s : G.State)
    (who : ι) (d : G.Act who) :
    G.finkContinuationGain (c • W) z s who d =
      c * G.finkContinuationGain W z s who d := by
  unfold finkContinuationGain
  simp_rw [Pi.smul_apply, smul_eq_mul, expect_const_mul]
  ring

/-- Baseline continuation expectation in the real coordinates of Fink's
domain.  This polynomial presentation is used for joint continuity in the
continuation vector and profile. -/
def finkContinuationCoordEU (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (W : G.State → Payoff ι)
    {U : ℝ} (z : G.finkDomain U) (s : G.State) (who : ι) : ℝ :=
  ∑ a : G.JointAct, (∏ i, z.1.1 (s, i) (a i)) *
    expect (G.transition s a) (fun s' => W s' who)

/-- Pure-deviation continuation expectation in Fink's real coordinates. -/
def finkDeviationContinuationCoordEU (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (W : G.State → Payoff ι)
    {U : ℝ} (z : G.finkDomain U) (s : G.State)
    (who : ι) (d : G.Act who) : ℝ :=
  ∑ a : G.JointAct,
    ((((PMF.pure d) (a who)).toReal) *
      (∏ i ∈ (Finset.univ.erase who), z.1.1 (s, i) (a i))) *
        expect (G.transition s a) (fun s' => W s' who)

/-- Continuation gain written entirely in the real coordinates of Fink's
finite-dimensional domain. -/
def finkContinuationCoordGain (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (W : G.State → Payoff ι)
    {U : ℝ} (z : G.finkDomain U) (s : G.State)
    (who : ι) (d : G.Act who) : ℝ :=
  G.finkDeviationContinuationCoordEU W z s who d -
    G.finkContinuationCoordEU W z s who

theorem finkContinuationCoordEU_eq (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (W : G.State → Payoff ι)
    {U : ℝ} (z : G.finkDomain U) (s : G.State) (who : ι) :
    G.finkContinuationCoordEU W z s who =
      expect (pmfPi (G.finkProfile z s)) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) := by
  classical
  rw [finkContinuationCoordEU, expect_eq_sum]
  refine Finset.sum_congr rfl ?_
  intro a ha
  congr 1
  simp [pmfPi_apply, finkProfile, finkSimplex,
    stdSimplexEquiv_symm_apply]
  rfl

theorem finkDeviationContinuationCoordEU_eq (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (W : G.State → Payoff ι)
    {U : ℝ} (z : G.finkDomain U) (s : G.State)
    (who : ι) (d : G.Act who) :
    G.finkDeviationContinuationCoordEU W z s who d =
      expect (pmfPi (Function.update (G.finkProfile z s)
          who (PMF.pure d))) (fun a =>
        expect (G.transition s a) (fun s' => W s' who)) := by
  classical
  rw [finkDeviationContinuationCoordEU, expect_eq_sum]
  refine Finset.sum_congr rfl ?_
  intro a ha
  congr 1
  rw [pmfPi_apply_update_family]
  by_cases hsa : a who = d
  · subst hsa
    simp [PMF.pure_apply, finkProfile, finkSimplex,
      stdSimplexEquiv_symm_apply]
    rfl
  · simp [PMF.pure_apply, hsa]

theorem finkContinuationCoordGain_eq (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (W : G.State → Payoff ι)
    {U : ℝ} (z : G.finkDomain U) (s : G.State)
    (who : ι) (d : G.Act who) :
    G.finkContinuationCoordGain W z s who d =
      G.finkContinuationGain W z s who d := by
  unfold finkContinuationCoordGain finkContinuationGain
  rw [G.finkDeviationContinuationCoordEU_eq,
    G.finkContinuationCoordEU_eq]

/-- The coordinate presentation of continuation gain is a finite polynomial
in the continuation vector and Fink-domain coordinates. -/
theorem continuous_finkContinuationCoordGain_param
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    (s : G.State) (who : ι) (d : G.Act who) :
    Continuous (fun q : (G.State → Payoff ι) × G.finkDomain U =>
      G.finkContinuationCoordGain q.1 q.2 s who d) := by
  unfold finkContinuationCoordGain finkDeviationContinuationCoordEU
    finkContinuationCoordEU
  simp_rw [expect_eq_sum]
  fun_prop

/-- Continuation gain is jointly continuous in the continuation vector and
the finite-dimensional Fink coordinates. -/
theorem continuous_finkContinuationGain_param
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    (s : G.State) (who : ι) (d : G.Act who) :
    Continuous (fun q : (G.State → Payoff ι) × G.finkDomain U =>
      G.finkContinuationGain q.1 q.2 s who d) := by
  have hc := G.continuous_finkContinuationCoordGain_param
    (U := U) s who d
  convert hc using 1
  funext q
  exact (G.finkContinuationCoordGain_eq q.1 q.2 s who d).symm

/-- A discounted auxiliary gain is exactly the weighted sum of its current
stage gain and its continuation-value gain. -/
theorem finkGain_eq_stage_add_continuation (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (β : ℝ) {U : ℝ}
    (z : G.finkDomain U) (s : G.State) (who : ι) (d : G.Act who) :
    G.finkGain β z s who d =
      (1 - β) * G.finkStageGain z s who d +
        β * G.finkContinuationGain (G.finkValue z) z s who d := by
  unfold finkGain
  rw [G.finkDeviationAuxEU_eq_discountedAuxEU,
    G.finkAuxEU_eq_discountedAuxEU,
    G.discountedAuxEU_eq, G.discountedAuxEU_eq]
  unfold finkStageGain finkContinuationGain mixedStageEU
  ring

/-- At discount zero, Fink's auxiliary gain is exactly the one-stage gain. -/
@[simp] theorem finkGain_zero_eq_finkStageGain (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ}
    (z : G.finkDomain U) (s : G.State) (who : ι) (d : G.Act who) :
    G.finkGain 0 z s who d = G.finkStageGain z s who d := by
  simpa using G.finkGain_eq_stage_add_continuation 0 z s who d

/-- The relative bias of a discounted Fink value around an arbitrary target
`W`, in the normalization relevant to average payoff. -/
def finkRelativeBias (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (β : ℝ) (W : G.State → Payoff ι) {U : ℝ}
    (z : G.finkDomain U) : G.State → Payoff ι :=
  fun s who => (β / (1 - β)) * (G.finkValue z s who - W s who)

/-- Continuation gain is linear in the continuation vector, so relative bias
records exactly the scaled difference between the discounted-value and target
continuation gains. -/
theorem finkContinuationGain_relativeBias (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (β : ℝ)
    (W : G.State → Payoff ι) {U : ℝ} (z : G.finkDomain U)
    (s : G.State) (who : ι) (d : G.Act who) :
    G.finkContinuationGain (G.finkRelativeBias β W z) z s who d =
      (β / (1 - β)) *
        (G.finkContinuationGain (G.finkValue z) z s who d -
          G.finkContinuationGain W z s who d) := by
  let q := β / (1 - β)
  have hinner (a : G.JointAct) :
      expect (G.transition s a)
          (fun s' => G.finkRelativeBias β W z s' who) =
        q * (expect (G.transition s a) (fun s' => G.finkValue z s' who) -
          expect (G.transition s a) (fun s' => W s' who)) := by
    unfold finkRelativeBias
    rw [expect_const_mul, expect_sub]
  unfold finkContinuationGain
  simp_rw [hinner, expect_const_mul, expect_sub]
  dsimp [q]
  ring

/-- Centering at any target `W` separates normalized discounted gain into
current stage gain, target continuation drift, and relative-bias drift.  This
is the exact higher-order identity needed on the continuation-neutral face. -/
theorem finkGain_div_one_sub_eq (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {β : ℝ} (hβ : β < 1)
    (W : G.State → Payoff ι) {U : ℝ} (z : G.finkDomain U)
    (s : G.State) (who : ι) (d : G.Act who) :
    G.finkGain β z s who d / (1 - β) =
      G.finkStageGain z s who d +
        (β / (1 - β)) * G.finkContinuationGain W z s who d +
          G.finkContinuationGain (G.finkRelativeBias β W z) z s who d := by
  rw [G.finkGain_eq_stage_add_continuation,
    G.finkContinuationGain_relativeBias]
  have hden : 1 - β ≠ 0 := ne_of_gt (sub_pos.mpr hβ)
  field_simp [hden]
  ring

/-- `x` is a statewise Nash selection for the auxiliary games determined by
`V`.  This is the best-response component of Fink's correspondence. -/
def IsDiscountedAuxNash (G : StochasticGame ι) [Fintype ι]
    [DecidableEq ι] (β : ℝ) (V : G.State → Payoff ι)
    (x : G.StationaryMixedProfile) : Prop :=
  ∀ (s : G.State) (who : ι) (d : PMF (G.Act who)),
    G.discountedAuxEU β V s (Function.update (x s) who d) who ≤
      G.discountedAuxEU β V s (x s) who

/-- For every continuation payoff, auxiliary mixed Nash profiles can be
selected simultaneously at all states.  This proves nonemptiness of the
best-response fibers required by Fink's fixed-point correspondence. -/
theorem exists_isDiscountedAuxNash (G : StochasticGame ι)
    [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] [∀ i, Nonempty (G.Act i)]
    (β : ℝ) (V : G.State → Payoff ι) :
    ∃ x : G.StationaryMixedProfile, G.IsDiscountedAuxNash β V x := by
  have hex : ∀ s : G.State, ∃ m : ∀ i, PMF (G.Act i),
      ∀ (who : ι) (d : PMF (G.Act who)),
        G.discountedAuxEU β V s (Function.update m who d) who ≤
          G.discountedAuxEU β V s m who := by
    intro s
    haveI : ∀ i, Finite ((G.discountedAuxGame β V s).Strategy i) :=
      fun i => inferInstanceAs (Finite (G.Act i))
    haveI : ∀ i, Nonempty ((G.discountedAuxGame β V s).Strategy i) :=
      fun i => inferInstanceAs (Nonempty (G.Act i))
    haveI : Finite (G.discountedAuxGame β V s).Outcome :=
      inferInstanceAs (Finite G.JointAct)
    obtain ⟨m, hm⟩ := (G.discountedAuxGame β V s).mixed_nash_exists
    refine ⟨m, fun who d => ?_⟩
    have h := hm who d
    rw [G.mixedExtension_eu_discountedAuxGame,
      G.mixedExtension_eu_discountedAuxGame] at h
    exact h
  choose x hx using hex
  exact ⟨x, hx⟩

/-- A Fink discounted stationary Bellman equilibrium: `x` is a statewise Nash
profile of the auxiliary games and `V` is consistent with the auxiliary
payoff generated by `x`. -/
def IsDiscountedStationaryBellmanEq (G : StochasticGame ι) [Fintype ι]
    [DecidableEq ι] (β : ℝ) (x : G.StationaryMixedProfile)
    (V : G.State → Payoff ι) : Prop :=
  G.IsDiscountedAuxNash β V x ∧
    ∀ (s : G.State) (who : ι), G.discountedAuxEU β V s (x s) who = V s who

/-- A fixed point of Fink's map decodes to the corresponding discounted
stationary Bellman equilibrium. -/
theorem isDiscountedStationaryBellmanEq_of_finkMap_fixedPoint
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (β U : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    (z : G.finkDomain U)
    (hfix : G.finkMap β U hβ0 hβ1 hpay z = z) :
    G.IsDiscountedStationaryBellmanEq β (G.finkProfile z)
      (G.finkValue z) := by
  constructor
  · intro s who dev
    let actFintype : ∀ i, Fintype (G.Act i) := inferInstance
    haveI : ∀ i,
        Fintype ((G.discountedAuxGame β (G.finkValue z) s).Strategy i) :=
      by
        change ∀ i, Fintype (G.Act i)
        infer_instance
    haveI : Finite (G.discountedAuxGame β (G.finkValue z) s).Outcome :=
      inferInstanceAs (Finite G.JointAct)
    have hfp : ∀ (i : ι) (d : G.Act i),
        ((G.finkProfile z s i) d).toReal *
              (1 + (G.discountedAuxGame β (G.finkValue z) s).gainSum
                (G.finkProfile z s) i) =
          ((G.finkProfile z s i) d).toReal +
            KernelGame.pospart
              ((G.discountedAuxGame β (G.finkValue z) s).mixedGain
                (G.finkProfile z s) i d) := by
      intro i d
      have hcoord := congrArg
        (fun q : G.finkDomain U => q.1.1 (s, i) d) hfix
      have hden : 1 + G.finkGainSum β z s i ≠ 0 := by
        linarith [G.finkGainSum_nonneg β z s i]
      have hsum :
          (G.discountedAuxGame β (G.finkValue z) s).gainSum
              (G.finkProfile z s) i = G.finkGainSum β z s i := by
        unfold KernelGame.gainSum finkGainSum
        apply Finset.sum_congr
        · ext x
          constructor
          · intro hx
            exact @Finset.mem_univ (G.Act i) (actFintype i) x
          · intro hx
            exact @Finset.mem_univ
              ((G.discountedAuxGame β (G.finkValue z) s).Strategy i)
              (inferInstance) x
        · intro x hx
          rw [← G.finkGain_eq_mixedGain β z s i x]
      have halg : z.1.1 (s, i) d * (1 + G.finkGainSum β z s i) =
          z.1.1 (s, i) d + KernelGame.pospart (G.finkGain β z s i d) := by
        have hdiv :
            (z.1.1 (s, i) d + KernelGame.pospart (G.finkGain β z s i d)) /
                (1 + G.finkGainSum β z s i) = z.1.1 (s, i) d := by
          simpa [finkMap, finkAmbientUpdate, finkStrategyWeightUpdate] using hcoord
        exact ((div_eq_iff hden).mp hdiv).symm
      rw [hsum, ← G.finkGain_eq_mixedGain β z s i d,
        G.finkProfile_apply_toReal]
      exact halg
    have hN :=
      (G.discountedAuxGame β (G.finkValue z) s).nash_fp_is_nash
        (G.finkProfile z s) hfp
    have hdev := hN who dev
    rw [G.mixedExtension_eu_discountedAuxGame,
      G.mixedExtension_eu_discountedAuxGame] at hdev
    exact hdev
  · intro s who
    rw [← G.finkAuxEU_eq_discountedAuxEU]
    exact G.finkAuxEU_eq_finkValue_of_finkMap_fixedPoint
      β U hβ0 hβ1 hpay z hfix s who

/-- In particular, every pure deviation has no positive auxiliary gain at a
fixed point of Fink's map. -/
theorem finkDeviationAuxEU_le_finkAuxEU_of_finkMap_fixedPoint
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (β U : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    (z : G.finkDomain U)
    (hfix : G.finkMap β U hβ0 hβ1 hpay z = z)
    (s : G.State) (who : ι) (d : G.Act who) :
    G.finkDeviationAuxEU β z s who d ≤ G.finkAuxEU β z s who := by
  have hF := G.isDiscountedStationaryBellmanEq_of_finkMap_fixedPoint
    β U hβ0 hβ1 hpay z hfix
  have hdev := hF.1 s who (PMF.pure d)
  rw [← G.finkDeviationAuxEU_eq_discountedAuxEU,
    ← G.finkAuxEU_eq_discountedAuxEU] at hdev
  exact hdev

/-- Every pure action used with positive probability at a Fink fixed point
has exactly zero auxiliary gain, not merely nonpositive gain. -/
theorem finkGain_eq_zero_of_finkMap_fixedPoint_of_ne_zero
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (β U : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    (z : G.finkDomain U)
    (hfix : G.finkMap β U hβ0 hβ1 hpay z = z)
    (s : G.State) (who : ι) (d : G.Act who)
    (hpos : G.finkProfile z s who d ≠ 0) :
    G.finkGain β z s who d = 0 := by
  haveI : Finite (G.discountedAuxGame β (G.finkValue z) s).Outcome :=
    inferInstanceAs (Finite G.JointAct)
  have hupper : ∀ d' : G.Act who, G.finkGain β z s who d' ≤ 0 := by
    intro d'
    exact sub_nonpos.mpr
      (G.finkDeviationAuxEU_le_finkAuxEU_of_finkMap_fixedPoint
        β U hβ0 hβ1 hpay z hfix s who d')
  have hmean : expect (G.finkProfile z s who)
      (fun d' => G.finkGain β z s who d') = 0 := by
    have hwg := (G.discountedAuxGame β (G.finkValue z) s).weighted_gain_sum_zero
      (G.finkProfile z s) who
    calc
      expect (G.finkProfile z s who) (fun d' => G.finkGain β z s who d') =
          expect (G.finkProfile z s who) (fun d' =>
            (G.discountedAuxGame β (G.finkValue z) s).mixedGain
              (G.finkProfile z s) who d') := by
        exact congrArg (expect (G.finkProfile z s who))
          (funext fun d' => G.finkGain_eq_mixedGain β z s who d')
      _ = 0 := hwg
  apply le_antisymm (hupper d)
  by_contra hnot
  have hlt : G.finkGain β z s who d < 0 := lt_of_not_ge hnot
  have hstrict := expect_lt_const_of_le_of_exists_lt
    (G.finkProfile z s who) (fun d' => G.finkGain β z s who d')
      hupper ⟨d, hpos, hlt⟩
  rw [hmean] at hstrict
  linarith

/-- At a discounted Fink fixed point, the centered gain decomposition is
nonpositive for every pure deviation.  Choosing a harmonic/excessive limit
as `W` isolates the strict-drift actions from the continuation-neutral face. -/
theorem finkCenteredGain_nonpos_of_finkMap_fixedPoint
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (β U : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    (z : G.finkDomain U)
    (hfix : G.finkMap β U hβ0 hβ1.le hpay z = z)
    (W : G.State → Payoff ι)
    (s : G.State) (who : ι) (d : G.Act who) :
    G.finkStageGain z s who d +
        (β / (1 - β)) * G.finkContinuationGain W z s who d +
          G.finkContinuationGain (G.finkRelativeBias β W z) z s who d ≤ 0 := by
  have haux := G.finkDeviationAuxEU_le_finkAuxEU_of_finkMap_fixedPoint
    β U hβ0 hβ1.le hpay z hfix s who d
  have hgain : G.finkGain β z s who d ≤ 0 := sub_nonpos.mpr haux
  have hdiv : G.finkGain β z s who d / (1 - β) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hgain (sub_nonneg.mpr hβ1.le)
  rw [G.finkGain_div_one_sub_eq hβ1 W] at hdiv
  exact hdiv

/-- On the support of a discounted Fink fixed point, the centered
higher-order gain equation holds with equality. -/
theorem finkCenteredGain_eq_zero_of_finkMap_fixedPoint_of_ne_zero
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (β U : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    (z : G.finkDomain U)
    (hfix : G.finkMap β U hβ0 hβ1.le hpay z = z)
    (W : G.State → Payoff ι)
    (s : G.State) (who : ι) (d : G.Act who)
    (hpos : G.finkProfile z s who d ≠ 0) :
    G.finkStageGain z s who d +
        (β / (1 - β)) * G.finkContinuationGain W z s who d +
          G.finkContinuationGain (G.finkRelativeBias β W z) z s who d = 0 := by
  rw [← G.finkGain_div_one_sub_eq hβ1 W]
  rw [G.finkGain_eq_zero_of_finkMap_fixedPoint_of_ne_zero
    β U hβ0 hβ1.le hpay z hfix s who d hpos]
  simp

/-- **Fink's theorem (finite discounted stochastic games).**  Every bounded
finite stochastic game has a stationary mixed profile and continuation value
satisfying the discounted Bellman equations and all statewise best-response
inequalities. -/
theorem exists_isDiscountedStationaryBellmanEq_bounded (G : StochasticGame ι)
    [Finite G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Finite (G.Act i)] [∀ i, Nonempty (G.Act i)]
    (β U : ℝ) (hU : 0 ≤ U) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U) :
    ∃ (x : G.StationaryMixedProfile) (V : G.State → Payoff ι),
      G.IsDiscountedStationaryBellmanEq β x V ∧
        ∀ s who, |V s who| ≤ U := by
  letI : Fintype G.State := Fintype.ofFinite G.State
  letI : ∀ i, Fintype (G.Act i) := fun i => Fintype.ofFinite (G.Act i)
  obtain ⟨z, hz⟩ := G.exists_finkMap_fixedPoint β U hU hβ0 hβ1 hpay
  exact ⟨G.finkProfile z, G.finkValue z,
    G.isDiscountedStationaryBellmanEq_of_finkMap_fixedPoint
      β U hβ0 hβ1 hpay z hz,
    fun s who => G.abs_finkValue_le z s who⟩

/-- Certificate-only form of Fink's theorem. -/
theorem exists_isDiscountedStationaryBellmanEq (G : StochasticGame ι)
    [Finite G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Finite (G.Act i)] [∀ i, Nonempty (G.Act i)]
    (β U : ℝ) (hU : 0 ≤ U) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U) :
    ∃ (x : G.StationaryMixedProfile) (V : G.State → Payoff ι),
      G.IsDiscountedStationaryBellmanEq β x V := by
  obtain ⟨x, V, hF, hV⟩ :=
    G.exists_isDiscountedStationaryBellmanEq_bounded
      β U hU hβ0 hβ1 hpay
  exact ⟨x, V, hF⟩

/-- Value consistency gives the historywise discounted Bellman equality for
the induced stationary behavior profile. -/
theorem IsDiscountedStationaryBellmanEq.onProfile_bellman_eq
    {G : StochasticGame ι} [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {β : ℝ} {x : G.StationaryMixedProfile} {V : G.State → Payoff ι}
    (hF : G.IsDiscountedStationaryBellmanEq β x V)
    (who : ι) (t : ℕ) (h : G.Hist t) :
    V h.2 who = (1 - β) * G.stageEUAt (G.markovBehaviorProfile x) h who +
      β * expect (G.stageActionDist (G.markovBehaviorProfile x) h) (fun a =>
        expect (G.transition h.2 a) (fun s' => V s' who)) := by
  rw [← hF.2 h.2 who, G.discountedAuxEU_eq]
  rfl

/-- Statewise auxiliary optimality gives a Bellman upper inequality after
every history for any unilateral behavior-strategy deviation. -/
theorem IsDiscountedStationaryBellmanEq.deviation_bellman_ge
    {G : StochasticGame ι} [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {β : ℝ} {x : G.StationaryMixedProfile} {V : G.State → Payoff ι}
    (hF : G.IsDiscountedStationaryBellmanEq β x V)
    (who : ι) (dev : G.BehaviorStrategy who) (t : ℕ) (h : G.Hist t) :
    (1 - β) * G.stageEUAt
        (Function.update (G.markovBehaviorProfile x) who dev) h who +
      β * expect
        (G.stageActionDist
          (Function.update (G.markovBehaviorProfile x) who dev) h)
        (fun a => expect (G.transition h.2 a) (fun s' => V s' who)) ≤
      V h.2 who := by
  have hopt := hF.1 h.2 who (dev t h)
  rw [hF.2 h.2 who] at hopt
  unfold stageEUAt
  rw [G.stageActionDist_update_markovBehaviorProfile]
  rw [← G.discountedAuxEU_eq]
  exact hopt

/-- The on-profile Fink certificate gives a quantitative lower
finite-horizon payoff bound. -/
theorem IsDiscountedStationaryBellmanEq.finiteAveragePayoff_ge
    {G : StochasticGame ι} [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {β : ℝ} {x : G.StationaryMixedProfile} {V : G.State → Payoff ι}
    (hF : G.IsDiscountedStationaryBellmanEq β x V)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (who : ι) (s₀ : G.State)
    {c C : ℝ} (hz : ∀ s, c ≤ V s who) (hv : ∀ s, |V s who| ≤ C)
    {T : ℕ} (hT : 0 < T) :
    c - 2 * ((β / (1 - β)) * C) / (T : ℝ) ≤
      G.finiteAveragePayoff s₀ T (G.markovBehaviorProfile x) who := by
  have h := G.finiteAveragePayoff_ge_of_discounted_bellman_le
    (G.markovBehaviorProfile x) s₀ who (fun s => V s who)
    hβ0 hβ1 hz hv (δ := 0) (fun t hist => by
      rw [hF.onProfile_bellman_eq who t hist]
      simp) hT
  simpa using h

/-- The on-profile Fink certificate also gives the matching upper
finite-horizon payoff bound. -/
theorem IsDiscountedStationaryBellmanEq.finiteAveragePayoff_le
    {G : StochasticGame ι} [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {β : ℝ} {x : G.StationaryMixedProfile} {V : G.State → Payoff ι}
    (hF : G.IsDiscountedStationaryBellmanEq β x V)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (who : ι) (s₀ : G.State)
    {c C : ℝ} (hz : ∀ s, V s who ≤ c) (hv : ∀ s, |V s who| ≤ C)
    {T : ℕ} (hT : 0 < T) :
    G.finiteAveragePayoff s₀ T (G.markovBehaviorProfile x) who ≤
      c + 2 * ((β / (1 - β)) * C) / (T : ℝ) := by
  have h := G.finiteAveragePayoff_le_of_discounted_bellman_ge
    (G.markovBehaviorProfile x) s₀ who (fun s => V s who)
    hβ0 hβ1 hz hv (δ := 0) (fun t hist => by
      rw [hF.onProfile_bellman_eq who t hist]
      simp) hT
  simpa using h

/-- Every history-dependent unilateral deviation is capped by the upper
finite-horizon bound certified by Fink's statewise best-response condition. -/
theorem IsDiscountedStationaryBellmanEq.deviation_finiteAveragePayoff_le
    {G : StochasticGame ι} [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {β : ℝ} {x : G.StationaryMixedProfile} {V : G.State → Payoff ι}
    (hF : G.IsDiscountedStationaryBellmanEq β x V)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (who : ι)
    (dev : G.BehaviorStrategy who) (s₀ : G.State)
    {c C : ℝ} (hz : ∀ s, V s who ≤ c) (hv : ∀ s, |V s who| ≤ C)
    {T : ℕ} (hT : 0 < T) :
    G.finiteAveragePayoff s₀ T
        (Function.update (G.markovBehaviorProfile x) who dev) who ≤
      c + 2 * ((β / (1 - β)) * C) / (T : ℝ) := by
  have h := G.finiteAveragePayoff_le_of_discounted_bellman_ge
    (Function.update (G.markovBehaviorProfile x) who dev) s₀ who
    (fun s => V s who) hβ0 hβ1 hz hv (δ := 0)
    (fun t hist => by
      have hdev := hF.deviation_bellman_ge who dev t hist
      simpa using hdev) hT
  simpa using h

/-- A direct discounted-to-uniform bridge.  If arbitrarily accurate Fink
certificates have continuation values uniformly close (over all states and
players) to one vector `v`, then `v` is a uniform equilibrium payoff.

This isolates the remaining substantive issue after Fink's theorem: selecting
discounted certificates whose continuation values stabilize in the strong
state-uniform sense needed by the elementary stationary argument. -/
theorem isUniformEquilibriumPayoff_of_fink_certificates
    (G : StochasticGame ι) [Finite G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Finite (G.Act i)] (s₀ : G.State) (v : Payoff ι)
    (hcert : ∀ η : ℝ, 0 < η →
      ∃ (β : ℝ) (x : G.StationaryMixedProfile)
        (V : G.State → Payoff ι) (C : ℝ),
        0 ≤ β ∧ β < 1 ∧ 0 ≤ C ∧
          G.IsDiscountedStationaryBellmanEq β x V ∧
          (∀ s who, |V s who| ≤ C) ∧
          ∀ s who, |V s who - v who| ≤ η) :
    G.IsUniformEquilibriumPayoff s₀ v := by
  apply G.isUniformEquilibriumPayoff_of_deviation_caps s₀ v
  intro δ hδ
  have hη : 0 < δ / 2 := by linarith
  obtain ⟨β, x, V, C, hβ0, hβ1, hC, hF, hV, hclose⟩ :=
    hcert (δ / 2) hη
  let K : ℝ := 2 * ((β / (1 - β)) * C)
  obtain ⟨N, hN⟩ := exists_nat_ge (K / (δ / 2))
  refine ⟨G.markovBehaviorProfile x, N + 1, fun T hT => ?_⟩
  have hTpos : 0 < T := lt_of_lt_of_le (Nat.zero_lt_succ N) hT
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hTpos
  have hNT : (N : ℝ) ≤ T := by exact_mod_cast (Nat.le_trans (Nat.le_succ N) hT)
  have hratio : K / (δ / 2) ≤ (T : ℝ) := le_trans hN hNT
  have hK : K ≤ (T : ℝ) * (δ / 2) := (div_le_iff₀ hη).mp hratio
  have hboundary : K / (T : ℝ) ≤ δ / 2 := by
    rw [div_le_iff₀ hTreal]
    nlinarith
  constructor
  · intro who
    have hlo := hF.finiteAveragePayoff_ge hβ0 hβ1 who s₀
      (c := v who - δ / 2) (C := C)
      (fun s => by
        have hs := (abs_le.mp (hclose s who)).1
        linarith)
      (fun s => hV s who) hTpos
    have hup := hF.finiteAveragePayoff_le hβ0 hβ1 who s₀
      (c := v who + δ / 2) (C := C)
      (fun s => by
        have hs := (abs_le.mp (hclose s who)).2
        linarith)
      (fun s => hV s who) hTpos
    change |G.finiteAveragePayoff s₀ T (G.markovBehaviorProfile x) who -
      v who| ≤ δ
    rw [abs_le]
    constructor <;> dsimp [K] at hboundary <;> linarith
  · intro who dev
    have hup := hF.deviation_finiteAveragePayoff_le hβ0 hβ1 who dev s₀
      (c := v who + δ / 2) (C := C)
      (fun s => by
        have hs := (abs_le.mp (hclose s who)).2
        linarith)
      (fun s => hV s who) hTpos
    dsimp [K] at hboundary
    linarith

end StochasticGame
end GameTheory
