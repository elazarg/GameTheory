/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.AnalyticBellmanHierarchy
import GameTheory.Concepts.Stochastic.FinkObstructionFarkas
import GameTheory.Concepts.Stochastic.OrientedResponseExtraction
import Math.Probability.AdaptiveOccupationFlow

/-!
# Analytic coordinates for Fink obstruction systems

Semantic Fink kernels are PMFs and are therefore available only after a
Bellman assignment has been proved to lie in the polynomial solution set.
For parametric Farkas selection we instead need ordinary analytic functions
through the endpoint.

This file writes pure-deviation joint weights, transition kernels, stage
gains, continuation gains, and the complete obstruction matrix directly in
the raw mixing coordinates of an `AnalyticBellmanGerm`. At every positive
valid parameter these formulas agree with the semantic Fink quantities.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace AnalyticBellmanGerm

open Math Math.LinearAlgebra Math.Probability Set

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

/-- Raw joint-action weight after fixing one player's action. -/
def rawPureDeviationProfileWeight
    (germ : G.AnalyticBellmanGerm)
    (t : ℝ) (s : G.State) (who : ι) (d : G.Act who)
    (a : G.JointAct) : ℝ :=
  if a who = d then
    ∏ other ∈ Finset.univ.erase who,
      germ.assignment t (BellmanVar.mix s other (a other))
  else 0

/-- Raw pure-deviation state kernel, defined through the endpoint. -/
def rawPureDeviationStateKernelCurve
    (germ : G.AnalyticBellmanGerm) :
    ℝ → G.State → ∀ who : ι, G.Act who → G.State → ℝ :=
  fun t s who d destination =>
    ∑ a, germ.rawPureDeviationProfileWeight t s who d a *
      (G.transition s a destination).toReal

/-- Pure-deviation stage gain in raw analytic mixing coordinates. -/
def rawPureDeviationStageGainCurve
    (germ : G.AnalyticBellmanGerm) :
    ℝ → G.State → ∀ who : ι, G.Act who → ℝ :=
  fun t s who d =>
    (∑ a, germ.rawPureDeviationProfileWeight t s who d a *
      G.stagePayoff s a who) -
        germ.rawStageCurve t s who

/-- Pure-deviation continuation gain against a fixed payoff vector, written
as the difference of the raw deviation and baseline state kernels. -/
def rawPureDeviationContinuationGainCurve
    (germ : G.AnalyticBellmanGerm)
    (W : G.State → Payoff ι) :
    ℝ → G.State → ∀ who : ι, G.Act who → ℝ :=
  fun t s who d =>
    ∑ destination,
      (germ.rawPureDeviationStateKernelCurve t s who d destination -
        germ.rawStateKernelCurve t s destination) * W destination who

/-- Actual analytic occupation columns of the baseline transitions and all
pure deviations. These use arrival mass minus source mass and therefore
represent operational transitions, not formal signed perturbations. -/
def rawAnalyticOccupationColumn
    (germ : G.AnalyticBellmanGerm) :
    ℝ →
      (G.State ⊕ (Σ who : ι, G.State × G.Act who)) →
      G.State → ℝ
  | t, Sum.inl source, destination =>
      germ.rawStateKernelCurve t source destination -
        if destination = source then 1 else 0
  | t, Sum.inr e, destination =>
      germ.rawPureDeviationStateKernelCurve
          t e.2.1 e.1 e.2.2 destination -
        if destination = e.2.1 then 1 else 0

/-- Semantic actual transition attached to a baseline-state or
pure-deviation occupation index at one valid germ parameter. -/
def finkActualOccupationKernelAt
    (germ : G.AnalyticBellmanGerm)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius) :
    (G.State ⊕ (Σ who : ι, G.State × G.Act who)) → PMF G.State :=
  occupationKernel
    (G.finkStateKernel (germ.finkPointAt ht))
    (fun e : Σ who : ι, G.State × G.Act who =>
      G.finkPureDeviationStateKernel
        (germ.finkPointAt ht) e.2.1 e.1 e.2.2)

/-- Source state attached to each actual occupation index. -/
def finkActualOccupationSource :
    (G.State ⊕ (Σ who : ι, G.State × G.Act who)) → G.State :=
  occupationSource
    (fun e : Σ who : ι, G.State × G.Act who => e.2.1)

omit [DecidableEq G.State] in
theorem analytic_rawPureDeviationProfileWeight
    (germ : G.AnalyticBellmanGerm)
    (s : G.State) (who : ι) (d : G.Act who) (a : G.JointAct) :
    AnalyticAt ℝ
      (fun t => germ.rawPureDeviationProfileWeight t s who d a) 0 := by
  by_cases had : a who = d
  · simp only [rawPureDeviationProfileWeight, if_pos had]
    exact (Finset.univ.erase who).analyticAt_fun_prod fun other _ =>
      germ.analytic_coordinate (BellmanVar.mix s other (a other))
  · simpa only [rawPureDeviationProfileWeight, if_neg had] using
      (analyticAt_const : AnalyticAt ℝ (fun _ : ℝ => (0 : ℝ)) 0)

omit [DecidableEq G.State] in
theorem analytic_rawPureDeviationStateKernelCurve
    (germ : G.AnalyticBellmanGerm) :
    AnalyticAt ℝ germ.rawPureDeviationStateKernelCurve 0 := by
  rw [analyticAt_pi_iff]
  intro s
  rw [analyticAt_pi_iff]
  intro who
  rw [analyticAt_pi_iff]
  intro d
  rw [analyticAt_pi_iff]
  intro destination
  exact Finset.univ.analyticAt_fun_sum fun a _ =>
    (germ.analytic_rawPureDeviationProfileWeight s who d a).mul
      analyticAt_const

omit [DecidableEq G.State] in
theorem analytic_rawPureDeviationStageGainCurve
    (germ : G.AnalyticBellmanGerm) :
    AnalyticAt ℝ germ.rawPureDeviationStageGainCurve 0 := by
  rw [analyticAt_pi_iff]
  intro s
  rw [analyticAt_pi_iff]
  intro who
  rw [analyticAt_pi_iff]
  intro d
  exact
    (Finset.univ.analyticAt_fun_sum fun a _ =>
      (germ.analytic_rawPureDeviationProfileWeight s who d a).mul
        analyticAt_const).sub
      (((analyticAt_pi_iff.mp
        ((analyticAt_pi_iff.mp germ.analytic_rawStageCurve) s)) who))

omit [DecidableEq G.State] in
theorem analytic_rawPureDeviationContinuationGainCurve
    (germ : G.AnalyticBellmanGerm) (W : G.State → Payoff ι) :
    AnalyticAt ℝ
      (germ.rawPureDeviationContinuationGainCurve W) 0 := by
  rw [analyticAt_pi_iff]
  intro s
  rw [analyticAt_pi_iff]
  intro who
  rw [analyticAt_pi_iff]
  intro d
  apply Finset.univ.analyticAt_fun_sum
  intro destination _
  exact
    ((((analyticAt_pi_iff.mp
      ((analyticAt_pi_iff.mp
        ((analyticAt_pi_iff.mp
          ((analyticAt_pi_iff.mp
            germ.analytic_rawPureDeviationStateKernelCurve) s)) who)) d))
              destination).sub
        (((analyticAt_pi_iff.mp
          ((analyticAt_pi_iff.mp
            germ.analytic_rawStateKernelCurve) s)) destination))).mul
      analyticAt_const)

theorem analytic_rawAnalyticOccupationColumn
    (germ : G.AnalyticBellmanGerm) :
    ∀ index destination,
      AnalyticAt ℝ
        (fun t =>
          germ.rawAnalyticOccupationColumn t index destination) 0 := by
  intro index destination
  cases index with
  | inl source =>
      exact
        (((analyticAt_pi_iff.mp
          ((analyticAt_pi_iff.mp
            germ.analytic_rawStateKernelCurve) source)) destination).sub
          analyticAt_const)
  | inr e =>
      exact
        (((analyticAt_pi_iff.mp
          ((analyticAt_pi_iff.mp
            ((analyticAt_pi_iff.mp
              ((analyticAt_pi_iff.mp
                germ.analytic_rawPureDeviationStateKernelCurve)
                e.2.1)) e.1)) e.2.2)) destination).sub
          analyticAt_const)

omit [DecidableEq G.State] in
/-- At a valid positive point, raw pure-deviation joint mass is the real
mass of the semantic independent action law. -/
theorem rawPureDeviationProfileWeight_eq_pmfPi_finkPointAt
    (germ : G.AnalyticBellmanGerm)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (s : G.State) (who : ι) (d : G.Act who) (a : G.JointAct) :
    germ.rawPureDeviationProfileWeight t s who d a =
      (Math.PMFProduct.pmfPi
        (Function.update
          (G.finkProfile (germ.finkPointAt ht) s)
          who (PMF.pure d)) a).toReal := by
  rw [germ.finkProfile_finkPointAt,
    Math.PMFProduct.pmfPi_apply_update_family,
    ENNReal.toReal_mul, ENNReal.toReal_prod, PMF.pure_apply]
  unfold rawPureDeviationProfileWeight
  by_cases had : a who = d
  · rw [if_pos had, if_pos had]
    simp only [ENNReal.toReal_one, one_mul]
    apply Finset.prod_congr rfl
    intro other _
    exact
      (G.bellmanDecodeProfile_apply_toReal
        (germ.solution t ht) s other (a other)).symm
  · rw [if_neg had, if_neg had]
    simp

omit [DecidableEq G.State] in
/-- At a valid positive point, the raw pure-deviation state kernel is the
semantic Fink pure-deviation kernel. -/
theorem rawPureDeviationStateKernelCurve_eq_finkPointAt
    (germ : G.AnalyticBellmanGerm)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (s : G.State) (who : ι) (d : G.Act who)
    (destination : G.State) :
    germ.rawPureDeviationStateKernelCurve t s who d destination =
      (G.finkPureDeviationStateKernel
        (germ.finkPointAt ht) s who d destination).toReal := by
  unfold rawPureDeviationStateKernelCurve
    finkPureDeviationStateKernel
  rw [Math.ProbabilityMassFunction.bind_apply_toReal_eq_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [germ.rawPureDeviationProfileWeight_eq_pmfPi_finkPointAt ht]

omit [DecidableEq G.State] in
/-- The raw stage-gain curve agrees with Fink's semantic stage gain. -/
theorem rawPureDeviationStageGainCurve_eq_finkPointAt
    (germ : G.AnalyticBellmanGerm)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (s : G.State) (who : ι) (d : G.Act who) :
    germ.rawPureDeviationStageGainCurve t s who d =
      G.finkStageGain (germ.finkPointAt ht) s who d := by
  unfold rawPureDeviationStageGainCurve finkStageGain mixedStageEU
  rw [Math.Probability.expect_eq_sum,
    Math.Probability.expect_eq_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro a _
    rw [germ.rawPureDeviationProfileWeight_eq_pmfPi_finkPointAt ht]
  · simpa [finkStageEU, Math.Probability.expect_eq_sum] using
      congrFun (congrFun
        (germ.rawStageCurve_eq_finkStageEU ht) s) who

omit [DecidableEq G.State] in
/-- The raw continuation-gain curve agrees with Fink's semantic
continuation gain against the same fixed payoff vector. -/
theorem rawPureDeviationContinuationGainCurve_eq_finkPointAt
    (germ : G.AnalyticBellmanGerm)
    (W : G.State → Payoff ι)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (s : G.State) (who : ι) (d : G.Act who) :
    germ.rawPureDeviationContinuationGainCurve W t s who d =
      G.finkContinuationGain W (germ.finkPointAt ht) s who d := by
  rw [G.finkContinuationGain_eq_expect_stateKernels]
  unfold rawPureDeviationContinuationGainCurve
  rw [Math.Probability.expect_eq_sum,
    Math.Probability.expect_eq_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro destination _
  rw [germ.rawPureDeviationStateKernelCurve_eq_finkPointAt ht,
    germ.rawStateKernelCurve_eq_finkStateKernel ht]
  ring

/-- At a valid positive parameter, the raw analytic occupation columns are
exactly the semantic baseline-and-pure-deviation occupation columns. -/
theorem rawAnalyticOccupationColumn_eq_finkPointAt
    (germ : G.AnalyticBellmanGerm)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius) :
    germ.rawAnalyticOccupationColumn t =
      stochasticOccupationColumn
        (G.finkStateKernel (germ.finkPointAt ht))
        (fun e : Σ who : ι, G.State × G.Act who =>
          G.finkPureDeviationStateKernel
            (germ.finkPointAt ht) e.2.1 e.1 e.2.2)
        (fun e : Σ who : ι, G.State × G.Act who => e.2.1) := by
  funext index destination
  cases index with
  | inl source =>
      simp only [rawAnalyticOccupationColumn,
        stochasticOccupationColumn, actualOccupationColumn,
        occupationKernel, occupationSource]
      rw [germ.rawStateKernelCurve_eq_finkStateKernel ht]
      rfl
  | inr e =>
      simp only [rawAnalyticOccupationColumn,
        stochasticOccupationColumn, actualOccupationColumn,
        occupationKernel, occupationSource]
      rw [germ.rawPureDeviationStateKernelCurve_eq_finkPointAt ht]
      rfl

/-- Pairing a raw analytic occupation column with a potential is the
ordinary expected potential drift of its actual semantic transition. -/
theorem potential_pair_rawAnalyticOccupationColumn_eq
    (germ : G.AnalyticBellmanGerm)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (potential : G.State → ℝ)
    (index : G.State ⊕ (Σ who : ι, G.State × G.Act who)) :
    (∑ destination,
      potential destination *
        germ.rawAnalyticOccupationColumn t index destination) =
      expect (germ.finkActualOccupationKernelAt ht index) potential -
        potential (finkActualOccupationSource index) := by
  rw [germ.rawAnalyticOccupationColumn_eq_finkPointAt ht]
  simpa [finkActualOccupationKernelAt,
    finkActualOccupationSource, stochasticOccupationColumn] using
    potential_pair_actualOccupationColumn
    (occupationKernel
      (G.finkStateKernel (germ.finkPointAt ht))
      (fun e : Σ who : ι, G.State × G.Act who =>
        G.finkPureDeviationStateKernel
          (germ.finkPointAt ht) e.2.1 e.1 e.2.2))
    (occupationSource
      (fun e : Σ who : ι, G.State × G.Act who => e.2.1))
    potential index

/-- Actual analytic occupation columns retain zero total mass throughout a
small punctured right neighborhood. -/
theorem eventually_sum_rawAnalyticOccupationColumn_eq_zero
    (germ : G.AnalyticBellmanGerm) :
    ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      ∀ index,
        ∑ destination,
          germ.rawAnalyticOccupationColumn t index destination = 0 := by
  have hradius_nhds :
      ∀ᶠ t in nhds (0 : ℝ), t < germ.radius :=
    Iio_mem_nhds germ.radius_pos
  have hradius :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0), t < germ.radius :=
    hradius_nhds.filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hradius] with t htpos htradius
  have ht : t ∈ Ioo (0 : ℝ) germ.radius :=
    ⟨htpos, htradius⟩
  intro index
  cases index with
  | inl source =>
      have hdelta :
          (∑ destination : G.State,
            if destination = source then (1 : ℝ) else 0) = 1 := by
        simp
      have hkernel :
          (∑ destination,
            germ.rawStateKernelCurve t source destination) = 1 := by
        calc
          _ = ∑ destination,
              (G.finkStateKernel
                (germ.finkPointAt ht) source destination).toReal := by
            apply Finset.sum_congr rfl
            intro destination _
            rw [germ.rawStateKernelCurve_eq_finkStateKernel ht]
          _ = 1 := Math.Probability.pmf_toReal_sum_one _
      simp only [rawAnalyticOccupationColumn]
      rw [Finset.sum_sub_distrib, hkernel, hdelta, sub_self]
  | inr e =>
      have hdelta :
          (∑ destination : G.State,
            if destination = e.2.1 then (1 : ℝ) else 0) = 1 := by
        simp
      have hkernel :
          (∑ destination,
            germ.rawPureDeviationStateKernelCurve
              t e.2.1 e.1 e.2.2 destination) = 1 := by
        calc
          _ = ∑ destination,
              (G.finkPureDeviationStateKernel
                (germ.finkPointAt ht)
                e.2.1 e.1 e.2.2 destination).toReal := by
            apply Finset.sum_congr rfl
            intro destination _
            rw [germ.rawPureDeviationStateKernelCurve_eq_finkPointAt ht]
          _ = 1 := Math.Probability.pmf_toReal_sum_one _
      simp only [rawAnalyticOccupationColumn]
      rw [Finset.sum_sub_distrib, hkernel, hdelta, sub_self]

/-- Raw mixing coordinate of one potential supported action. -/
def rawFinkActionCoordinate
    (germ : G.AnalyticBellmanGerm)
    (t : ℝ) (e : Σ who : ι, G.State × G.Act who) : ℝ :=
  germ.assignment t (BellmanVar.mix e.2.1 e.1 e.2.2)

omit [DecidableEq G.State] in
theorem analytic_rawFinkActionCoordinate
    (germ : G.AnalyticBellmanGerm)
    (e : Σ who : ι, G.State × G.Act who) :
    AnalyticAt ℝ (fun t => germ.rawFinkActionCoordinate t e) 0 := by
  exact germ.analytic_coordinate
    (BellmanVar.mix e.2.1 e.1 e.2.2)

omit [DecidableEq G.State] in
/-- One support predicate eventually describes every nonzero decoded action
coordinate of the analytic Bellman germ. -/
theorem exists_eventually_fixed_finkSupport
    (germ : G.AnalyticBellmanGerm) :
    ∃ supported : (Σ who : ι, G.State × G.Act who) → Bool,
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        t ∈ Ioo (0 : ℝ) germ.radius ∧
          ∀ ht : t ∈ Ioo (0 : ℝ) germ.radius,
            ∀ e : Σ who : ι, G.State × G.Act who,
              (supported e = true ↔
                G.finkProfile (germ.finkPointAt ht)
                  e.2.1 e.1 e.2.2 ≠ 0) := by
  classical
  let coordinate :
      (Σ who : ι, G.State × G.Act who) → ℝ → ℝ :=
    fun e t => germ.rawFinkActionCoordinate t e
  have hcoordinate :
      ∀ e, AnalyticAt ℝ (coordinate e) 0 :=
    fun e => germ.analytic_rawFinkActionCoordinate e
  have hvalid :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        t ∈ Ioo (0 : ℝ) germ.radius := by
    have hradius_nhds :
        ∀ᶠ t in nhds (0 : ℝ), t < germ.radius :=
      Iio_mem_nhds germ.radius_pos
    have hradius :
        ∀ᶠ t in nhdsWithin 0 (Ioi 0), t < germ.radius :=
      hradius_nhds.filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hradius] with t ht htradius
    exact ⟨ht, htradius⟩
  have hnonneg :
      ∀ e, ∀ᶠ t in nhdsWithin 0 (Ioi 0), 0 ≤ coordinate e t := by
    intro e
    filter_upwards [hvalid] with t ht
    rcases e with ⟨who, s, d⟩
    change 0 ≤ germ.assignment t (BellmanVar.mix s who d)
    rw [← G.bellmanDecodeProfile_apply_toReal
      (germ.solution t ht) s who d]
    exact ENNReal.toReal_nonneg
  obtain ⟨zeroCoordinate, hzeroCoordinate⟩ :=
    finite_analytic_nonnegative_family_eventually_active_set
      coordinate hcoordinate hnonneg
  let supported :
      (Σ who : ι, G.State × G.Act who) → Bool :=
    fun e => decide (¬ zeroCoordinate e)
  refine ⟨supported, ?_⟩
  filter_upwards [hvalid, hzeroCoordinate] with t ht hzero
  refine ⟨ht, fun ht' e => ?_⟩
  have hactive :
      coordinate e t ≠ 0 ↔ ¬ zeroCoordinate e :=
    not_congr (hzero e).1
  have hreal :
      (G.finkProfile (germ.finkPointAt ht') e.2.1 e.1 e.2.2).toReal =
        coordinate e t := by
    rw [germ.finkProfile_finkPointAt]
    exact G.bellmanDecodeProfile_apply_toReal
      (germ.solution t ht') e.2.1 e.1 e.2.2
  have hpmf :
      G.finkProfile (germ.finkPointAt ht') e.2.1 e.1 e.2.2 ≠ 0 ↔
        coordinate e t ≠ 0 := by
    rw [← hreal]
    constructor
    · intro hne
      exact ENNReal.toReal_ne_zero.mpr
        ⟨hne, PMF.apply_ne_top _ _⟩
    · intro hne
      exact (ENNReal.toReal_ne_zero.mp hne).1
  simpa only [supported, decide_eq_true_eq] using
    hactive.symm.trans hpmf.symm

/-- Analytic coordinate matrix of the Fink obstruction system after its
finite action support has stabilized. -/
def rawFinkObstructionBalance
    (germ : G.AnalyticBellmanGerm)
    (supported : (Σ who : ι, G.State × G.Act who) → Bool) :
    ℝ → Matrix (FinkObstructionRow G) (FinkObstructionColumn G) ℝ :=
  fun t row column =>
    match row, column with
    | (who, destination), Sum.inl (s, sourceWho) =>
        if sourceWho = who then
          germ.rawStateKernelCurve t s destination -
            if s = destination then 1 else 0
        else 0
    | (who, destination), Sum.inr e =>
        if e.1 = who then
          if supported e then
            germ.rawPureDeviationStateKernelCurve
                t e.2.1 e.1 e.2.2 destination -
              germ.rawStateKernelCurve t e.2.1 destination
          else 0
        else 0

/-- Analytic tangent target row after the action support has stabilized. -/
def rawFinkObstructionMass
    (germ : G.AnalyticBellmanGerm)
    (supported : (Σ who : ι, G.State × G.Act who) → Bool)
    (H K : G.State → Payoff ι) :
    ℝ → FinkObstructionColumn G → ℝ :=
  fun t column =>
    match column with
    | Sum.inl _ => 0
    | Sum.inr e =>
        if supported e then
          germ.rawPureDeviationStageGainCurve
              t e.2.1 e.1 e.2.2 +
            germ.rawPureDeviationContinuationGainCurve
              (H - K) t e.2.1 e.1 e.2.2
        else 0

theorem analytic_rawFinkObstructionBalance
    (germ : G.AnalyticBellmanGerm)
    (supported : (Σ who : ι, G.State × G.Act who) → Bool) :
    ∀ row column,
      AnalyticAt ℝ
        (fun t => germ.rawFinkObstructionBalance supported t row column) 0 := by
  rintro ⟨who, destination⟩ column
  cases column with
  | inl residual =>
      rcases residual with ⟨s, sourceWho⟩
      by_cases hwho : sourceWho = who
      · simp only [rawFinkObstructionBalance, hwho, if_true]
        exact
          (((analyticAt_pi_iff.mp
            ((analyticAt_pi_iff.mp
              germ.analytic_rawStateKernelCurve) s)) destination).sub
            analyticAt_const)
      · simpa only [rawFinkObstructionBalance, hwho, if_false] using
          (analyticAt_const :
            AnalyticAt ℝ (fun _ : ℝ => (0 : ℝ)) 0)
  | inr e =>
      by_cases hwho : e.1 = who
      · by_cases hsupported : supported e
        · simp only [rawFinkObstructionBalance, hwho, hsupported,
            if_true]
          exact
            (((analyticAt_pi_iff.mp
              ((analyticAt_pi_iff.mp
                ((analyticAt_pi_iff.mp
                  ((analyticAt_pi_iff.mp
                    germ.analytic_rawPureDeviationStateKernelCurve)
                    e.2.1)) e.1)) e.2.2)) destination).sub
              ((analyticAt_pi_iff.mp
                ((analyticAt_pi_iff.mp
                  germ.analytic_rawStateKernelCurve)
                  e.2.1)) destination))
        · simpa only [rawFinkObstructionBalance, hwho, hsupported,
            if_true, if_false, Bool.false_eq_true] using
            (analyticAt_const :
              AnalyticAt ℝ (fun _ : ℝ => (0 : ℝ)) 0)
      · simpa only [rawFinkObstructionBalance, hwho, if_false] using
          (analyticAt_const :
            AnalyticAt ℝ (fun _ : ℝ => (0 : ℝ)) 0)

omit [DecidableEq G.State] in
theorem analytic_rawFinkObstructionMass
    (germ : G.AnalyticBellmanGerm)
    (supported : (Σ who : ι, G.State × G.Act who) → Bool)
    (H K : G.State → Payoff ι) :
    ∀ column,
      AnalyticAt ℝ
        (fun t => germ.rawFinkObstructionMass supported H K t column) 0 := by
  intro column
  cases column with
  | inl residual =>
      simpa only [rawFinkObstructionMass] using
        (analyticAt_const :
          AnalyticAt ℝ (fun _ : ℝ => (0 : ℝ)) 0)
  | inr e =>
      by_cases hsupported : supported e
      · simp only [rawFinkObstructionMass, hsupported, if_true]
        exact
          (((analyticAt_pi_iff.mp
            ((analyticAt_pi_iff.mp
              ((analyticAt_pi_iff.mp
                germ.analytic_rawPureDeviationStageGainCurve)
                e.2.1)) e.1)) e.2.2).add
            ((analyticAt_pi_iff.mp
              ((analyticAt_pi_iff.mp
                ((analyticAt_pi_iff.mp
                  (germ.analytic_rawPureDeviationContinuationGainCurve
                    (H - K))) e.2.1)) e.1)) e.2.2))
      · simpa only [rawFinkObstructionMass, hsupported, if_false,
          Bool.false_eq_true] using
          (analyticAt_const :
            AnalyticAt ℝ (fun _ : ℝ => (0 : ℝ)) 0)

/-- When the frozen support matches the positive-parameter profile, the raw
analytic balance matrix is the semantic Fink balance matrix. -/
theorem rawFinkObstructionBalance_eq_finkPointAt
    (germ : G.AnalyticBellmanGerm)
    (supported : (Σ who : ι, G.State × G.Act who) → Bool)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (hsupported :
      ∀ e : Σ who : ι, G.State × G.Act who,
        supported e = true ↔
          G.finkProfile (germ.finkPointAt ht)
            e.2.1 e.1 e.2.2 ≠ 0) :
    germ.rawFinkObstructionBalance supported t =
      G.finkObstructionBalance (germ.finkPointAt ht) := by
  funext row column
  rcases row with ⟨who, destination⟩
  cases column with
  | inl residual =>
      rcases residual with ⟨s, sourceWho⟩
      by_cases hwho : sourceWho = who
      · simp only [rawFinkObstructionBalance,
          finkObstructionBalance, hwho, if_true]
        rw [germ.rawStateKernelCurve_eq_finkStateKernel ht]
      · simp [rawFinkObstructionBalance,
          finkObstructionBalance, hwho]
  | inr e =>
      by_cases hwho : e.1 = who
      · by_cases hprofile :
          G.finkProfile (germ.finkPointAt ht)
            e.2.1 e.1 e.2.2 ≠ 0
        · have hsupported_true : supported e = true :=
            (hsupported e).2 hprofile
          simp only [rawFinkObstructionBalance, hwho,
            hsupported_true, if_true]
          rw [germ.rawPureDeviationStateKernelCurve_eq_finkPointAt ht,
            germ.rawStateKernelCurve_eq_finkStateKernel ht]
          rw [finkObstructionBalance, if_pos hwho,
            if_pos hprofile]
        · have hsupported_false : supported e = false :=
            Bool.eq_false_of_not_eq_true fun hs =>
              hprofile ((hsupported e).1 hs)
          simp only [rawFinkObstructionBalance, hwho,
            hsupported_false, if_true, Bool.false_eq_true,
            if_false]
          rw [finkObstructionBalance, if_pos hwho,
            if_neg hprofile]
      · simp [rawFinkObstructionBalance,
          finkObstructionBalance, hwho]

omit [DecidableEq G.State] in
/-- Under the same frozen support, the raw analytic target row is the
semantic Fink target functional. -/
theorem rawFinkObstructionMass_eq_finkPointAt
    (germ : G.AnalyticBellmanGerm)
    (supported : (Σ who : ι, G.State × G.Act who) → Bool)
    (H K : G.State → Payoff ι)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (hsupported :
      ∀ e : Σ who : ι, G.State × G.Act who,
        supported e = true ↔
          G.finkProfile (germ.finkPointAt ht)
            e.2.1 e.1 e.2.2 ≠ 0) :
    germ.rawFinkObstructionMass supported H K t =
      G.finkObstructionMass (germ.finkPointAt ht) H K := by
  funext column
  cases column with
  | inl residual =>
      simp [rawFinkObstructionMass, finkObstructionMass]
  | inr e =>
      by_cases hprofile :
          G.finkProfile (germ.finkPointAt ht)
            e.2.1 e.1 e.2.2 ≠ 0
      · have hsupported_true : supported e = true :=
          (hsupported e).2 hprofile
        simp only [rawFinkObstructionMass,
          hsupported_true, if_true]
        rw [
          germ.rawPureDeviationStageGainCurve_eq_finkPointAt ht,
          germ.rawPureDeviationContinuationGainCurve_eq_finkPointAt
            (H - K) ht]
        rw [finkObstructionMass, if_pos hprofile]
      · have hsupported_false : supported e = false :=
          Bool.eq_false_of_not_eq_true fun hs =>
            hprofile ((hsupported e).1 hs)
        simp only [rawFinkObstructionMass,
          hsupported_false, Bool.false_eq_true, if_false]
        rw [finkObstructionMass, if_neg hprofile]

/-- On the stabilized support, the analytic harmonic-adjustment system is
the transpose of the raw obstruction balance with the raw target row as its
right-hand side. -/
theorem exists_finkHarmonicAdjustment_iff_rawTranspose_mulVec
    (germ : G.AnalyticBellmanGerm)
    (supported : (Σ who : ι, G.State × G.Act who) → Bool)
    (H K : G.State → Payoff ι)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (hsupported :
      ∀ e : Σ who : ι, G.State × G.Act who,
        supported e = true ↔
          G.finkProfile (germ.finkPointAt ht)
            e.2.1 e.1 e.2.2 ≠ 0) :
    (∃ A : G.State → Payoff ι,
      G.finkContinuationResidualVector A
          (germ.finkPointAt ht) = 0 ∧
        ∀ s who (d : G.Act who),
          G.finkProfile (germ.finkPointAt ht) s who d ≠ 0 →
            G.finkContinuationGain A
                (germ.finkPointAt ht) s who d =
              G.finkStageGain
                  (germ.finkPointAt ht) s who d +
                G.finkContinuationGain (H - K)
                  (germ.finkPointAt ht) s who d) ↔
      ∃ a : FinkObstructionRow G → ℝ,
        Matrix.mulVec
            (germ.rawFinkObstructionBalance
              supported t).transpose a =
          germ.rawFinkObstructionMass supported H K t := by
  rw [germ.rawFinkObstructionBalance_eq_finkPointAt
      supported ht hsupported,
    germ.rawFinkObstructionMass_eq_finkPointAt
      supported H K ht hsupported]
  exact G.exists_finkHarmonicAdjustment_iff_transpose_mulVec
    (germ.finkPointAt ht) H K

/-- If the Fink alternative stays in its obstruction branch on a punctured
right neighborhood, one fixed oriented Cramer support and one common power
produce an analytic coefficient vector through the endpoint.

This is the parameter-coherence bridge. It does not assert that the
obstruction branch occurs; that decision belongs to the Bellman hierarchy.
-/
theorem exists_analytic_scaled_eventual_finkObstructionCertificate_withSupport
    (germ : G.AnalyticBellmanGerm)
    (H K : G.State → Payoff ι)
    (hflow :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        ∀ ht : t ∈ Ioo (0 : ℝ) germ.radius,
          Nonempty
            (G.NormalizedFinkSupportTangentObstructionFlow
              (germ.finkPointAt ht) H K)) :
    ∃ (supported :
          (Σ who : ι, G.State × G.Act who) → Bool)
        (support : Finset (FinkObstructionColumn G × Bool))
        (poleOrder : ℕ)
        (scaled : ℝ → FinkObstructionColumn G × Bool → ℝ),
      AnalyticAt ℝ scaled 0 ∧
        ∀ᶠ t in nhdsWithin 0 (Ioi 0),
          t ∈ Ioo (0 : ℝ) germ.radius ∧
            (∀ ht : t ∈ Ioo (0 : ℝ) germ.radius,
              ∀ e : Σ who : ι, G.State × G.Act who,
                supported e = true ↔
                  G.finkProfile (germ.finkPointAt ht)
                    e.2.1 e.1 e.2.2 ≠ 0) ∧
            (t ^ poleOrder •
                supportCramerVector
                  (normalizedFarkasMatrix
                    (orientedFarkasBalance
                      (germ.rawFinkObstructionBalance supported t))
                    (orientedFarkasMass
                      (germ.rawFinkObstructionMass supported H K t)))
                  normalizedFarkasRhs support =
              scaled t) ∧
            supportCramerVector
                (normalizedFarkasMatrix
                  (orientedFarkasBalance
                    (germ.rawFinkObstructionBalance supported t))
                  (orientedFarkasMass
                    (germ.rawFinkObstructionMass supported H K t)))
                normalizedFarkasRhs support ∈
              normalizedFarkasCertificateSet
                (orientedFarkasBalance
                  (germ.rawFinkObstructionBalance supported t))
                (orientedFarkasMass
                  (germ.rawFinkObstructionMass supported H K t)) := by
  classical
  obtain ⟨supported, hsupport⟩ :=
    germ.exists_eventually_fixed_finkSupport
  let balance :
      ℝ → Matrix (FinkObstructionRow G)
        (FinkObstructionColumn G × Bool) ℝ :=
    fun t => orientedFarkasBalance
      (germ.rawFinkObstructionBalance supported t)
  let mass : ℝ → FinkObstructionColumn G × Bool → ℝ :=
    fun t => orientedFarkasMass
      (germ.rawFinkObstructionMass supported H K t)
  have hbalance :
      ∀ row column, AnalyticAt ℝ (fun t => balance t row column) 0 := by
    intro row column
    rcases column with ⟨column, positive⟩
    cases positive
    · simp only [balance, orientedFarkasBalance,
        farkasOrientation_false, neg_one_mul]
      exact (germ.analytic_rawFinkObstructionBalance
        supported row column).neg
    · simp only [balance, orientedFarkasBalance,
        farkasOrientation_true, one_mul]
      exact germ.analytic_rawFinkObstructionBalance
        supported row column
  have hmass :
      ∀ column, AnalyticAt ℝ (fun t => mass t column) 0 := by
    intro column
    rcases column with ⟨column, positive⟩
    cases positive
    · simp only [mass, orientedFarkasMass,
        farkasOrientation_false, neg_one_mul]
      exact (germ.analytic_rawFinkObstructionMass
        supported H K column).neg
    · simp only [mass, orientedFarkasMass,
        farkasOrientation_true, one_mul]
      exact germ.analytic_rawFinkObstructionMass
        supported H K column
  have hfeasible :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        (normalizedFarkasCertificateSet
          (balance t) (mass t)).Nonempty := by
    filter_upwards [hsupport, hflow] with t hsupport_t hflow_t
    obtain ⟨ht, hsupport_at⟩ := hsupport_t
    obtain ⟨F⟩ := hflow_t ht
    refine ⟨signedFarkasToOriented F.coefficient, ?_⟩
    have hcertificate := F.orientedFarkasCertificate
    rw [← germ.rawFinkObstructionBalance_eq_finkPointAt
          supported ht (hsupport_at ht),
        ← germ.rawFinkObstructionMass_eq_finkPointAt
          supported H K ht (hsupport_at ht)] at hcertificate
    simpa [balance, mass] using hcertificate
  obtain ⟨support, poleOrder, scaled, hscaled, hcertificate⟩ :=
    exists_analytic_scaled_eventual_feasible_normalizedFarkasCertificate
      balance mass hbalance hmass hfeasible
  refine ⟨supported, support, poleOrder, scaled, hscaled, ?_⟩
  filter_upwards [hsupport, hcertificate] with t hsupport_t hcertificate_t
  exact ⟨hsupport_t.1, hsupport_t.2,
    by simpa [balance, mass] using hcertificate_t.1,
    by simpa [balance, mass] using hcertificate_t.2⟩

/-- Compatibility wrapper for the original analytic Fink certificate API.

The stronger `_withSupport` theorem also retains the exact support witness
needed by downstream positivity repairs; this projection deliberately
forgets only that additional witness. -/
theorem exists_analytic_scaled_eventual_finkObstructionCertificate
    (germ : G.AnalyticBellmanGerm)
    (H K : G.State → Payoff ι)
    (hflow :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        ∀ ht : t ∈ Ioo (0 : ℝ) germ.radius,
          Nonempty
            (G.NormalizedFinkSupportTangentObstructionFlow
              (germ.finkPointAt ht) H K)) :
    ∃ (supported :
          (Σ who : ι, G.State × G.Act who) → Bool)
        (support : Finset (FinkObstructionColumn G × Bool))
        (poleOrder : ℕ)
        (scaled : ℝ → FinkObstructionColumn G × Bool → ℝ),
      AnalyticAt ℝ scaled 0 ∧
        ∀ᶠ t in nhdsWithin 0 (Ioi 0),
          t ∈ Ioo (0 : ℝ) germ.radius ∧
            (t ^ poleOrder •
                supportCramerVector
                  (normalizedFarkasMatrix
                    (orientedFarkasBalance
                      (germ.rawFinkObstructionBalance supported t))
                    (orientedFarkasMass
                      (germ.rawFinkObstructionMass supported H K t)))
                  normalizedFarkasRhs support =
              scaled t) ∧
            supportCramerVector
                (normalizedFarkasMatrix
                  (orientedFarkasBalance
                    (germ.rawFinkObstructionBalance supported t))
                  (orientedFarkasMass
                    (germ.rawFinkObstructionMass supported H K t)))
                normalizedFarkasRhs support ∈
              normalizedFarkasCertificateSet
                (orientedFarkasBalance
                  (germ.rawFinkObstructionBalance supported t))
                (orientedFarkasMass
                  (germ.rawFinkObstructionMass supported H K t)) := by
  obtain ⟨supported, support, poleOrder, scaled,
      hscaled, hcertificate⟩ :=
    germ.exists_analytic_scaled_eventual_finkObstructionCertificate_withSupport
      H K hflow
  refine ⟨supported, support, poleOrder, scaled, hscaled, ?_⟩
  filter_upwards [hcertificate] with t ht
  exact ⟨ht.1, ht.2.2.1, ht.2.2.2⟩

/-- Reconstruct the doubled nonnegative Cramer certificate as an ordinary
signed analytic obstruction flow.

The common pole-clearing factor changes the normalized target mass from one
to exactly `t ^ poleOrder`; the homogeneous balance remains zero. -/
theorem exists_analytic_scaled_signed_eventual_finkObstructionFlow_withSupport
    (germ : G.AnalyticBellmanGerm)
    (H K : G.State → Payoff ι)
    (hflow :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        ∀ ht : t ∈ Ioo (0 : ℝ) germ.radius,
          Nonempty
            (G.NormalizedFinkSupportTangentObstructionFlow
              (germ.finkPointAt ht) H K)) :
    ∃ (supported :
          (Σ who : ι, G.State × G.Act who) → Bool)
        (poleOrder : ℕ)
        (signed : ℝ → FinkObstructionColumn G → ℝ),
      AnalyticAt ℝ signed 0 ∧
        ∀ᶠ t in nhdsWithin 0 (Ioi 0),
          t ∈ Ioo (0 : ℝ) germ.radius ∧
            (∀ ht : t ∈ Ioo (0 : ℝ) germ.radius,
              ∀ e : Σ who : ι, G.State × G.Act who,
                supported e = true ↔
                  G.finkProfile (germ.finkPointAt ht)
                    e.2.1 e.1 e.2.2 ≠ 0) ∧
            Matrix.mulVec
                (germ.rawFinkObstructionBalance supported t)
                (signed t) = 0 ∧
            (∑ j,
                germ.rawFinkObstructionMass supported H K t j *
                  signed t j) =
              t ^ poleOrder := by
  classical
  obtain
      ⟨supported, support, poleOrder, scaled,
        hscaled, hcertificate⟩ :=
    germ.exists_analytic_scaled_eventual_finkObstructionCertificate_withSupport
      H K hflow
  let signed : ℝ → FinkObstructionColumn G → ℝ := fun t =>
    orientedFarkasToSigned (scaled t)
  have hsigned : AnalyticAt ℝ signed 0 := by
    rw [analyticAt_pi_iff]
    intro column
    exact
      ((analyticAt_pi_iff.mp hscaled (column, true)).sub
        (analyticAt_pi_iff.mp hscaled (column, false)))
  refine ⟨supported, poleOrder, signed, hsigned, ?_⟩
  filter_upwards [hcertificate] with t ht
  let z :=
    supportCramerVector
      (normalizedFarkasMatrix
        (orientedFarkasBalance
          (germ.rawFinkObstructionBalance supported t))
        (orientedFarkasMass
          (germ.rawFinkObstructionMass supported H K t)))
      normalizedFarkasRhs support
  have hz :
      Matrix.mulVec
          (germ.rawFinkObstructionBalance supported t)
          (orientedFarkasToSigned z) = 0 ∧
        (∑ j,
            germ.rawFinkObstructionMass supported H K t j *
              orientedFarkasToSigned z j) = 1 :=
    normalizedFarkasCertificateSet_oriented_toSigned
      (germ.rawFinkObstructionBalance supported t)
      (germ.rawFinkObstructionMass supported H K t)
      ht.2.2.2
  have hsigned_eq :
      signed t =
        t ^ poleOrder • orientedFarkasToSigned z := by
    funext column
    have hcoordinate :=
      congrFun ht.2.2.1 (column, true)
    have hcoordinate_neg :=
      congrFun ht.2.2.1 (column, false)
    change
      scaled t (column, true) -
          scaled t (column, false) =
        t ^ poleOrder *
          (z (column, true) - z (column, false))
    change
      t ^ poleOrder * z (column, true) =
        scaled t (column, true) at hcoordinate
    change
      t ^ poleOrder * z (column, false) =
        scaled t (column, false) at hcoordinate_neg
    rw [← hcoordinate, ← hcoordinate_neg]
    ring
  refine ⟨ht.1, ht.2.1, ?_, ?_⟩
  · rw [hsigned_eq, Matrix.mulVec_smul, hz.1, smul_zero]
  · rw [hsigned_eq]
    simp only [Pi.smul_apply, smul_eq_mul]
    calc
      (∑ j,
          germ.rawFinkObstructionMass supported H K t j *
            (t ^ poleOrder * orientedFarkasToSigned z j)) =
          t ^ poleOrder *
            ∑ j,
              germ.rawFinkObstructionMass supported H K t j *
                orientedFarkasToSigned z j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = t ^ poleOrder := by rw [hz.2, mul_one]

/-- Compatibility wrapper for the original signed analytic-flow API.

Use `_withSupport` when downstream constructions must know that the frozen
Boolean support is exactly the decoded positive-parameter support. -/
theorem exists_analytic_scaled_signed_eventual_finkObstructionFlow
    (germ : G.AnalyticBellmanGerm)
    (H K : G.State → Payoff ι)
    (hflow :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        ∀ ht : t ∈ Ioo (0 : ℝ) germ.radius,
          Nonempty
            (G.NormalizedFinkSupportTangentObstructionFlow
              (germ.finkPointAt ht) H K)) :
    ∃ (supported :
          (Σ who : ι, G.State × G.Act who) → Bool)
        (poleOrder : ℕ)
        (signed : ℝ → FinkObstructionColumn G → ℝ),
      AnalyticAt ℝ signed 0 ∧
        ∀ᶠ t in nhdsWithin 0 (Ioi 0),
          t ∈ Ioo (0 : ℝ) germ.radius ∧
            Matrix.mulVec
                (germ.rawFinkObstructionBalance supported t)
                (signed t) = 0 ∧
            (∑ j,
                germ.rawFinkObstructionMass supported H K t j *
                  signed t j) =
              t ^ poleOrder := by
  obtain ⟨supported, poleOrder, signed, hsigned, hflow⟩ :=
    germ.exists_analytic_scaled_signed_eventual_finkObstructionFlow_withSupport
      H K hflow
  refine ⟨supported, poleOrder, signed, hsigned, ?_⟩
  filter_upwards [hflow] with t ht
  exact ⟨ht.1, ht.2.2.1, ht.2.2.2⟩

/-- A fixed pure deviation extracted from an analytic Fink obstruction flow.

The signed obstruction is retained so downstream arguments can use its exact
flow balance.  The selected deviation carries a positive power-law share of
the normalized obstruction mass.  Its actual transition is either
indistinguishable from the baseline as an analytic right germ, or one fixed
destination coordinate has a positive oriented power-law drift. -/
structure AnalyticOrientedFinkObstructionResponse
    (germ : G.AnalyticBellmanGerm)
    (H K : G.State → Payoff ι) where
  supported :
    (Σ who : ι, G.State × G.Act who) → Bool
  poleOrder : ℕ
  signed : ℝ → FinkObstructionColumn G → ℝ
  analytic_signed : AnalyticAt ℝ signed 0
  eventual_flow :
    ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      t ∈ Ioo (0 : ℝ) germ.radius ∧
        Matrix.mulVec
            (germ.rawFinkObstructionBalance supported t)
            (signed t) = 0 ∧
        (∑ j,
            germ.rawFinkObstructionMass supported H K t j *
              signed t j) =
          t ^ poleOrder
  response : Σ who : ι, G.State × G.Act who
  positive : Bool
  weightOrder : ℕ
  kappa : ℝ
  kappa_pos : 0 < kappa
  eventual_charge :
    ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      (Fintype.card
          (Σ who : ι, G.State × G.Act who) : ℝ)⁻¹ *
            t ^ poleOrder ≤
          signed t (Sum.inr response) *
            germ.rawFinkObstructionMass supported H K t
              (Sum.inr response) ∧
        kappa * t ^ weightOrder ≤
          responseOrientation positive *
            signed t (Sum.inr response) ∧
        kappa * t ^ weightOrder ≤
          responseOrientation positive *
            germ.rawFinkObstructionMass supported H K t
              (Sum.inr response)
  transition :
    (∀ᶠ t in nhdsWithin 0 (Ioi 0),
      ∀ destination,
        germ.rawPureDeviationStateKernelCurve
            t response.2.1 response.1 response.2.2 destination =
          germ.rawStateKernelCurve t response.2.1 destination) ∨
      ∃ destination n c, 0 < c ∧
        ∀ᶠ t in nhdsWithin 0 (Ioi 0),
          c * t ^ n ≤
              responseOrientation positive *
                (germ.rawPureDeviationStateKernelCurve
                    t response.2.1 response.1 response.2.2 destination -
                  germ.rawStateKernelCurve
                    t response.2.1 destination) ∧
            0 <
              responseOrientation positive *
                (germ.rawPureDeviationStateKernelCurve
                    t response.2.1 response.1 response.2.2 destination -
                  germ.rawStateKernelCurve
                    t response.2.1 destination)

/-- Extract one fixed, operationally oriented pure deviation from every
eventual analytic Fink obstruction.

The orientation changes the sign of the statistical monitor only.  The
forward kernel in the conclusion is always the transition induced by the
selected action itself. -/
theorem exists_analyticOrientedFinkObstructionResponse
    [Nonempty G.State] [Nonempty ι] [∀ i, Nonempty (G.Act i)]
    (germ : G.AnalyticBellmanGerm)
    (H K : G.State → Payoff ι)
    (hflow :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        ∀ ht : t ∈ Ioo (0 : ℝ) germ.radius,
          Nonempty
            (G.NormalizedFinkSupportTangentObstructionFlow
              (germ.finkPointAt ht) H K)) :
    Nonempty (germ.AnalyticOrientedFinkObstructionResponse H K) := by
  classical
  let E := Σ who : ι, G.State × G.Act who
  letI : Nonempty E := by
    let who : ι := Classical.choice (inferInstance : Nonempty ι)
    let s : G.State :=
      Classical.choice (inferInstance : Nonempty G.State)
    let d : G.Act who :=
      Classical.choice (inferInstance : Nonempty (G.Act who))
    exact ⟨⟨who, s, d⟩⟩
  let baseline : G.State → ℝ → G.State → ℝ :=
    fun source t destination =>
      germ.rawStateKernelCurve t source destination
  let source : E → G.State := fun e => e.2.1
  let forward : E → ℝ → G.State → ℝ :=
    fun e t destination =>
      germ.rawPureDeviationStateKernelCurve
        t e.2.1 e.1 e.2.2 destination
  obtain ⟨supported, poleOrder, signed, hsigned, hsignedFlow⟩ :=
    germ.exists_analytic_scaled_signed_eventual_finkObstructionFlow
      H K hflow
  let weight : E → ℝ → ℝ := fun e t => signed t (Sum.inr e)
  let charge : E → ℝ → ℝ := fun e t =>
    germ.rawFinkObstructionMass supported H K t (Sum.inr e)
  have hbaseline :
      ∀ s destination,
        AnalyticAt ℝ (fun t => baseline s t destination) 0 := by
    intro s destination
    exact
      (analyticAt_pi_iff.mp
        (analyticAt_pi_iff.mp
          germ.analytic_rawStateKernelCurve s) destination)
  have hforward :
      ∀ e destination,
        AnalyticAt ℝ (fun t => forward e t destination) 0 := by
    intro e destination
    exact
      (analyticAt_pi_iff.mp
        (analyticAt_pi_iff.mp
          (analyticAt_pi_iff.mp
            (analyticAt_pi_iff.mp
              germ.analytic_rawPureDeviationStateKernelCurve e.2.1)
            e.1) e.2.2) destination)
  have hmass :
      ∀ e,
        ∀ᶠ t in nhdsWithin 0 (Ioi 0),
          ∑ destination, forward e t destination =
            ∑ destination, baseline (source e) t destination := by
    intro e
    filter_upwards [Ioo_mem_nhdsGT germ.radius_pos] with t ht
    calc
      (∑ destination, forward e t destination) =
          ∑ destination,
            (G.finkPureDeviationStateKernel
              (germ.finkPointAt ht) e.2.1 e.1 e.2.2 destination).toReal := by
        apply Finset.sum_congr rfl
        intro destination _
        exact
          germ.rawPureDeviationStateKernelCurve_eq_finkPointAt
            ht e.2.1 e.1 e.2.2 destination
      _ = 1 :=
        Math.Probability.pmf_toReal_sum_one
          (G.finkPureDeviationStateKernel
            (germ.finkPointAt ht) e.2.1 e.1 e.2.2)
      _ =
          ∑ destination,
            (G.finkStateKernel
              (germ.finkPointAt ht) e.2.1 destination).toReal :=
        (Math.Probability.pmf_toReal_sum_one
          (G.finkStateKernel
            (germ.finkPointAt ht) e.2.1)).symm
      _ = ∑ destination, baseline (source e) t destination := by
        apply Finset.sum_congr rfl
        intro destination _
        exact
          (germ.rawStateKernelCurve_eq_finkStateKernel
            ht e.2.1 destination).symm
  have hweight : ∀ e, AnalyticAt ℝ (weight e) 0 := by
    intro e
    exact analyticAt_pi_iff.mp hsigned (Sum.inr e)
  have hcharge : ∀ e, AnalyticAt ℝ (charge e) 0 := by
    intro e
    exact germ.analytic_rawFinkObstructionMass
      supported H K (Sum.inr e)
  have htotal :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        (1 : ℝ) * t ^ poleOrder ≤
          ∑ e, weight e t * charge e t := by
    filter_upwards [hsignedFlow] with t ht
    have hmass_eq := ht.2.2
    rw [Fintype.sum_sum_type] at hmass_eq
    have haction :
        (∑ e,
            germ.rawFinkObstructionMass supported H K t (Sum.inr e) *
              signed t (Sum.inr e)) =
          t ^ poleOrder := by
      simpa only [rawFinkObstructionMass, zero_mul,
        Finset.sum_const_zero, zero_add] using hmass_eq
    rw [one_mul]
    apply le_of_eq
    calc
      t ^ poleOrder =
          ∑ e,
            germ.rawFinkObstructionMass supported H K t (Sum.inr e) *
              signed t (Sum.inr e) :=
        haction.symm
      _ = ∑ e, weight e t * charge e t := by
        apply Finset.sum_congr rfl
        intro e _
        simp only [weight, charge]
        ring
  obtain ⟨e, positive, weightOrder, kappa, hkappa,
      hevidence, htransition⟩ :=
    exists_fixed_oriented_analytic_stochastic_response_curve
      baseline source forward weight charge
      hbaseline hforward hmass hweight hcharge
      (C := (1 : ℝ)) (K := poleOrder) (by norm_num) htotal
  exact ⟨{
    supported := supported
    poleOrder := poleOrder
    signed := signed
    analytic_signed := hsigned
    eventual_flow := hsignedFlow
    response := e
    positive := positive
    weightOrder := weightOrder
    kappa := kappa
    kappa_pos := hkappa
    eventual_charge := by
      simpa only [weight, charge, one_mul] using hevidence
    transition := by
      simpa only [baseline, source, forward] using htransition }⟩

namespace AnalyticOrientedFinkObstructionResponse

/-- The selected response belongs to the stabilized support. Otherwise its
target charge would vanish identically, contradicting the positive
power-law lower bound. -/
theorem response_supported
    {germ : G.AnalyticBellmanGerm}
    {H K : G.State → Payoff ι}
    (C : AnalyticOrientedFinkObstructionResponse germ H K) :
    C.supported C.response = true := by
  by_contra hunsupported
  have hfalse : C.supported C.response = false :=
    Bool.eq_false_of_not_eq_true hunsupported
  obtain ⟨t, hevidence, ht⟩ :=
    (C.eventual_charge.and self_mem_nhdsWithin).exists
  have hlower_pos :
      0 < C.kappa * t ^ C.weightOrder :=
    mul_pos C.kappa_pos (pow_pos ht C.weightOrder)
  have hmass_zero :
      germ.rawFinkObstructionMass C.supported H K t
          (Sum.inr C.response) = 0 := by
    simp [rawFinkObstructionMass, hfalse]
  simp only [hmass_zero, mul_zero] at hevidence
  exact (not_le_of_gt hlower_pos) hevidence.2.2

/-- Correct decomposition of the selected obstruction charge.

The positive total Bellman charge may be carried by the stage term even
when the action changes the transition law. Therefore the stage branch does
not assume transition invisibility. In the continuation branch the whole
transition-value pairing, rather than an unrelated coordinate contrast, is
proved positive with a power-law margin. -/
theorem stageCharge_or_continuationCharge
    {germ : G.AnalyticBellmanGerm}
    {H K : G.State → Payoff ι}
    (C : AnalyticOrientedFinkObstructionResponse germ H K) :
    (∀ᶠ t in nhdsWithin 0 (Ioi 0),
      (C.kappa / 2) * t ^ C.weightOrder ≤
        responseOrientation C.positive *
          germ.rawPureDeviationStageGainCurve
            t C.response.2.1 C.response.1 C.response.2.2) ∨
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        (C.kappa / 2) * t ^ C.weightOrder ≤
          responseOrientation C.positive *
            germ.rawPureDeviationContinuationGainCurve
              (H - K) t C.response.2.1
                C.response.1 C.response.2.2 := by
  let stage : ℝ → ℝ := fun t =>
    responseOrientation C.positive *
      germ.rawPureDeviationStageGainCurve
        t C.response.2.1 C.response.1 C.response.2.2
  let continuation : ℝ → ℝ := fun t =>
    responseOrientation C.positive *
      germ.rawPureDeviationContinuationGainCurve
        (H - K) t C.response.2.1 C.response.1 C.response.2.2
  have hstage : AnalyticAt ℝ stage 0 := by
    exact analyticAt_const.mul
      (analyticAt_pi_iff.mp
        (analyticAt_pi_iff.mp
          (analyticAt_pi_iff.mp
            germ.analytic_rawPureDeviationStageGainCurve
            C.response.2.1) C.response.1) C.response.2.2)
  have hcontinuation : AnalyticAt ℝ continuation 0 := by
    exact analyticAt_const.mul
      (analyticAt_pi_iff.mp
        (analyticAt_pi_iff.mp
          (analyticAt_pi_iff.mp
            (germ.analytic_rawPureDeviationContinuationGainCurve
              (H - K)) C.response.2.1) C.response.1)
        C.response.2.2)
  have htotal :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        C.kappa * t ^ C.weightOrder ≤
          stage t + continuation t := by
    filter_upwards [C.eventual_charge] with t ht
    simpa only [stage, continuation, rawFinkObstructionMass,
      C.response_supported, if_true, mul_add] using ht.2.2
  simpa only [stage, continuation] using
    analytic_sum_powerCharge_left_or_right
      hstage hcontinuation htotal

/-- A transition-invisible selected response carries its entire obstruction
margin in the stage term. -/
theorem stageCharge_of_transitionInvisible
    {germ : G.AnalyticBellmanGerm}
    {H K : G.State → Payoff ι}
    (C : AnalyticOrientedFinkObstructionResponse germ H K)
    (hinvisible :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        ∀ destination,
          germ.rawPureDeviationStateKernelCurve
              t C.response.2.1 C.response.1 C.response.2.2 destination =
            germ.rawStateKernelCurve
              t C.response.2.1 destination) :
    ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      C.kappa * t ^ C.weightOrder ≤
        responseOrientation C.positive *
          germ.rawPureDeviationStageGainCurve
            t C.response.2.1 C.response.1 C.response.2.2 := by
  filter_upwards [C.eventual_charge, hinvisible] with t hevidence hsame
  have hcontinuation :
      germ.rawPureDeviationContinuationGainCurve
          (H - K) t C.response.2.1
            C.response.1 C.response.2.2 = 0 := by
    unfold rawPureDeviationContinuationGainCurve
    apply Finset.sum_eq_zero
    intro destination _
    rw [hsame destination, sub_self, zero_mul]
  simpa only [rawFinkObstructionMass, C.response_supported, if_true,
    hcontinuation, add_zero] using hevidence.2.2

/-- The actual transition selected by the analytic Fink response has one
stable analytic occupation classification.

The first branch supplies a pole-cleared nonnegative circulation using the
selected transition. The second supplies a bounded analytic potential whose
drift is nonnegative on every other baseline or deviation transition and is
an exact positive power law on the selected transition. -/
theorem analyticCirculation_xor_boundedPotential
    {germ : G.AnalyticBellmanGerm}
    {H K : G.State → Payoff ι}
    (C : AnalyticOrientedFinkObstructionResponse germ H K) :
    Xor
      (Nonempty
        (AnalyticPositiveCirculation
          germ.rawAnalyticOccupationColumn
          (Sum.inr C.response)))
      (Nonempty
        (AnalyticBoundedOccupationSeparator
          germ.rawAnalyticOccupationColumn
          (Sum.inr C.response))) := by
  exact analyticPositiveCirculation_xor_boundedSeparator
    germ.rawAnalyticOccupationColumn
    (Sum.inr C.response)
    germ.analytic_rawAnalyticOccupationColumn
    germ.eventually_sum_rawAnalyticOccupationColumn_eq_zero

/-- At a valid parameter in the bounded-potential branch, all actual
semantic transitions have nonnegative potential drift and the selected
transition has the exact analytic charge. -/
theorem boundedPotential_semanticDriftAt
    {germ : G.AnalyticBellmanGerm}
    {H K : G.State → Payoff ι}
    (C : AnalyticOrientedFinkObstructionResponse germ H K)
    (B : AnalyticBoundedOccupationSeparator
      germ.rawAnalyticOccupationColumn (Sum.inr C.response))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (hB :
      (∀ destination,
        0 ≤ B.potential t destination ∧
          B.potential t destination ≤ 1) ∧
      (∀ index :
          {index :
            G.State ⊕ (Σ who : ι, G.State × G.Act who) //
              index ≠ Sum.inr C.response},
        0 ≤ ∑ destination,
          B.potential t destination *
            germ.rawAnalyticOccupationColumn
              t index.1 destination) ∧
      (∑ destination,
        B.potential t destination *
          germ.rawAnalyticOccupationColumn
            t (Sum.inr C.response) destination) =
        B.charge * t ^ B.poleOrder) :
    (∀ index,
      0 ≤
        expect
            (germ.finkActualOccupationKernelAt ht index)
            (B.potential t) -
          B.potential t (finkActualOccupationSource index)) ∧
    expect
          (germ.finkActualOccupationKernelAt ht
            (Sum.inr C.response))
          (B.potential t) -
        B.potential t
          (finkActualOccupationSource (Sum.inr C.response)) =
      B.charge * t ^ B.poleOrder := by
  have hpair (index :
      G.State ⊕ (Σ who : ι, G.State × G.Act who)) :=
    germ.potential_pair_rawAnalyticOccupationColumn_eq
      ht (B.potential t) index
  constructor
  · intro index
    rw [← hpair index]
    by_cases hi : index = Sum.inr C.response
    · subst index
      rw [hB.2.2]
      exact mul_nonneg B.charge_pos.le
        (pow_nonneg (le_of_lt ht.1) _)
    · exact hB.2.1 ⟨index, hi⟩
  · rw [← hpair (Sum.inr C.response)]
    exact hB.2.2

/-- In the bounded-potential branch, arbitrary history-dependent switching
among source-compatible actual transitions can use the selected response
only a bounded expected number of times. At parameter `t`, each use costs
the exact margin `B.charge * t ^ B.poleOrder`. -/
theorem eventually_selectedUseBudget
    {germ : G.AnalyticBellmanGerm}
    {H K : G.State → Payoff ι}
    (C : AnalyticOrientedFinkObstructionResponse germ H K)
    (B : AnalyticBoundedOccupationSeparator
      germ.rawAnalyticOccupationColumn (Sum.inr C.response)) :
    ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      ∀ (ht : t ∈ Ioo (0 : ℝ) germ.radius)
        (initial : G.State)
        (choice :
          ∀ n, (Fin (n + 1) → G.State) →
            (G.State ⊕ (Σ who : ι, G.State × G.Act who))),
        (∀ n history,
          finkActualOccupationSource (choice n history) =
            history (Fin.last n)) →
        ∀ T,
          (B.charge * t ^ B.poleOrder) *
              expect
                (adaptiveHistoryLaw
                  (adaptiveMarkovStep initial
                    (selectedTransitionComparison
                      (germ.finkActualOccupationKernelAt ht)
                      choice))
                  (T + 1))
                (selectedTransitionUseCount
                  choice (Sum.inr C.response) T) ≤
            1 := by
  filter_upwards [B.eventual] with t hB
  intro ht initial choice hsource T
  obtain ⟨hdrift, hmargin⟩ :=
    C.boundedPotential_semanticDriftAt B ht hB
  exact margin_mul_expect_selectedTransitionUseCount_le_one
    initial
    (germ.finkActualOccupationKernelAt ht)
    finkActualOccupationSource choice
    (Sum.inr C.response) (B.potential t)
    hB.1 hsource hdrift hmargin.ge T

/-- At every valid positive parameter, the response selected from the
analytic obstruction enters the exact actual-flow alternative.

The circulation branch uses only genuinely available baseline and pure
deviation transitions. In the other branch, a Euclidean-unit potential is
subharmonic for every unselected transition and has strict positive drift
on the selected response. -/
theorem circulation_xor_unitPotentialAt
    {germ : G.AnalyticBellmanGerm}
    {H K : G.State → Payoff ι}
    (C : AnalyticOrientedFinkObstructionResponse germ H K)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius) :
    let z := germ.finkPointAt ht
    Xor
      (HasPositiveCirculation
        (stochasticOccupationColumn
          (G.finkStateKernel z)
          (fun e : Σ who : ι, G.State × G.Act who =>
            G.finkPureDeviationStateKernel
              z e.2.1 e.1 e.2.2)
          (fun e : Σ who : ι, G.State × G.Act who => e.2.1))
        (Sum.inr C.response))
      (∃ h : G.State → ℝ,
        (∑ destination, h destination ^ 2) = 1 ∧
        (∀ s,
          0 ≤
            expect (G.finkStateKernel z s) h - h s) ∧
        (∀ e : Σ who : ι, G.State × G.Act who,
          e ≠ C.response →
            0 ≤
              expect
                  (G.finkPureDeviationStateKernel
                    z e.2.1 e.1 e.2.2) h -
                h e.2.1) ∧
        0 <
          expect
              (G.finkPureDeviationStateKernel
                z C.response.2.1 C.response.1 C.response.2.2) h -
            h C.response.2.1) := by
  dsimp only
  exact controlledEdgeCirculation_xor_unitPotential
    (G.finkStateKernel (germ.finkPointAt ht))
    (fun e : Σ who : ι, G.State × G.Act who =>
      G.finkPureDeviationStateKernel
        (germ.finkPointAt ht) e.2.1 e.1 e.2.2)
    (fun e : Σ who : ι, G.State × G.Act who => e.2.1)
    C.response

end AnalyticOrientedFinkObstructionResponse

end AnalyticBellmanGerm
end StochasticGame
end GameTheory
