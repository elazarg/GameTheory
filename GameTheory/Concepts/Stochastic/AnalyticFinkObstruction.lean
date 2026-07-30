/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.AnalyticBellmanHierarchy
import GameTheory.Concepts.Stochastic.FinkObstructionFarkas

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

set_option autoImplicit false

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
  exact ⟨hsupport_t.1,
    by simpa [balance, mass] using hcertificate_t.1,
    by simpa [balance, mass] using hcertificate_t.2⟩

end AnalyticBellmanGerm
end StochasticGame
end GameTheory
