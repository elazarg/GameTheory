/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.VanishingDiscount.Analytic.Accounting.AnalyticBellmanHierarchy
import UniformEquilibrium.VanishingDiscount.Fink.ActionWeightRepair

/-!
# Endpoint-harmonic continuation drift

Endpoint harmonicity is weaker than harmonicity under a positive-parameter
Bellman kernel. This file records the exact seam.

A fixed endpoint-harmonic payoff vector has analytic baseline drift
vanishing to at least first order in the ordinary analytic parameter. After
the analytic Fink action repair, the residual-weighted baseline drift still
has one factor of the parameter. No higher order follows without additional
jet equations.

The final finite example shows why this is not enough to dominate a positive
target of order two.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Filter Math Set

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

namespace AnalyticBellmanGerm

/-- Baseline continuation drift of a fixed state-payoff vector along the
moving analytic Fink profile. -/
def fixedBaselineDriftCurve
    (germ : G.AnalyticBellmanGerm)
    (W : G.State → Payoff ι) :
    ℝ → G.State → Payoff ι :=
  germ.rawContinuationCurve (fun _ => W) - fun _ => W

omit [DecidableEq G.State] in
theorem analytic_fixedBaselineDriftCurve
    (germ : G.AnalyticBellmanGerm)
    (W : G.State → Payoff ι) :
    AnalyticAt ℝ (germ.fixedBaselineDriftCurve W) 0 := by
  exact
    (germ.analytic_rawContinuationCurve analyticAt_const).sub
      analyticAt_const

omit [DecidableEq G.State] in
theorem fixedBaselineDriftCurve_zero_of_endpointHarmonic
    (germ : G.AnalyticBellmanGerm)
    (W : G.State → Payoff ι)
    (hW :
      G.finkContinuationResidualVector
        W germ.endpointFinkPoint = 0) :
    germ.fixedBaselineDriftCurve W 0 = 0 := by
  ext s who
  have hcoordinate :=
    congrFun (congrFun hW s) who
  simp only [fixedBaselineDriftCurve, Pi.sub_apply]
  rw [germ.rawContinuationCurve_zero_eq_finkContinuationEU]
  simpa [finkContinuationResidualVector,
    finkContinuationResidual] using hcoordinate

omit [DecidableEq G.State] in
/-- Endpoint harmonicity supplies exactly one universal analytic parameter
factor in the moving-kernel baseline drift. -/
theorem exists_fixedBaselineDriftFactor_of_endpointHarmonic
    (germ : G.AnalyticBellmanGerm)
    (W : G.State → Payoff ι)
    (hW :
      G.finkContinuationResidualVector
        W germ.endpointFinkPoint = 0) :
    ∃ factor : ℝ → G.State → Payoff ι,
      AnalyticAt ℝ factor 0 ∧
        ∀ᶠ t in nhds 0,
          germ.fixedBaselineDriftCurve W t = t • factor t := by
  have hanalytic :=
    germ.analytic_fixedBaselineDriftCurve W
  have hzero :=
    germ.fixedBaselineDriftCurve_zero_of_endpointHarmonic W hW
  have horder_ne :
      analyticOrderAt
          (germ.fixedBaselineDriftCurve W) 0 ≠ 0 :=
    hanalytic.analyticOrderAt_ne_zero.mpr hzero
  have hone :
      (1 : ℕ∞) ≤
        analyticOrderAt (germ.fixedBaselineDriftCurve W) 0 :=
    Order.one_le_iff_ne_zero.mpr horder_ne
  obtain ⟨factor, hfactor, heq⟩ :=
    (natCast_le_analyticOrderAt hanalytic (n := 1)).mp hone
  refine ⟨factor, hfactor, ?_⟩
  filter_upwards [heq] with t ht
  simpa using ht

omit [DecidableEq G.State] in
/-- Analytic weights cannot remove the first-order vanishing forced by
endpoint harmonicity. -/
theorem exists_weightedBaselineDriftFactor_of_endpointHarmonic
    (germ : G.AnalyticBellmanGerm)
    (W : G.State → Payoff ι)
    (weight : ℝ → G.State → ℝ)
    (hweight :
      ∀ s, AnalyticAt ℝ (fun t => weight t s) 0)
    (hW :
      G.finkContinuationResidualVector
        W germ.endpointFinkPoint = 0)
    (who : ι) :
    ∃ factor : ℝ → ℝ,
      AnalyticAt ℝ factor 0 ∧
        ∀ᶠ t in nhds 0,
          (∑ s, weight t s *
            germ.fixedBaselineDriftCurve W t s who) =
          t * factor t := by
  obtain ⟨driftFactor, hdriftAnalytic, hdrift⟩ :=
    germ.exists_fixedBaselineDriftFactor_of_endpointHarmonic W hW
  let factor : ℝ → ℝ := fun t =>
    ∑ s, weight t s * driftFactor t s who
  have hfactor : AnalyticAt ℝ factor 0 := by
    apply Finset.univ.analyticAt_fun_sum
    intro s _
    exact (hweight s).mul
      ((analyticAt_pi_iff.mp
        ((analyticAt_pi_iff.mp hdriftAnalytic) s)) who)
  refine ⟨factor, hfactor, ?_⟩
  filter_upwards [hdrift] with t ht
  have htcoord :
      ∀ s,
        germ.fixedBaselineDriftCurve W t s who =
          t * driftFactor t s who := by
    intro s
    have hcoordinate :=
      congrFun (congrFun ht s) who
    simpa only [Pi.smul_apply, smul_eq_mul] using hcoordinate
  simp_rw [htcoord]
  dsimp only [factor]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- Specialization to the residual coordinates of the analytic action
repair. Their weighted baseline drift is still only known to be first
order. -/
theorem exists_rawActionRepairedResidualDriftFactor
    (germ : G.AnalyticBellmanGerm)
    (supported :
      (Σ who : ι, G.State × G.Act who) → Bool)
    (signed : ℝ → FinkObstructionColumn G → ℝ)
    (hsigned : AnalyticAt ℝ signed 0)
    (H K : G.State → Payoff ι)
    (hHK :
      G.finkContinuationResidualVector
        (H - K) germ.endpointFinkPoint = 0)
    (who : ι) :
    ∃ factor : ℝ → ℝ,
      AnalyticAt ℝ factor 0 ∧
        ∀ᶠ t in nhds 0,
          (∑ s,
            germ.rawActionRepairedFinkObstructionWeight
                supported signed t (Sum.inl (s, who)) *
              germ.fixedBaselineDriftCurve (H - K) t s who) =
            t * factor t := by
  let weight : ℝ → G.State → ℝ := fun t s =>
    germ.rawActionRepairedFinkObstructionWeight
      supported signed t (Sum.inl (s, who))
  have hweight :
      ∀ s, AnalyticAt ℝ (fun t => weight t s) 0 := by
    intro s
    exact
      analyticAt_pi_iff.mp
        (germ.analytic_rawActionRepairedFinkObstructionWeight
          supported signed hsigned)
        (Sum.inl (s, who))
  simpa only [weight] using
    germ.exists_weightedBaselineDriftFactor_of_endpointHarmonic
      (H - K) weight hweight hHK who

omit [DecidableEq G.State] in
/-- The Poisson equation used by the finite-bias hierarchy does not make
`H - K` harmonic. Its residual is exactly endpoint value minus current
on-profile stage payoff. -/
theorem FiniteBiasSeed.continuationResidual_H_sub_K_eq
    {germ : G.AnalyticBellmanGerm}
    (seed : germ.FiniteBiasSeed)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (K : G.State → Payoff ι)
    (hPoisson :
      G.finkBellmanForcingVector germ.endpointValue seed.H
          (germ.finkPointAt ht) =
        -G.finkContinuationResidualVector K
          (germ.finkPointAt ht)) :
    G.finkContinuationResidualVector
        (seed.H - K) (germ.finkPointAt ht) =
      fun s who =>
        germ.endpointValue s who -
          G.finkStageEU (germ.finkPointAt ht) s who := by
  ext s who
  have hcoordinate :=
    congrFun (congrFun hPoisson s) who
  simp only [finkBellmanForcingVector,
    finkContinuationResidualVector,
    finkContinuationResidual, Pi.sub_apply,
    Pi.neg_apply] at hcoordinate ⊢
  rw [G.finkContinuationEU_sub]
  linarith

omit [DecidableEq G.State] in
/-- Consequently, under the finite-bias Poisson equation, positive-parameter
harmonicity is equivalent to pointwise equality of current on-profile stage
payoff and the endpoint value. -/
theorem FiniteBiasSeed.harmonic_H_sub_K_iff_stage_eq_endpoint
    {germ : G.AnalyticBellmanGerm}
    (seed : germ.FiniteBiasSeed)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (K : G.State → Payoff ι)
    (hPoisson :
      G.finkBellmanForcingVector germ.endpointValue seed.H
          (germ.finkPointAt ht) =
        -G.finkContinuationResidualVector K
          (germ.finkPointAt ht)) :
    G.finkContinuationResidualVector
        (seed.H - K) (germ.finkPointAt ht) = 0 ↔
      ∀ s who,
        G.finkStageEU (germ.finkPointAt ht) s who =
          germ.endpointValue s who := by
  rw [seed.continuationResidual_H_sub_K_eq ht K hPoisson]
  constructor
  · intro hzero s who
    have hcoordinate := congrFun (congrFun hzero s) who
    simp only [Pi.zero_apply] at hcoordinate
    linarith
  · intro hstage
    funext s who
    simp only [Pi.zero_apply]
    rw [hstage]
    simp

end AnalyticBellmanGerm

namespace EndpointHarmonicDriftCounterexample

/-- A two-state analytic stochastic matrix. State `false` leaks to `true`
with probability `t`; state `true` is absorbing. -/
def rawKernel (t : ℝ) (source destination : Bool) : ℝ :=
  match source, destination with
  | false, false => 1 - t
  | false, true => t
  | true, false => 0
  | true, true => 1

/-- Endpoint-harmonic value, equal to one at `false` and zero at `true`. -/
def value (state : Bool) : ℝ :=
  if state then 0 else 1

def drift (t : ℝ) (source : Bool) : ℝ :=
  ∑ destination, rawKernel t source destination * value destination -
    value source

@[simp]
theorem drift_false (t : ℝ) :
    drift t false = -t := by
  simp [drift, rawKernel, value]

@[simp]
theorem drift_true (t : ℝ) :
    drift t true = 0 := by
  simp [drift, rawKernel, value]

theorem endpoint_harmonic (source : Bool) :
    drift 0 source = 0 := by
  cases source <;> simp

theorem rawKernel_sum_eq_one (t : ℝ) (source : Bool) :
    ∑ destination, rawKernel t source destination = 1 := by
  cases source <;> simp [rawKernel]

theorem rawKernel_nonneg
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (source destination : Bool) :
    0 ≤ rawKernel t source destination := by
  rcases ht with ⟨ht0, ht1⟩
  cases source <;> cases destination <;>
    simp [rawKernel, ht0, sub_nonneg.mpr ht1]

/-- A repaired residual coefficient of two makes the endpoint-harmonic
baseline drift first order. -/
def residualDrift (t : ℝ) : ℝ :=
  2 * drift t false

@[simp]
theorem residualDrift_eq (t : ℝ) :
    residualDrift t = -2 * t := by
  simp [residualDrift]

/-- A positive repaired target may start only at second order. -/
def positiveTarget (t : ℝ) : ℝ :=
  t ^ 2

/-- The first-order residual drift dominates the positive second-order
target, so the corresponding stage term remains negative. -/
theorem eventually_positiveTarget_add_residualDrift_neg :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
      0 < positiveTarget t ∧
        positiveTarget t + residualDrift t < 0 := by
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with
      t ht
  rcases ht with ⟨ht0, ht1⟩
  constructor
  · exact pow_pos ht0 2
  · simp only [positiveTarget, residualDrift_eq]
    have hproduct : 0 < t * (1 - t) :=
      mul_pos ht0 (sub_pos.mpr ht1)
    nlinarith

end EndpointHarmonicDriftCounterexample

end StochasticGame
end GameTheory
