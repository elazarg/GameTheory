/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.VanishingDiscount.Analytic.Accounting.AnalyticStageResponseDichotomy
import Math.AnalyticLinearSystem

/-!
# Coherent selection in the harmonic stage-response branch

Pointwise harmonic adjustments do not automatically form an analytic
curve. The finite transposed Fink system does, however, admit a fixed-basis
Cramer selector after one common endpoint pole is cleared.

The selected curve has a sharp alternative. Either the clearing power
divides it analytically and gives a coherent bounded adjustment, or its
first lower-order coefficient is a nonzero endpoint-harmonic direction.
The latter is exactly the datum consumed by the harmonic-jet rank.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Filter Math Math.LinearAlgebra Set

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

namespace AnalyticBellmanGerm

/-- Read a curve indexed by Fink obstruction rows as a payoff-adjustment
curve. -/
def adjustmentCurveOfRow
    (coefficient : ℝ → FinkObstructionRow G → ℝ) :
    ℝ → G.State → Payoff ι :=
  fun t destination who => coefficient t (who, destination)

omit [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)] in
@[simp]
theorem finkAdjustmentCoefficient_adjustmentCurveOfRow
    (coefficient : ℝ → FinkObstructionRow G → ℝ)
    (t : ℝ) :
    G.finkAdjustmentCoefficient
        (adjustmentCurveOfRow coefficient t) =
      coefficient t := by
  funext row
  rcases row with ⟨who, destination⟩
  rfl

omit [DecidableEq G.State] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)] in
/-- Analyticity of row coordinates is the same as analyticity of the
corresponding payoff-adjustment curve. -/
theorem analytic_adjustmentCurveOfRow
    (coefficient : ℝ → FinkObstructionRow G → ℝ)
    (hcoefficient : AnalyticAt ℝ coefficient 0) :
    AnalyticAt ℝ (adjustmentCurveOfRow coefficient) 0 := by
  rw [analyticAt_pi_iff]
  intro destination
  rw [analyticAt_pi_iff]
  intro who
  exact analyticAt_pi_iff.mp hcoefficient (who, destination)

/-- The residual column of the raw transposed obstruction matrix is the
moving continuation residual of the corresponding adjustment curve. -/
theorem rawFinkObstructionTranspose_mulVec_adjustment_residual
    (germ : G.AnalyticBellmanGerm)
    (supported :
      (Σ who : ι, G.State × G.Act who) → Bool)
    (adjustment : ℝ → G.State → Payoff ι)
    (t : ℝ) (s : G.State) (who : ι) :
    Matrix.mulVec
        (germ.rawFinkObstructionBalance supported t).transpose
        (G.finkAdjustmentCoefficient (adjustment t))
        (Sum.inl (s, who)) =
      germ.rawContinuationCurve adjustment t s who -
        adjustment t s who := by
  classical
  rw [germ.rawContinuationCurve_eq_sum_rawStateKernel]
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    rawFinkObstructionBalance, finkAdjustmentCoefficient,
    Fintype.sum_prod_type]
  rw [Fintype.sum_eq_single who]
  · simp only [if_true]
    calc
      (∑ destination,
          (germ.rawStateKernelCurve t s destination -
              if s = destination then 1 else 0) *
            adjustment t destination who) =
          (∑ destination,
              germ.rawStateKernelCurve t s destination *
                adjustment t destination who) -
            ∑ destination,
              (if s = destination then 1 else 0) *
                adjustment t destination who := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro destination _
        ring
      _ = (∑ destination,
            germ.rawStateKernelCurve t s destination *
              adjustment t destination who) -
          adjustment t s who := by
        simp
  · intro other hother
    simp [Ne.symm hother]

/-- A raw endpoint transpose-kernel vector is an endpoint-harmonic payoff
adjustment. This uses only residual columns, so it is independent of whether
the positive-parameter action support agrees with the endpoint support. -/
theorem endpointHarmonic_of_rawFinkTranspose_kernel
    (germ : G.AnalyticBellmanGerm)
    (supported :
      (Σ who : ι, G.State × G.Act who) → Bool)
    (coefficient : FinkObstructionRow G → ℝ)
    (hkernel :
      Matrix.mulVec
          (germ.rawFinkObstructionBalance supported 0).transpose
          coefficient = 0) :
    G.finkContinuationResidualVector
        (adjustmentCurveOfRow (fun _ => coefficient) 0)
        germ.endpointFinkPoint = 0 := by
  let adjustment : ℝ → G.State → Payoff ι :=
    adjustmentCurveOfRow (fun _ => coefficient)
  funext s who
  have hcoordinate := congrFun hkernel (Sum.inl (s, who))
  rw [← finkAdjustmentCoefficient_adjustmentCurveOfRow
      (fun _ => coefficient) 0,
    germ.rawFinkObstructionTranspose_mulVec_adjustment_residual
      supported adjustment 0 s who] at hcoordinate
  simp only [Pi.zero_apply] at hcoordinate
  change
    G.finkContinuationEU
          (adjustment 0)
          germ.endpointFinkPoint s who -
        adjustment 0 s who =
      0
  have hcontinuation :=
    congrFun
      (congrFun
        (germ.rawContinuationCurve_zero_eq_finkContinuationEU
          adjustment) s) who
  rw [← hcontinuation]
  exact hcoordinate

/-- In the stabilized harmonic branch, one fixed support and one common
power clear all poles of a Cramer-selected adjustment coefficient curve. -/
theorem
    exists_analytic_poleCleared_eventual_stageHarmonicAdjustment
    (germ : G.AnalyticBellmanGerm)
    (H : G.State → Payoff ι)
    (hharmonic :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        t ∈ Ioo (0 : ℝ) germ.radius ∧
          ∀ ht : t ∈ Ioo (0 : ℝ) germ.radius,
            ∃ A : G.State → Payoff ι,
              G.finkContinuationResidualVector A
                  (germ.finkPointAt ht) = 0 ∧
                ∀ s who (d : G.Act who),
                  G.finkProfile
                      (germ.finkPointAt ht) s who d ≠ 0 →
                    G.finkContinuationGain A
                        (germ.finkPointAt ht) s who d =
                      G.finkStageGain
                        (germ.finkPointAt ht) s who d) :
    ∃ (supported :
          (Σ who : ι, G.State × G.Act who) → Bool)
        (poleOrder : ℕ)
        (coefficient : ℝ → FinkObstructionRow G → ℝ),
      AnalyticAt ℝ coefficient 0 ∧
        ∀ᶠ t in nhdsWithin 0 (Ioi 0),
          t ∈ Ioo (0 : ℝ) germ.radius ∧
            (∀ ht : t ∈ Ioo (0 : ℝ) germ.radius,
              ∀ e : Σ who : ι, G.State × G.Act who,
                supported e = true ↔
                  G.finkProfile (germ.finkPointAt ht)
                    e.2.1 e.1 e.2.2 ≠ 0) ∧
            Matrix.mulVec
                (germ.rawFinkObstructionBalance
                  supported t).transpose
                (coefficient t) =
              t ^ poleOrder •
                germ.rawFinkObstructionMass supported H H t := by
  obtain ⟨supported, hsupport⟩ :=
    germ.exists_eventually_fixed_finkSupport
  let A : ℝ →
      Matrix (FinkObstructionColumn G)
        (FinkObstructionRow G) ℝ := fun t =>
    (germ.rawFinkObstructionBalance supported t).transpose
  let b : ℝ → FinkObstructionColumn G → ℝ := fun t =>
    germ.rawFinkObstructionMass supported H H t
  have hA :
      ∀ column row,
        AnalyticAt ℝ (fun t => A t column row) 0 := by
    intro column row
    simpa only [A, Matrix.transpose_apply] using
      germ.analytic_rawFinkObstructionBalance
        supported row column
  have hb :
      ∀ column,
        AnalyticAt ℝ (fun t => b t column) 0 := by
    intro column
    exact germ.analytic_rawFinkObstructionMass
      supported H H column
  have hfeasible :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        ∃ coefficient : FinkObstructionRow G → ℝ,
          Matrix.mulVec (A t) coefficient = b t := by
    filter_upwards [hharmonic, hsupport] with t ht hsupportAt
    apply
      (germ.exists_finkHarmonicAdjustment_iff_rawTranspose_mulVec
        supported H H ht.1 (hsupportAt.2 ht.1)).mp
    obtain ⟨adjustment, hresidual, hgain⟩ := ht.2 ht.1
    refine ⟨adjustment, hresidual, ?_⟩
    intro s who d hsupported
    have hzero :
        G.finkContinuationGain (H - H)
            (germ.finkPointAt ht.1) s who d = 0 := by
      apply G.finkContinuationGain_eq_zero_of_stateConstant
      intro other source destination
      simp
    simpa only [hzero, add_zero] using
      hgain s who d hsupported
  obtain ⟨poleOrder, coefficient, hcoefficient, hequation⟩ :=
    exists_analytic_scaled_eventual_linearSolution
      A b hA hb hfeasible
  refine ⟨supported, poleOrder, coefficient, hcoefficient, ?_⟩
  filter_upwards [hsupport, hequation] with t hsupportAt hequationAt
  refine ⟨hsupportAt.1, hsupportAt.2, ?_⟩
  simpa only [A, b, sub_zero] using hequationAt

/-- A single analytic adjustment curve realizing the supported stage gains
on every sufficiently small positive slice. -/
structure CoherentAnalyticStageHarmonicAdjustment
    (germ : G.AnalyticBellmanGerm) where
  adjustment : ℝ → G.State → Payoff ι
  analytic_adjustment : AnalyticAt ℝ adjustment 0
  realizes_stage :
    ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      t ∈ Ioo (0 : ℝ) germ.radius ∧
        ∀ ht : t ∈ Ioo (0 : ℝ) germ.radius,
          G.finkContinuationResidualVector
              (adjustment t) (germ.finkPointAt ht) = 0 ∧
            ∀ s who (d : G.Act who),
              G.finkProfile
                  (germ.finkPointAt ht) s who d ≠ 0 →
                G.finkContinuationGain (adjustment t)
                    (germ.finkPointAt ht) s who d =
                  G.finkStageGain
                    (germ.finkPointAt ht) s who d

/-- The lower-order branch of a pole-cleared harmonic adjustment. -/
structure AnalyticStageHarmonicKernelJet
    (germ : G.AnalyticBellmanGerm) where
  supported :
    (Σ who : ι, G.State × G.Act who) → Bool
  poleOrder : ℕ
  scaledCoefficient : ℝ → FinkObstructionRow G → ℝ
  jet :
    AnalyticLinearKernelJet
      (fun t =>
        (germ.rawFinkObstructionBalance supported t).transpose)
      0 poleOrder scaledCoefficient

namespace AnalyticStageHarmonicKernelJet

/-- Payoff adjustment represented by the leading row coefficient. -/
def leadingAdjustment
    {germ : G.AnalyticBellmanGerm}
    (jet : germ.AnalyticStageHarmonicKernelJet) :
    G.State → Payoff ι :=
  adjustmentCurveOfRow jet.jet.factor 0

/-- The pole branch really supplies a nonzero payoff direction. -/
theorem leadingAdjustment_ne_zero
    {germ : G.AnalyticBellmanGerm}
    (jet : germ.AnalyticStageHarmonicKernelJet) :
    jet.leadingAdjustment ≠ 0 := by
  intro hzero
  apply jet.jet.leading_ne_zero
  funext row
  rcases row with ⟨who, destination⟩
  have hcoordinate := congrFun (congrFun hzero destination) who
  exact hcoordinate

/-- The leading adjustment belongs to the endpoint harmonic subspace. -/
theorem leadingAdjustment_mem_endpointHarmonicSubmodule
    {germ : G.AnalyticBellmanGerm}
    (jet : germ.AnalyticStageHarmonicKernelJet) :
    jet.leadingAdjustment ∈ germ.endpointHarmonicSubmodule := by
  apply
    (germ.mem_endpointHarmonicSubmodule_iff
      jet.leadingAdjustment).2
  exact germ.endpointHarmonic_of_rawFinkTranspose_kernel
    jet.supported (jet.jet.factor 0)
    jet.jet.endpoint_kernel

/-- Relative to the processed harmonic span, the leading direction is
either redundant or strictly decreases the remaining harmonic rank. -/
theorem redundant_or_rankDecrease
    {germ : G.AnalyticBellmanGerm}
    (jet : germ.AnalyticStageHarmonicKernelJet)
    (span : germ.EndpointHarmonicJetSpan) :
    jet.leadingAdjustment ∈ span.carrier ∨
      ∃ hH :
          jet.leadingAdjustment ∈
            germ.endpointHarmonicSubmodule,
        (span.extend jet.leadingAdjustment hH).rank <
          span.rank := by
  by_cases hprocessed :
      jet.leadingAdjustment ∈ span.carrier
  · exact Or.inl hprocessed
  · have hH :=
      jet.leadingAdjustment_mem_endpointHarmonicSubmodule
    exact Or.inr
      ⟨hH,
        span.rank_extend_lt jet.leadingAdjustment hH hprocessed⟩

end AnalyticStageHarmonicKernelJet

/-- Decode a raw transposed-system solution into the corresponding
semantic harmonic stage adjustment on a positive slice. -/
theorem adjustmentCurveOfRow_realizes_stage
    (germ : G.AnalyticBellmanGerm)
    (supported :
      (Σ who : ι, G.State × G.Act who) → Bool)
    (H : G.State → Payoff ι)
    (coefficient : ℝ → FinkObstructionRow G → ℝ)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (hsupported :
      ∀ e : Σ who : ι, G.State × G.Act who,
        supported e = true ↔
          G.finkProfile (germ.finkPointAt ht)
            e.2.1 e.1 e.2.2 ≠ 0)
    (hequation :
      Matrix.mulVec
          (germ.rawFinkObstructionBalance supported t).transpose
          (coefficient t) =
        germ.rawFinkObstructionMass supported H H t) :
    G.finkContinuationResidualVector
        (adjustmentCurveOfRow coefficient t)
        (germ.finkPointAt ht) = 0 ∧
      ∀ s who (d : G.Act who),
        G.finkProfile (germ.finkPointAt ht) s who d ≠ 0 →
          G.finkContinuationGain
              (adjustmentCurveOfRow coefficient t)
              (germ.finkPointAt ht) s who d =
            G.finkStageGain
              (germ.finkPointAt ht) s who d := by
  have hsemantic :
      Matrix.mulVec
          (G.finkObstructionBalance
            (germ.finkPointAt ht)).transpose
          (coefficient t) =
        G.finkObstructionMass
          (germ.finkPointAt ht) H H := by
    rw [← germ.rawFinkObstructionBalance_eq_finkPointAt
        supported ht hsupported,
      ← germ.rawFinkObstructionMass_eq_finkPointAt
        supported H H ht hsupported]
    exact hequation
  have hcoefficient :
      G.finkAdjustmentCoefficient
          (adjustmentCurveOfRow coefficient t) =
        coefficient t :=
    finkAdjustmentCoefficient_adjustmentCurveOfRow coefficient t
  constructor
  · funext s who
    have hcoordinate :=
      congrFun hsemantic (Sum.inl (s, who))
    rw [← hcoefficient,
      G.finkObstructionTranspose_mulVec_adjustment_residual]
      at hcoordinate
    simpa [finkObstructionMass] using hcoordinate
  · intro s who d hsupport
    have hcoordinate :=
      congrFun hsemantic (Sum.inr ⟨who, s, d⟩)
    rw [← hcoefficient,
      G.finkObstructionTranspose_mulVec_adjustment_action,
      if_pos hsupport]
      at hcoordinate
    have hmassCoordinate :
        G.finkObstructionMass
              (germ.finkPointAt ht) H H
              (Sum.inr ⟨who, s, d⟩) =
            G.finkStageGain
              (germ.finkPointAt ht) s who d := by
      rw [← germ.rawFinkObstructionMass_eq_finkPointAt
          supported H H ht hsupported,
        germ.rawFinkObstructionMass_sameContinuation_action,
        if_pos ((hsupported ⟨who, s, d⟩).2 hsupport),
        germ.rawPureDeviationStageGainCurve_eq_finkPointAt ht]
    exact hcoordinate.trans hmassCoordinate

/-- Sharp coherent-selection alternative inside the stabilized harmonic
branch.

Either the Cramer pole is removable and gives one bounded analytic semantic
adjustment, or the first lower-order coefficient is a nonzero
endpoint-harmonic kernel jet. -/
theorem
    coherentAnalyticStageHarmonicAdjustment_or_kernelJet
    (germ : G.AnalyticBellmanGerm)
    (H : G.State → Payoff ι)
    (hharmonic :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        t ∈ Ioo (0 : ℝ) germ.radius ∧
          ∀ ht : t ∈ Ioo (0 : ℝ) germ.radius,
            ∃ A : G.State → Payoff ι,
              G.finkContinuationResidualVector A
                  (germ.finkPointAt ht) = 0 ∧
                ∀ s who (d : G.Act who),
                  G.finkProfile
                      (germ.finkPointAt ht) s who d ≠ 0 →
                    G.finkContinuationGain A
                        (germ.finkPointAt ht) s who d =
                      G.finkStageGain
                        (germ.finkPointAt ht) s who d) :
    Nonempty germ.CoherentAnalyticStageHarmonicAdjustment ∨
      Nonempty germ.AnalyticStageHarmonicKernelJet := by
  obtain ⟨supported, poleOrder, coefficient, hcoefficient,
      heventual⟩ :=
    germ.exists_analytic_poleCleared_eventual_stageHarmonicAdjustment
      H hharmonic
  let A : ℝ →
      Matrix (FinkObstructionColumn G)
        (FinkObstructionRow G) ℝ := fun t =>
    (germ.rawFinkObstructionBalance supported t).transpose
  let b : ℝ → FinkObstructionColumn G → ℝ := fun t =>
    germ.rawFinkObstructionMass supported H H t
  have hA :
      ∀ column row,
        AnalyticAt ℝ (fun t => A t column row) 0 := by
    intro column row
    simpa only [A, Matrix.transpose_apply] using
      germ.analytic_rawFinkObstructionBalance
        supported row column
  have hb :
      ∀ column,
        AnalyticAt ℝ (fun t => b t column) 0 := by
    intro column
    exact germ.analytic_rawFinkObstructionMass
      supported H H column
  have hequation :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        Matrix.mulVec (A t) (coefficient t) =
          t ^ poleOrder • b t :=
    heventual.mono fun _ ht => ht.2.2
  rcases
      analytic_scaled_linearSolution_factor_or_kernelJet
        A b hA hb poleOrder coefficient hcoefficient
          (by simpa only [sub_zero] using hequation) with
    hfactor | hjet
  · left
    obtain ⟨factor, hfactorAnalytic, _hfactorEq,
        hfactorEquation⟩ := hfactor
    let adjustment : ℝ → G.State → Payoff ι :=
      adjustmentCurveOfRow factor
    refine ⟨
      { adjustment := adjustment
        analytic_adjustment :=
          analytic_adjustmentCurveOfRow factor hfactorAnalytic
        realizes_stage := ?_ }⟩
    filter_upwards [heventual, hfactorEquation] with
        t ht hfactorEquationAt
    refine ⟨ht.1, fun ht' => ?_⟩
    apply germ.adjustmentCurveOfRow_realizes_stage
      supported H factor ht' (ht.2.1 ht')
    simpa only [A, b] using hfactorEquationAt
  · right
    exact ⟨
      { supported := supported
        poleOrder := poleOrder
        scaledCoefficient := coefficient
        jet := hjet.some }⟩

/-- Complete local analytic stage-response trichotomy.

The harmonic branch has now been refined into a coherent bounded adjustment
or a nonzero endpoint-harmonic kernel jet. The complementary branch is the
fixed public action response constructed from the analytic obstruction. -/
theorem
    coherentStageAdjustment_or_kernelJet_or_stagePublicResponse
    [Nonempty G.State] [Nonempty ι] [∀ i, Nonempty (G.Act i)]
    (germ : G.AnalyticBellmanGerm)
    (H : G.State → Payoff ι) :
    Nonempty germ.CoherentAnalyticStageHarmonicAdjustment ∨
      Nonempty germ.AnalyticStageHarmonicKernelJet ∨
        ∃ response : Σ who : ι, G.State × G.Act who,
          Nonempty
            (AnalyticFinkStagePublicResponse germ response) := by
  rcases
      germ.stageHarmonicAdjustment_or_analyticStagePublicResponse H with
    hharmonic | hresponse
  · rcases
        germ.coherentAnalyticStageHarmonicAdjustment_or_kernelJet
          H hharmonic with
      hadjustment | hjet
    · exact Or.inl hadjustment
    · exact Or.inr (Or.inl hjet)
  · exact Or.inr (Or.inr hresponse)

end AnalyticBellmanGerm

end StochasticGame
end GameTheory
