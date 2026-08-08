/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.VanishingDiscount.Bellman.EndpointHarmonicDrift

/-!
# Moving harmonic corrections and the pure-stage obstruction branch

An endpoint-harmonic vector need not admit a continuous harmonic extension
along a moving finite-state Markov kernel. The obstruction is a rank drop of
the moving harmonic space at the endpoint.

The correct local alternative does not require such an extension. Apply the
Fink tangent alternative with equal continuation data. Its feasible branch
is exactly a moving harmonic correction representing the supported stage
gains; its obstruction branch has a pure-stage target. Thus no
residual-drift valuation comparison is needed in that branch.
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

omit [DecidableEq G.State] in
/-- Specializing the Fink alternative to equal continuation data gives the
exact stage-only dichotomy. In the first branch a harmonic correction
represents every supported stage gain. In the second branch the normalized
obstruction target contains no continuation term. -/
theorem
    stageHarmonicAdjustment_or_normalizedObstructionFlowAt
    (germ : G.AnalyticBellmanGerm)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (H : G.State → Payoff ι) :
    (∃ A : G.State → Payoff ι,
      G.finkContinuationResidualVector A
          (germ.finkPointAt ht) = 0 ∧
        ∀ s who (d : G.Act who),
          G.finkProfile (germ.finkPointAt ht) s who d ≠ 0 →
            G.finkContinuationGain A
                (germ.finkPointAt ht) s who d =
              G.finkStageGain
                (germ.finkPointAt ht) s who d) ∨
      Nonempty
        (G.NormalizedFinkSupportTangentObstructionFlow
          (germ.finkPointAt ht) H H) := by
  rcases
      germ.harmonicAdjustment_or_normalizedObstructionFlowAt
        ht H H with hA | hF
  · left
    obtain ⟨A, hresidual, hgain⟩ := hA
    refine ⟨A, hresidual, ?_⟩
    intro s who d hsupported
    have hzero :
        G.finkContinuationGain (H - H)
            (germ.finkPointAt ht) s who d = 0 := by
      apply G.finkContinuationGain_eq_zero_of_stateConstant
      intro other source destination
      simp
    simpa only [hzero, add_zero] using
      hgain s who d hsupported
  · exact Or.inr hF

omit [DecidableEq G.State] in
/-- With equal continuation data, the analytic obstruction mass of an
action column is exactly its supported pure stage gain. -/
theorem rawFinkObstructionMass_sameContinuation_action
    (germ : G.AnalyticBellmanGerm)
    (supported :
      (Σ who : ι, G.State × G.Act who) → Bool)
    (H : G.State → Payoff ι)
    (t : ℝ)
    (e : Σ who : ι, G.State × G.Act who) :
    germ.rawFinkObstructionMass supported H H t (Sum.inr e) =
      if supported e then
        germ.rawPureDeviationStageGainCurve
          t e.2.1 e.1 e.2.2
      else 0 := by
  simp [rawFinkObstructionMass,
    rawPureDeviationContinuationGainCurve]

omit [DecidableEq G.State] in
/-- The residual columns of every raw Fink target have zero mass. -/
theorem rawFinkObstructionMass_residual
    (germ : G.AnalyticBellmanGerm)
    (supported :
      (Σ who : ι, G.State × G.Act who) → Bool)
    (H K : G.State → Payoff ι)
    (t : ℝ) (residual : G.State × ι) :
    germ.rawFinkObstructionMass supported H K t
        (Sum.inl residual) = 0 := by
  rfl

/-- An eventual pure-stage obstruction has one analytic action repair whose
exact positive monomial is the aggregate supported stage gain. This is the
analytic form in which the endpoint-drift seam disappears. -/
theorem
    exists_analytic_actionRepaired_eventual_pureStageObstructionFlow
    (germ : G.AnalyticBellmanGerm)
    (H : G.State → Payoff ι)
    (hflow :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        ∀ ht : t ∈ Ioo (0 : ℝ) germ.radius,
          Nonempty
            (G.NormalizedFinkSupportTangentObstructionFlow
              (germ.finkPointAt ht) H H)) :
    ∃ (supported :
          (Σ who : ι, G.State × G.Act who) → Bool)
        (poleOrder : ℕ)
        (repaired : ℝ → FinkObstructionColumn G → ℝ),
      AnalyticAt ℝ repaired 0 ∧
        ∀ᶠ t in nhdsWithin 0 (Ioi 0),
          t ∈ Ioo (0 : ℝ) germ.radius ∧
            (∀ ht : t ∈ Ioo (0 : ℝ) germ.radius,
              ∀ e : Σ who : ι, G.State × G.Act who,
                supported e = true ↔
                  G.finkProfile (germ.finkPointAt ht)
                    e.2.1 e.1 e.2.2 ≠ 0) ∧
            Matrix.mulVec
                (germ.rawFinkObstructionBalance supported t)
                (repaired t) = 0 ∧
            (∑ e : Σ who : ι, G.State × G.Act who,
                (if supported e then
                  germ.rawPureDeviationStageGainCurve
                    t e.2.1 e.1 e.2.2
                else 0) * repaired t (Sum.inr e)) =
              germ.rawFinkSupportProduct supported t *
                t ^ poleOrder ∧
            (∀ e : Σ who : ι, G.State × G.Act who,
              supported e = true →
                0 < repaired t (Sum.inr e)) ∧
            0 <
              germ.rawFinkSupportProduct supported t *
                t ^ poleOrder := by
  obtain ⟨supported, poleOrder, repaired, hanalytic, heventual⟩ :=
    germ.exists_analytic_actionRepaired_eventual_finkObstructionFlow
      H H hflow
  refine ⟨supported, poleOrder, repaired, hanalytic, ?_⟩
  filter_upwards [heventual] with t ht
  refine ⟨ht.1, ht.2.1, ht.2.2.1, ?_, ht.2.2.2.2⟩
  rw [← ht.2.2.2.1]
  rw [Fintype.sum_sum_type]
  simp only [rawFinkObstructionMass_residual, zero_mul,
    Finset.sum_const_zero, zero_add]
  apply Finset.sum_congr rfl
  intro e _
  rw [germ.rawFinkObstructionMass_sameContinuation_action
    supported H t e]

end AnalyticBellmanGerm

namespace PositiveFinkActualOccupationFlow

omit [DecidableEq G.State] [∀ i, DecidableEq (G.Act i)] in
/-- Equal continuation data make the harmonicity premise of operational
stage extraction automatic. -/
theorem exists_owner_positive_stageGain_sameContinuation
    {U : ℝ} {z : G.finkDomain U}
    {H : G.State → Payoff ι}
    (C : G.PositiveFinkActualOccupationFlow z H H) :
    ∃ who : ι, 0 <
      ∑ s, ∑ d,
        C.actionMass s who d *
          G.finkStageGain z s who d := by
  apply C.exists_owner_positive_stageGain_of_harmonic
  intro who s
  simp

end PositiveFinkActualOccupationFlow

namespace NormalizedFinkSupportTangentObstructionFlow

omit [DecidableEq G.State] [∀ i, DecidableEq (G.Act i)] in
/-- On a baseline with a full-support stationary weight, the standard
action-and-occupation repair turns a pure-stage obstruction into a genuine
positive operational stage gain. No irreducibility assumption is used. -/
theorem exists_owner_positive_stageGain_afterRepair_sameContinuation
    {U : ℝ} (z : G.finkDomain U)
    (H : G.State → Payoff ι)
    (F :
      G.NormalizedFinkSupportTangentObstructionFlow z H H)
    (stationary : G.FullSupportFinkStationaryWeight z) :
    ∃ who : ι, 0 <
      ∑ s, ∑ d,
        (F.repairActionAndOccupation z H H stationary).actionMass
            s who d *
          G.finkStageGain z s who d := by
  exact
    PositiveFinkActualOccupationFlow.exists_owner_positive_stageGain_sameContinuation
      (F.repairActionAndOccupation z H H stationary)

end NormalizedFinkSupportTangentObstructionFlow

namespace MovingHarmonicCorrectionCounterexample

open EndpointHarmonicDriftCounterexample

/-- For every positive parameter, harmonicity for the leaking two-state
kernel forces equality of the two state values. -/
theorem harmonic_rawKernel_forces_eq
    {t : ℝ} (ht : 0 < t)
    (W : Bool → ℝ)
    (hharmonic :
      ∀ source,
        (∑ destination,
          rawKernel t source destination * W destination) =
            W source) :
    W false = W true := by
  have hfalse := hharmonic false
  simp [rawKernel] at hfalse
  nlinarith

/-- A continuous curve harmonic for every small positive leaking kernel
must have equal endpoint values. -/
theorem continuous_harmonicCurve_endpoint_eq
    (W : ℝ → Bool → ℝ)
    (hcontinuous : ContinuousAt W 0)
    (hharmonic :
      ∀ t ∈ Ioo (0 : ℝ) 1, ∀ source,
        (∑ destination,
          rawKernel t source destination * W t destination) =
            W t source) :
    W 0 false = W 0 true := by
  let difference : ℝ → ℝ := fun t => W t false - W t true
  have hdifferenceContinuous : ContinuousAt difference 0 := by
    exact
      (continuousAt_pi.mp hcontinuous false).sub
        (continuousAt_pi.mp hcontinuous true)
  have heventual :
      ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
        difference t = 0 := by
    filter_upwards
        [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with
        t ht
    exact sub_eq_zero.mpr
      (harmonic_rawKernel_forces_eq ht.1 (W t)
        (hharmonic t ht))
  have hlimitAtEndpoint :
      Tendsto difference
        (nhdsWithin (0 : ℝ) (Ioi 0))
        (nhds (difference 0)) :=
    hdifferenceContinuous.tendsto.mono_left inf_le_left
  have hlimitZero :
      Tendsto difference
        (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) :=
    tendsto_const_nhds.congr'
      (heventual.mono fun _ ht => ht.symm)
  have : difference 0 = 0 :=
    tendsto_nhds_unique hlimitAtEndpoint hlimitZero
  exact sub_eq_zero.mp this

/-- The endpoint-harmonic vector `(1,0)` has no analytic harmonic extension
along the leaking kernels. This is the minimal rank-change obstruction to a
moving analytic harmonic correction. -/
theorem not_exists_analytic_harmonicExtension :
    ¬ ∃ W : ℝ → Bool → ℝ,
      AnalyticAt ℝ W 0 ∧
        W 0 = value ∧
        ∀ t ∈ Ioo (0 : ℝ) 1, ∀ source,
          (∑ destination,
            rawKernel t source destination * W t destination) =
              W t source := by
  rintro ⟨W, hanalytic, hendpoint, hharmonic⟩
  have heq :=
    continuous_harmonicCurve_endpoint_eq
      W hanalytic.continuousAt hharmonic
  rw [hendpoint] at heq
  simp [value] at heq

end MovingHarmonicCorrectionCounterexample

end StochasticGame
end GameTheory
