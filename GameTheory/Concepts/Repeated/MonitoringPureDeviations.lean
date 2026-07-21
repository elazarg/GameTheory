/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Repeated.MonitoringDecomposition
import GameTheory.Concepts.Repeated.MonitoringRankInstances

/-!
# Pure-Deviation Reduction for Public Monitoring

For behavioral mixed extensions at embedded pure profiles, every mixed
unilateral deviation is a lottery over pure deviations. Consequently, it is
enough to check pure deviations in the APS enforceability inequalities.
-/

noncomputable section

namespace GameTheory
namespace KernelGame
namespace PublicMonitoring

open Math.Probability

variable {iota : Type} {G : KernelGame iota}

/-- A decomposed payoff coordinate inherits explicit bounds on stage utility
and public continuation values. -/
theorem abs_decomposedPayoff_apply_le_of_bounded
    (M : G.PublicMonitoring) (delta : ℝ) (a : Profile G)
    (w : M.ContinuationAssignment) (who : iota)
    {Cu Cw : ℝ}
    (hu : ∀ omega, |G.utility omega who| ≤ Cu)
    (hw : ∀ y, |w y who| ≤ Cw) :
    |M.decomposedPayoff delta a w who| ≤
      |1 - delta| * Cu + |delta| * Cw := by
  rw [decomposedPayoff]
  calc
    |(1 - delta) * G.eu a who +
        delta * expect (M.signalKernel a) (fun y => w y who)| ≤
        |(1 - delta) * G.eu a who| +
          |delta * expect (M.signalKernel a) (fun y => w y who)| :=
      abs_add_le _ _
    _ = |1 - delta| * |G.eu a who| +
        |delta| * |expect (M.signalKernel a) (fun y => w y who)| := by
      rw [abs_mul, abs_mul]
    _ ≤ |1 - delta| * Cu + |delta| * Cw := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          (G.eu_abs_le_of_bounded who hu a) (abs_nonneg _)
      · exact mul_le_mul_of_nonneg_left
          (abs_expect_le_of_abs_le _ _ hw) (abs_nonneg _)

/-- A decomposed unilateral-deviation payoff obeys the same explicit bound. -/
theorem abs_decomposedDeviationPayoff_le_of_bounded
    [DecidableEq iota]
    (M : G.PublicMonitoring) (delta : ℝ) (a : Profile G)
    (w : M.ContinuationAssignment) (who : iota) (dev : G.Strategy who)
    {Cu Cw : ℝ}
    (hu : ∀ omega, |G.utility omega who| ≤ Cu)
    (hw : ∀ y, |w y who| ≤ Cw) :
    |M.decomposedDeviationPayoff delta a w who dev| ≤
      |1 - delta| * Cu + |delta| * Cw := by
  exact M.abs_decomposedPayoff_apply_le_of_bounded delta
    (Function.update a who dev) w who hu hw

/-- Embedding a pure profile in the behavioral mixed extension preserves its
APS decomposed payoff under the same continuation assignment. -/
theorem decomposedPayoff_mixedExtension_pureMixedProfile
    [Fintype iota]
    (M : G.PublicMonitoring) (delta : ℝ) (a : Profile G)
    (w : M.ContinuationAssignment) :
    M.mixedExtension.decomposedPayoff delta (G.pureMixedProfile a) w =
      M.decomposedPayoff delta a w := by
  funext who
  simp only [decomposedPayoff]
  rw [G.mixedExtension_eu_pureMixedProfile,
    Math.PMFProduct.pmfPi_pure, PMF.pure_bind]

/-- Against a pure opponents' profile, a mixed deviation's decomposed payoff
is the expectation of the corresponding pure-deviation decomposed payoffs.
Only the deviating player's utility and continuation coordinate need be
bounded. -/
theorem decomposedDeviationPayoff_mixedExtension_eq_expect_pure_of_bounded
    [Fintype iota] [DecidableEq iota]
    (M : G.PublicMonitoring) (delta : ℝ) (a : Profile G)
    (w : M.ContinuationAssignment) (who : iota)
    (tau : PMF (G.Strategy who))
    {Cu Cw : ℝ}
    (hu : ∀ omega, |G.utility omega who| ≤ Cu)
    (hw : ∀ y, |w y who| ≤ Cw) :
    M.mixedExtension.decomposedDeviationPayoff delta
        (G.pureMixedProfile a) w who tau =
      expect tau (fun dev =>
        M.decomposedDeviationPayoff delta a w who dev) := by
  simp only [decomposedDeviationPayoff]
  rw [G.mixedExtension_eu_update_of_bounded
    (G.pureMixedProfile a) who tau hu]
  simp_rw [← G.pureMixedProfile_update,
    G.mixedExtension_eu_pureMixedProfile]
  change
    (1 - delta) * expect tau
          (fun dev => G.eu (Function.update a who dev) who) +
        delta * expect
          ((Math.PMFProduct.pmfPi
            (Function.update
              (fun i => (PMF.pure (a i) : PMF (G.Strategy i)))
              who tau)).bind M.signalKernel)
          (fun y => w y who) =
      expect tau (fun dev =>
        (1 - delta) * G.eu (Function.update a who dev) who +
          delta * expect (M.signalKernel (Function.update a who dev))
            (fun y => w y who))
  have hproduct (dev : G.Strategy who) :
      Math.PMFProduct.pmfPi
          (Function.update
            (fun i => (PMF.pure (a i) : PMF (G.Strategy i)))
            who (PMF.pure dev)) =
        PMF.pure (Function.update a who dev) := by
    rw [show Function.update
        (fun i => (PMF.pure (a i) : PMF (G.Strategy i)))
        who (PMF.pure dev) =
          fun i => (PMF.pure ((Function.update a who dev) i) :
            PMF (G.Strategy i)) by
      funext i
      by_cases hi : i = who
      · subst hi
        simp
      · simp [Function.update_of_ne hi]]
    exact Math.PMFProduct.pmfPi_pure _
  rw [Math.PMFProduct.pmfPi_update_bind, PMF.bind_bind]
  simp_rw [hproduct, PMF.pure_bind]
  rw [expect_bind_of_bounded tau
    (fun dev => M.signalKernel (Function.update a who dev))
    (fun y => w y who) hw]
  have hstage : ∀ dev, |G.eu (Function.update a who dev) who| ≤ Cu :=
    fun dev => G.eu_abs_le_of_bounded who hu _
  have hcontinuation : ∀ dev,
      |expect (M.signalKernel (Function.update a who dev))
        (fun y => w y who)| ≤ Cw :=
    fun dev => abs_expect_le_of_abs_le _ _ hw
  have hsStage : Summable (fun dev => (tau dev).toReal *
      ((1 - delta) * G.eu (Function.update a who dev) who)) :=
    expect_summable_of_bounded tau _ (fun dev => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hstage dev) (abs_nonneg _))
  have hsContinuation : Summable (fun dev => (tau dev).toReal *
      (delta * expect (M.signalKernel (Function.update a who dev))
        (fun y => w y who))) :=
    expect_summable_of_bounded tau _ (fun dev => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (hcontinuation dev) (abs_nonneg _))
  rw [← expect_const_mul, ← expect_const_mul]
  exact (expect_add_of_summable tau _ _ hsStage hsContinuation).symm

/-- Under bounded utilities and bounded continuation promises, checking APS
enforceability against pure deviations is equivalent to checking every
behavioral mixed deviation. Strategy carriers need only be finite; no chosen
enumerations appear in the statement. -/
theorem isEnforceable_mixedExtension_pureMixedProfile_iff_of_bounded
    [Fintype iota] [DecidableEq iota]
    (M : G.PublicMonitoring) (delta : ℝ) (a : Profile G)
    (w : M.ContinuationAssignment)
    (hu : ∀ who, ∃ C, ∀ omega, |G.utility omega who| ≤ C)
    (hw : M.IsBoundedContinuationAssignment w) :
    M.mixedExtension.IsEnforceable delta (G.pureMixedProfile a) w ↔
      M.IsEnforceable delta a w := by
  constructor
  · intro h who dev
    obtain ⟨Cu, hCu⟩ := hu who
    obtain ⟨Cw, hCw⟩ := hw who
    have hdev := h who (PMF.pure dev)
    rw [M.decomposedDeviationPayoff_mixedExtension_eq_expect_pure_of_bounded
        delta a w who (PMF.pure dev) hCu hCw,
      expect_pure,
      M.decomposedPayoff_mixedExtension_pureMixedProfile] at hdev
    exact hdev
  · intro h who tau
    obtain ⟨Cu, hCu⟩ := hu who
    obtain ⟨Cw, hCw⟩ := hw who
    rw [M.decomposedDeviationPayoff_mixedExtension_eq_expect_pure_of_bounded
        delta a w who tau hCu hCw,
      M.decomposedPayoff_mixedExtension_pureMixedProfile]
    have hdevBound : ∀ dev,
        |M.decomposedDeviationPayoff delta a w who dev| ≤
          |1 - delta| * Cu + |delta| * Cw :=
      fun dev => M.abs_decomposedDeviationPayoff_le_of_bounded
        delta a w who dev hCu hCw
    have hpayoffBound : ∀ _ : G.Strategy who,
        |M.decomposedPayoff delta a w who| ≤
          |1 - delta| * Cu + |delta| * Cw :=
      fun _ => M.abs_decomposedPayoff_apply_le_of_bounded
        delta a w who hCu hCw
    calc
      expect tau (fun dev =>
          M.decomposedDeviationPayoff delta a w who dev)
          ≤ expect tau (fun _ => M.decomposedPayoff delta a w who) :=
        Math.ProbabilityMassFunction.expect_mono_of_pointwise_bounded
          tau _ _ (fun dev => h who dev) hdevBound hpayoffBound
      _ = M.decomposedPayoff delta a w who := expect_const _ _

/-- Finite outcomes and public signals supply the boundedness assumptions for
the pure-deviation reduction automatically. -/
theorem isEnforceable_mixedExtension_pureMixedProfile_iff
    [Fintype iota] [DecidableEq iota]
    [Finite G.Outcome]
    (M : G.PublicMonitoring) [Finite M.Signal]
    (delta : ℝ) (a : Profile G) (w : M.ContinuationAssignment) :
    M.mixedExtension.IsEnforceable delta (G.pureMixedProfile a) w ↔
      M.IsEnforceable delta a w := by
  apply M.isEnforceable_mixedExtension_pureMixedProfile_iff_of_bounded
    delta a w
  · intro who
    exact Math.Probability.exists_abs_bound_of_finite
      (fun omega => G.utility omega who)
  · exact M.isBoundedContinuationAssignment_of_finite w

end PublicMonitoring
end KernelGame
end GameTheory
