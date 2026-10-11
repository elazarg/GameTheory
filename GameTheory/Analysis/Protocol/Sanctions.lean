/- Copyright (c) 2026 VegasCore contributors. Released under MIT; see NOTICE. -/

import GameTheory.Analysis.Enforcement
import GameTheory.Protocol.BehavioralAssessment

/-! # Sequential incentives from incremental penalties

Bounds apply to each whole continuation deviation at the assessment's actual
beliefs. Additional collection risk includes collection under the prescribed
plan. No finite player carrier, runtime monitor or consistent belief system is
constructed by these incentive certificates.
-/

noncomputable section
namespace GameTheory
open Math.Probability

namespace Protocol.InformationModel.BehavioralAssessment

variable {ι : Type} [DecidableEq ι]
  {E : ExecutionProtocol ι} [E.FiniteMovers] {M : InformationModel E}

/-- A deterrence certificate for every whole continuation deviation establishes
local sequential rationality in the actual assessment context. Every bound is
at this information set; an initialized detection bound alone does not suffice. -/
theorem isSequentiallyRationalAt_of_incremental_penalty
    (assessment : M.BehavioralAssessment) {who : ι} (site : M.InformationSite who)
    (base : E.History → ℝ) (sanction : Set E.History) (fuel : Nat) {penalty : ℝ}
    (penalty_nonneg : 0 ≤ penalty)
    (gain probability : M.BehavioralPolicy who → ℝ)
    (integrable : ∀ policy, (assessment.truncatedContinuationContext site base fuel).IntegrableAt
        policy)
    (gain_bound : ∀ alternative,
      (assessment.truncatedContinuationContext site base fuel).value alternative -
        (assessment.truncatedContinuationContext site base fuel).value (assessment.strategy who) ≤
          gain alternative)
    (detection : ∀ alternative, probability alternative ≤
      (((assessment.truncatedContinuationContext site base fuel).outcome alternative).toOuterMeasure
        sanction).toReal -
      (((assessment.truncatedContinuationContext site base fuel).outcome
        (assessment.strategy who)).toOuterMeasure sanction).toReal)
    (sufficient : ∀ alternative, gain alternative ≤ probability alternative * penalty) :
    assessment.IsSequentiallyRationalAt site
      (assessment.truncatedContinuationContext site
        (penalizedPayoff base sanction penalty) fuel) := by
  have sanctioned (policy : M.BehavioralPolicy who) :
      (assessment.truncatedContinuationContext site
        (penalizedPayoff base sanction penalty) fuel).IntegrableAt policy :=
    payoffIntegrable_penalizedPayoff (integrable policy) sanction penalty
  refine (Context.isLocallyOptimal_iff_of_integrable (sanctioned _)
    fun alternative _ => sanctioned alternative).mpr fun alternative _ => ?_
  let comparison : IncentiveComparison E.History := {
    prescribed := (assessment.truncatedContinuationContext site base fuel).outcome
      (assessment.strategy who)
    alternative := (assessment.truncatedContinuationContext site base fuel).outcome alternative }
  exact (IncentiveComparison.holds_iff_of_integrable comparison
    (penalizedPayoff base sanction penalty)
    (payoffIntegrable_penalizedPayoff (integrable (assessment.strategy who))
      sanction penalty)
    (payoffIntegrable_penalizedPayoff (integrable alternative) sanction penalty)).mp
      ((Enforcement.holds_iff_incremental_sanction comparison base sanction penalty
        (integrable (assessment.strategy who)) (integrable alternative)).mpr
        ((gain_bound alternative).trans ((sufficient alternative).trans
          (mul_le_mul_of_nonneg_right (detection alternative) penalty_nonneg))))

end Protocol.InformationModel.BehavioralAssessment
end GameTheory
