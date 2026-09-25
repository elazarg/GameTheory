/-
# Passing continuation optimality to assessment limits

The approximating deviations may obey restrictions that disappear in the
limit. This is the analytic step used to remove positive trembles; it does
not assume that the limit assessment is rational.
-/

import GameTheory.Analysis.Protocol.BehavioralConvergence

noncomputable section

namespace GameTheory.Protocol.InformationModel

open Filter GameTheory.Math.Probability

universe uι us ua up uq uk

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]
    {E : ExecutionProtocol.{uι, us, ua} ι}
    {M : InformationModel.{uι, us, ua, up, uq, uk} E}

/-- Full continuation-policy optimality passes to a pointwise assessment limit
for bounded payoffs, without finite state, history, or action carriers. Every
alternative must have a convergent sequence of allowed approximating deviations. -/
theorem BehavioralAssessment.isSequentiallyRationalWithin_of_converging_deviations_bounded
    {sequence : ℕ → M.BehavioralAssessment} {target : M.BehavioralAssessment}
    (hstrategy : ∀ i info, PMFConvergesPointwise
      (fun n => (sequence n).strategy i info) (target.strategy i info))
    (hbelief : ∀ i site, PMFConvergesPointwise
      (fun n => (sequence n).belief i site) (target.belief i site))
    (repair : ℕ → (i : ι) → M.BehavioralPolicy i → M.BehavioralPolicy i)
    (hrepair : ∀ i alternative info, PMFConvergesPointwise
      (fun n => repair n i alternative info) (alternative info))
    (payoff : ι → E.History → ℝ) (fuel : ℕ)
    (bound : ι → ℝ) (hbound : ∀ i history, |payoff i history| ≤ bound i)
    (hoptimal : ∀ n i site alternative,
      ((sequence n).continuationContext site (payoff i) fuel).value
          (repair n i alternative)
          (payoffIntegrable_of_bounded _ _ (hbound i)) ≤
        ((sequence n).continuationContext site (payoff i) fuel).value
          ((sequence n).strategy i)
          (payoffIntegrable_of_bounded _ _ (hbound i))) :
    target.IsSequentiallyRationalWithin payoff fuel := by
  intro i site
  simp only [BehavioralAssessment.IsSequentiallyRationalAt,
    Context.IsLocallyOptimal]
  refine ⟨payoffIntegrable_of_bounded _ _ (hbound i), ?_, ?_⟩
  · intro alternative _
    exact payoffIntegrable_of_bounded _ _ (hbound i)
  · intro alternative _ hincumbent halternative
    have hnonneg : 0 ≤ bound i :=
      (abs_nonneg (payoff i E.initHistory)).trans (hbound i E.initHistory)
    have hdeviation := M.continuationContext_value_tendsto_of_bounded
      hstrategy i site (hbelief i site) (hrepair i alternative)
      (payoff i) fuel (bound i) hnonneg (hbound i)
    have hbaseline := M.continuationContext_value_tendsto_of_bounded
      hstrategy i site (hbelief i site) (hstrategy i)
      (payoff i) fuel (bound i) hnonneg (hbound i)
    have hlimit := le_of_tendsto_of_tendsto hdeviation hbaseline
      (Eventually.of_forall fun n => hoptimal n i site alternative)
    simpa only [Context.value, expect_proof_irrel] using hlimit

/-- On finite history carriers, full continuation-policy optimality passes to the
limit when every deviation can be approximated by deviations allowed at the corresponding
approximating assessments. All inequalities concern the canonical contexts. -/
theorem BehavioralAssessment.isSequentiallyRationalWithin_of_converging_deviations
    [Fintype E.History]
    {sequence : ℕ → M.BehavioralAssessment} {target : M.BehavioralAssessment}
    (hstrategy : ∀ i info, PMFConvergesPointwise
      (fun n => (sequence n).strategy i info) (target.strategy i info))
    (hbelief : ∀ i site, PMFConvergesPointwise
      (fun n => (sequence n).belief i site) (target.belief i site))
    (repair : ℕ → (i : ι) → M.BehavioralPolicy i → M.BehavioralPolicy i)
    (hrepair : ∀ i alternative info, PMFConvergesPointwise
      (fun n => repair n i alternative info) (alternative info))
    (payoff : ι → E.History → ℝ) (fuel : ℕ)
    (hoptimal : ∀ n i site alternative,
      ((sequence n).continuationContext site (payoff i) fuel).value
          (repair n i alternative)
          (payoffIntegrable_of_finite _ (payoff i)) ≤
        ((sequence n).continuationContext site (payoff i) fuel).value
          ((sequence n).strategy i)
          (payoffIntegrable_of_finite _ (payoff i))) :
    target.IsSequentiallyRationalWithin payoff fuel := by
  let bound (i : ι) := ∑ history : E.History, |payoff i history|
  have hbound (i : ι) (history : E.History) : |payoff i history| ≤ bound i := by
    exact Finset.single_le_sum (fun other _ => abs_nonneg (payoff i other))
      (Finset.mem_univ history)
  exact BehavioralAssessment.isSequentiallyRationalWithin_of_converging_deviations_bounded
    hstrategy hbelief repair hrepair payoff fuel bound hbound hoptimal

end GameTheory.Protocol.InformationModel
