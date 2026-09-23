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

/-- Full continuation-policy optimality passes to the limit when every
deviation can be approximated by deviations allowed at the corresponding
approximating assessments. All inequalities concern the canonical contexts. -/
theorem BehavioralAssessment.isSequentiallyRationalWithin_of_converging_deviations
    [Fintype E.State] [Fintype E.History] [∀ i, Fintype (E.Action i)]
    [∀ i (site : M.InformationSite i), Fintype (M.InformationHistory i site.1)]
    {sequence : ℕ → M.BehavioralAssessment} {target : M.BehavioralAssessment}
    (hstrategy : ∀ i info, FinDistConvergesPointwise
      (fun n => (sequence n).strategy i info) (target.strategy i info))
    (hbelief : ∀ i site, FinDistConvergesPointwise
      (fun n => (sequence n).belief i site) (target.belief i site))
    (repair : ℕ → (i : ι) → M.BehavioralPolicy i → M.BehavioralPolicy i)
    (hrepair : ∀ i alternative info, FinDistConvergesPointwise
      (fun n => repair n i alternative info) (alternative info))
    (payoff : ι → E.History → ℝ) (fuel : ℕ)
    (hoptimal : ∀ n i site alternative,
      ((sequence n).continuationContext site (payoff i) fuel).value
          (repair n i alternative) ≤
        ((sequence n).continuationContext site (payoff i) fuel).value
          ((sequence n).strategy i)) :
    target.IsSequentiallyRationalWithin payoff fuel := by
  intro i site alternative _
  have hdeviation := M.continuationContext_value_tendsto hstrategy i site
    (hbelief i site) (hrepair i alternative) (payoff i) fuel
  have hbaseline := M.continuationContext_value_tendsto hstrategy i site
    (hbelief i site) (hstrategy i) (payoff i) fuel
  exact le_of_tendsto_of_tendsto hdeviation hbaseline
    (Eventually.of_forall fun n => hoptimal n i site alternative)

end GameTheory.Protocol.InformationModel
