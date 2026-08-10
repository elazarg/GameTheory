/-
# Local counterfactual regret matching

This module connects canonical Protocol counterfactual action regret to the
existing Blackwell/Hannan regret-matching process.  It proves both a finite
squared-distance estimate and asymptotic approach to the nonpositive orthant.
It is local learning at one information site, not global CFR exploitability.
-/

import GameTheory.Analysis.Approachability
import GameTheory.Analysis.Protocol.CounterfactualRegret

noncomputable section

namespace GameTheory.Protocol

open Filter GameTheory Probability Protocol
open GameTheory.Analysis.Approachability
open GameTheoryMath.Approachability GameTheoryMath.OrthantProjection

universe uι us ua up uq uk

variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)

namespace InformationModel

/-- The vector of D45 pure-action regrets at one information site. -/
def localCounterfactualRegretVector
    [Fintype ι] [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) [DecidableEq (M.InfoState who)]
    (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    [Fintype (M.Choice who site.1)]
    (payoff : E.History → ℝ) (fuel : ℕ) :
    EuclideanSpace ℝ (M.Choice who site.1) :=
  WithLp.toLp 2 fun choice =>
    M.counterfactualActionRegret strategy who site payoff fuel choice

/-- Any exact Protocol realization of the ordinary regret-payoff vector
inherits the finite regret-matching estimate.  The premise is pointwise in
every current action law and environment; it does not assume convergence. -/
theorem counterfactualRegretMatch_sq_infDist_avg_le
    {Q : Type*}
    [Fintype ι] [DecidableEq ι]
    (who : ι) [DecidableEq (M.InfoState who)]
    (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    [Fintype (M.Choice who site.1)] [Nonempty (M.Choice who site.1)]
    (utility : M.Choice who site.1 → Q → ℝ)
    (strategyOf : FinDist (M.Choice who site.1) → Q →
      (player : ι) → M.BehavioralPolicy player)
    (payoffOf : Q → E.History → ℝ) (fuel : ℕ)
    (hrealize : ∀ law environment,
      localCounterfactualRegretVector M (strategyOf law environment)
          who site (payoffOf environment) fuel =
        regretPayoff utility law environment)
    {bound : ℝ} (hbound0 : 0 ≤ bound)
    (hbound : ∀ law environment,
      ‖regretPayoff utility law environment‖ ≤ bound)
    (environment : ℕ → Q) (t : ℕ) :
    Metric.infDist
        (avgVec
          (fun law current => localCounterfactualRegretVector M
            (strategyOf law current) who site (payoffOf current) fuel)
          regretMatch environment t)
        nonposOrthant ^ 2 * (t : ℝ) ≤ (2 * bound) ^ 2 := by
  have hpayoff :
      (fun law current => localCounterfactualRegretVector M
        (strategyOf law current) who site (payoffOf current) fuel) =
        regretPayoff utility := by
    funext law current
    exact hrealize law current
  rw [hpayoff]
  exact regretMatch_sq_infDist_avg_le utility hbound0 hbound environment t

/-- Under the same exact realization premise, the cumulative local
counterfactual-regret process approaches the nonpositive orthant. -/
theorem counterfactualRegretMatch_approaches
    {Q : Type*}
    [Fintype ι] [DecidableEq ι]
    (who : ι) [DecidableEq (M.InfoState who)]
    (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    [Fintype (M.Choice who site.1)] [Nonempty (M.Choice who site.1)]
    (utility : M.Choice who site.1 → Q → ℝ)
    (strategyOf : FinDist (M.Choice who site.1) → Q →
      (player : ι) → M.BehavioralPolicy player)
    (payoffOf : Q → E.History → ℝ) (fuel : ℕ)
    (hrealize : ∀ law environment,
      localCounterfactualRegretVector M (strategyOf law environment)
          who site (payoffOf environment) fuel =
        regretPayoff utility law environment)
    {bound : ℝ} (hbound0 : 0 ≤ bound)
    (hbound : ∀ law environment,
      ‖regretPayoff utility law environment‖ ≤ bound)
    (environment : ℕ → Q) :
    Tendsto
      (fun t => Metric.infDist
        (avgVec
          (fun law current => localCounterfactualRegretVector M
            (strategyOf law current) who site (payoffOf current) fuel)
          regretMatch environment t)
        nonposOrthant)
      atTop (nhds 0) := by
  have hpayoff :
      (fun law current => localCounterfactualRegretVector M
        (strategyOf law current) who site (payoffOf current) fuel) =
        regretPayoff utility := by
    funext law current
    exact hrealize law current
  rw [hpayoff]
  exact regretMatch_approaches utility hbound0 hbound environment

end InformationModel

end GameTheory.Protocol
