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

/-- Install the learner's current law at one information site of an otherwise
fixed behavioral profile.  This is a transparent specialization of the sole
public profile update and the transport-free `BehavioralPolicy.withLaw`. -/
def strategyWithLocalLaw
    [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) [DecidableEq (M.InfoState who)]
    (site : M.InformationSite who)
    (law : FinDist (M.Choice who site.1)) :
    (player : ι) → M.BehavioralPolicy player :=
  Profile.update (sig := M.behavioralSignature) strategy who
    ((strategy who).withLaw site.1 law)

@[simp]
theorem strategyWithLocalLaw_same
    [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) [DecidableEq (M.InfoState who)]
    (site : M.InformationSite who)
    (law : FinDist (M.Choice who site.1)) :
    strategyWithLocalLaw M strategy who site law who site.1 = law := by
  rw [strategyWithLocalLaw, Profile.update_same,
    BehavioralPolicy.withLaw_self]

@[simp]
theorem strategyWithLocalLaw_of_ne
    [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) [DecidableEq (M.InfoState who)]
    (site : M.InformationSite who)
    (law : FinDist (M.Choice who site.1))
    {other : ι} (hne : other ≠ who) :
    strategyWithLocalLaw M strategy who site law other = strategy other := by
  exact Profile.update_of_ne (sig := M.behavioralSignature) strategy _ hne

/-- The pure-commitment counterfactual utility is independent of which law is
currently installed at the focal site. -/
theorem counterfactualActionUtility_strategyWithLocalLaw
    [Fintype ι] [DecidableEq ι]
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) [DecidableEq (M.InfoState who)]
    (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    (law : FinDist (M.Choice who site.1))
    (payoff : E.History → ℝ) (fuel : ℕ)
    (choice : M.Choice who site.1) :
    counterfactualActionUtility M
        (strategyWithLocalLaw M strategy who site law)
        who site payoff fuel choice =
      counterfactualActionUtility M strategy who site payoff fuel choice := by
  unfold counterfactualActionUtility
  rw [show strategyWithLocalLaw M strategy who site law who =
      (strategy who).withLaw site.1 law by
        rw [strategyWithLocalLaw, Profile.update_same],
    BehavioralPolicy.withLaw_commit]
  exact M.counterfactualContinuationValue_eq_of_eq_off
    (fun other hne => strategyWithLocalLaw_of_ne M strategy who site law hne)
      site ((strategy who).commit site.1 choice) payoff fuel

/-- Generic realization of the local vector at any qualifying strategy: its
current site law is the mixed action and pure-commitment continuation values
are the ordinary finite-action utilities. -/
theorem localCounterfactualRegretVector_eq_regretPayoff_actionUtility
    [Fintype ι] [DecidableEq ι]
    (hactsOnce : M.ActsOnceWhereItMatters)
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) [DecidableEq (M.InfoState who)]
    (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    [Fintype (M.Choice who site.1)]
    (hallNonterminal : InformationSite.AllNonterminal M site)
    (payoff : E.History → ℝ) (fuel : ℕ) :
    localCounterfactualRegretVector M strategy who site payoff (fuel + 1) =
      regretPayoff
        (fun choice (_environment : Unit) =>
          counterfactualActionUtility M strategy who site
            payoff (fuel + 1) choice)
        (strategy who site.1) () := by
  ext choice
  rw [regretPayoff_ofLp]
  exact M.counterfactualActionRegret_eq_sub_expect hactsOnce strategy who
    site hallNonterminal payoff fuel choice

/-- Installing an arbitrary current law in a fixed environment realizes the
ordinary regret-payoff vector for the environment's pure-commitment
counterfactual utilities. -/
theorem localCounterfactualRegretVector_strategyWithLocalLaw
    {Q : Type*}
    [Fintype ι] [DecidableEq ι]
    (hactsOnce : M.ActsOnceWhereItMatters)
    (strategy : (player : ι) → M.BehavioralPolicy player)
    (who : ι) [DecidableEq (M.InfoState who)]
    (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    [Fintype (M.Choice who site.1)]
    (hallNonterminal : InformationSite.AllNonterminal M site)
    (law : FinDist (M.Choice who site.1))
    (payoff : E.History → ℝ) (fuel : ℕ) (environment : Q) :
    localCounterfactualRegretVector M
        (strategyWithLocalLaw M strategy who site law)
        who site payoff (fuel + 1) =
      regretPayoff
        (fun choice (_current : Q) =>
          counterfactualActionUtility M strategy who site
            payoff (fuel + 1) choice)
        law environment := by
  ext choice
  rw [localCounterfactualRegretVector, regretPayoff_ofLp,
    WithLp.ofLp_toLp]
  rw [M.counterfactualActionRegret_eq_sub_expect hactsOnce
      (strategyWithLocalLaw M strategy who site law) who site
        hallNonterminal payoff fuel,
    strategyWithLocalLaw_same]
  rw [M.counterfactualActionUtility_strategyWithLocalLaw strategy who site
    law payoff (fuel + 1) choice]
  congr 1
  apply FinDist.expect_congr
  intro current _
  exact M.counterfactualActionUtility_strategyWithLocalLaw strategy who site
    law payoff (fuel + 1) current

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
