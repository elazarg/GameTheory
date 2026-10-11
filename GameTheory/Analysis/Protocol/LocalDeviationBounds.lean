/- Copyright (c) 2026 VegasCore contributors. Released under MIT; see NOTICE. -/

import GameTheory.Analysis.Protocol.RestrictionIncentives
import GameTheory.Math.Probability.ExpectationMixture

/-! # Bounds for local continuation deviations

When consequential decisions are not revisited, pure-choice gain bounds cover
every local lottery. Mixing a local lottery with a reference costs at most
the mixing weight times the terminal payoff range. Values at nonterminal
histories are unrestricted. These comparisons use actual terminal continuation
contexts, independently of Bayesian consistency or rationality.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability

variable {Player : Type*} [DecidableEq Player]
  {T : ExecutionProtocol Player} {N : InformationModel T}
  [T.FiniteMovers] [Finite T.History]

/-- A uniform pure-choice gain bound covers every local lottery. -/
theorem BehavioralAssessment.withLaw_gain_le_of_choice_gain_le
    (assessment : N.BehavioralAssessment) (actsOnce : N.ActsOnceWhereItMatters)
    (certificate : T.WellFoundedHistories) {who : Player}
    [DecidableEq (N.InfoState who)] (site : N.InformationSite who)
    (payoff : T.History → ℝ) (bound : ℝ)
    (choiceGain : ∀ choice : N.Choice who site.1,
      (assessment.continuationContext certificate site payoff).value
          ((assessment.strategy who).withLaw site.1 (PMF.pure choice)) -
        (assessment.continuationContext certificate site payoff).value
          (assessment.strategy who) ≤ bound)
    (law : PMF (N.Choice who site.1)) :
    (assessment.continuationContext certificate site payoff).value
        ((assessment.strategy who).withLaw site.1 law) -
      (assessment.continuationContext certificate site payoff).value
        (assessment.strategy who) ≤ bound := by
  have : Finite (N.Choice who site.1) :=
    InformationSite.finite_choice N who site
  have expand (installed : PMF (N.Choice who site.1)) :=
    BehavioralAssessment.continuationContext_withLaw_eq_expect actsOnce assessment certificate
      site (assessment.strategy who) installed payoff
  rw [expand]
  have committed := expect_le_const law
    (fun choice => (assessment.continuationContext certificate site payoff).value
      ((assessment.strategy who).commit site.1 choice)) (payoffIntegrable_of_finite _ _)
    ((assessment.continuationContext certificate site payoff).value
      (assessment.strategy who) + bound) fun choice _ => by
        have single := choiceGain choice
        rw [expand, expect_pure] at single
        linarith
  linarith

/-- Mixing weight `weight` on a reference law changes the local gain by at
most `weight * (upper - lower)`. Only terminal payoff values are bounded. -/
theorem BehavioralAssessment.withLaw_gain_le_mix_add
    (assessment : N.BehavioralAssessment) (actsOnce : N.ActsOnceWhereItMatters)
    (certificate : T.WellFoundedHistories) {who : Player}
    [DecidableEq (N.InfoState who)] (site : N.InformationSite who)
    (payoff : T.History → ℝ) (lower upper : ℝ)
    (payoffRange : ∀ final, T.terminal final.state →
      lower ≤ payoff final ∧ payoff final ≤ upper)
    (reference law : PMF (N.Choice who site.1))
    (weight : ℝ) (nonnegative : 0 ≤ weight) (small : weight ≤ 1) :
    (assessment.continuationContext certificate site payoff).value
        ((assessment.strategy who).withLaw site.1 law) -
      (assessment.continuationContext certificate site payoff).value
        (assessment.strategy who) ≤
    (assessment.continuationContext certificate site payoff).value
        ((assessment.strategy who).withLaw site.1
          (mix weight nonnegative small reference law)) -
      (assessment.continuationContext certificate site payoff).value
        (assessment.strategy who) + weight * (upper - lower) := by
  have bounded final (terminal : T.terminal final.state) :
      |payoff final| ≤ max |lower| |upper| := by
    have range := payoffRange final terminal
    have first := (abs_le.mp (le_max_left |lower| |upper|)).1
    have second := (abs_le.mp (le_max_right |lower| |upper|)).2
    exact abs_le.mpr ⟨first.trans range.1, range.2.trans second⟩
  have values (installed : PMF (N.Choice who site.1)) :
      lower ≤ (assessment.continuationContext certificate site payoff).value
          ((assessment.strategy who).withLaw site.1 installed) ∧
        (assessment.continuationContext certificate site payoff).value
          ((assessment.strategy who).withLaw site.1 installed) ≤ upper := by
    have integrable := assessment.continuationContext_integrable_of_bounded_terminal
      certificate site payoff (max |lower| |upper|) bounded
      ((assessment.strategy who).withLaw site.1 installed)
    have range final (supported : final ∈
        ((assessment.continuationContext certificate site payoff).outcome
          ((assessment.strategy who).withLaw site.1 installed)).support) :=
      payoffRange final (assessment.continuationContext_support_terminal certificate site payoff
        ((assessment.strategy who).withLaw site.1 installed) final supported)
    constructor
    · rw [← expect_constant
        ((assessment.continuationContext certificate site payoff).outcome
          ((assessment.strategy who).withLaw site.1 installed)) lower]
      exact expect_mono (fun final supported => (range final supported).1)
        (payoffIntegrable_constant _ _) integrable
    · exact expect_le_const _ _ integrable upper (fun final supported => (range final supported).2)
  have committed (choice : N.Choice who site.1) :
      |(assessment.continuationContext certificate site payoff).value
        ((assessment.strategy who).commit site.1 choice)| ≤ max |lower| |upper| := by
    apply expect_abs_le_of_bounded_on_support
    intro final supported
    exact bounded final (assessment.continuationContext_support_terminal certificate site payoff
      ((assessment.strategy who).commit site.1 choice) final supported)
  have expand (installed : PMF (N.Choice who site.1)) :=
    BehavioralAssessment.continuationContext_withLaw_eq_expect actsOnce assessment certificate
      site (assessment.strategy who) installed payoff
  have mixed := expand (mix weight nonnegative small reference law)
  rw [expect_mix _ _ _ _ _ _ (payoffIntegrable_of_bounded reference _ committed)
    (payoffIntegrable_of_bounded law _ committed), ← expand reference, ← expand law] at mixed
  have first := mul_le_mul_of_nonneg_left (values law).2 nonnegative
  have second := mul_le_mul_of_nonneg_left (values reference).1 nonnegative
  linarith

/-- Approximate optimality among full-menu trembling components bounds every
local deviation, including laws outside the trembling menu. -/
theorem BehavioralAssessment.withLaw_gain_le_of_trembling_component_bound
    (assessment : N.BehavioralAssessment) (actsOnce : N.ActsOnceWhereItMatters)
    (certificate : T.WellFoundedHistories) {who : Player}
    [DecidableEq (N.InfoState who)] (site : N.InformationSite who)
    (payoff : T.History → ℝ) (lower upper : ℝ)
    (payoffRange : ∀ final, T.terminal final.state →
      lower ≤ payoff final ∧ payoff final ≤ upper)
    (reference : PMF (N.Choice who site.1))
    (weight : ℝ) (nonnegative : 0 ≤ weight) (small : weight ≤ 1)
    (error : ℝ)
    (memberBound : ∀ alternative : PMF (N.Choice who site.1),
      (assessment.continuationContext certificate site payoff).value
          ((assessment.strategy who).withLaw site.1
            (alternative.bind fun choice =>
              mix weight nonnegative small reference (PMF.pure choice))) -
        (assessment.continuationContext certificate site payoff).value
          (assessment.strategy who) ≤ error)
    (law : PMF (N.Choice who site.1)) :
    (assessment.continuationContext certificate site payoff).value
        ((assessment.strategy who).withLaw site.1 law) -
      (assessment.continuationContext certificate site payoff).value
        (assessment.strategy who) ≤ error + weight * (upper - lower) := by
  have comparison := memberBound law
  rw [bind_mix_pure] at comparison
  exact (assessment.withLaw_gain_le_mix_add actsOnce certificate site payoff lower upper
    payoffRange reference law weight nonnegative small).trans
      (add_le_add comparison le_rfl)

end GameTheory.Protocol.InformationModel
