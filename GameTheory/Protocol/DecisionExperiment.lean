/-
# Terminal decision experiments with retained outcomes

A policy observes a summary of a hidden state and chooses a public action.
Utilities concern a retained fact and that action. Optimality is the canonical
context comparison over whole policies, with defined expectations required
for the incumbent and every alternative. Extended values remain comparable.

When the observation determines the retained fact on the prior support,
lifting and conditional averaging preserve the complete sets of optimal
retained outcome laws for every utility. This does not require finite carriers,
a finite-support prior or bounded payoffs. The result concerns terminal
decisions; it does not assert sequential-equilibrium abstraction for arbitrary
multiplayer protocols.
-/

import GameTheory.Math.Probability.ObservationAbstraction
import GameTheory.Protocol.ContextTransport

noncomputable section

namespace GameTheory.DecisionExperiment
open GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Math.Probability.ObservationAbstraction
variable {State Signal Action Fact : Type*}

/-- A terminal decision context over the retained fact and public action. -/
def context (prior : PMF State) (observe : State → Signal) (fact : State → Fact)
    (utility : Fact → Action → ℝ) : Context (Signal → PMF Action) (Fact × Action) where
  outcome := responseLaw prior observe fact
  continuation pair := utility pair.1 pair.2

/-- Whole-policy optimality is the canonical guarded context comparison. -/
abbrev IsOptimal (prior : PMF State) (observe : State → Signal) (fact : State → Fact)
    (utility : Fact → Action → ℝ) (policy : Signal → PMF Action) : Prop :=
  (context prior observe fact utility).IsLocallyOptimal Set.univ policy

/-- Recovering the retained fact makes an abstract optimum remain optimal under full information. -/
theorem isOptimal_lift (prior : PMF State) (observe : State → Signal) (fact : State → Fact)
    (determines : Determines prior observe fact) (utility : Fact → Action → ℝ)
    (policy : Signal → PMF Action) (optimal : IsOptimal prior observe fact utility policy) :
    IsOptimal prior id fact utility (fun state => policy (observe state)) := by
  refine optimal.of_outcome_coverage rfl rfl ?_
  intro alternative _
  exact ⟨averagePolicy prior observe alternative, Set.mem_univ _,
    (averagePolicy_response_law prior observe fact determines alternative).symm⟩

/-- A fully informed optimum averages to an abstract optimum with the same retained law. -/
theorem isOptimal_average (prior : PMF State) (observe : State → Signal) (fact : State → Fact)
    (determines : Determines prior observe fact) (utility : Fact → Action → ℝ)
    (policy : State → PMF Action) (optimal : IsOptimal prior id fact utility policy) :
    IsOptimal prior observe fact utility (averagePolicy prior observe policy) := by
  refine optimal.of_outcome_coverage rfl
    (averagePolicy_response_law prior observe fact determines policy) ?_
  intro alternative _
  exact ⟨fun state => alternative (observe state), Set.mem_univ _, rfl⟩

/-- The complete sets of optimal retained outcome laws coincide, including extended values. -/
theorem optimal_response_law_iff (prior : PMF State) (observe : State → Signal) (fact : State →
  Fact)
    (determines : Determines prior observe fact) (utility : Fact → Action → ℝ)
    (law : PMF (Fact × Action)) :
    (∃ policy : Signal → PMF Action, IsOptimal prior observe fact utility policy ∧
      responseLaw prior observe fact policy = law) ↔
    (∃ policy : State → PMF Action, IsOptimal prior id fact utility policy ∧
      responseLaw prior id fact policy = law) := by
  constructor
  · rintro ⟨policy, optimal, same⟩
    exact ⟨fun state => policy (observe state),
      isOptimal_lift prior observe fact determines utility policy optimal, same⟩
  · rintro ⟨policy, optimal, same⟩
    exact ⟨averagePolicy prior observe policy,
      isOptimal_average prior observe fact determines utility policy optimal,
      (averagePolicy_response_law prior observe fact determines policy).trans same⟩

end GameTheory.DecisionExperiment
