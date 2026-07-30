/-
# Aggregating rankings

Social choice ranks alternatives, not laws over them, and no probability appears
anywhere in it. That makes it the cleanest test of whether the preference
vocabulary is really about preferences or was quietly about lotteries: an
aggregation rule takes one ranking per agent and returns one ranking, and every
law it is asked to satisfy — totality, transitivity, the strict part — is the
same law the equilibrium theory uses.

The rule below is pairwise majority, and the theorem it exists for is a
*failure*: individually impeccable rankings can aggregate into a cycle. That
failure is why the subject has impossibility theorems at all.
-/

import GameTheory.Core.Rank
import Mathlib.Data.Fintype.Card

namespace GameTheory

universe ua uα

/-- A rule that turns one ranking per agent into a single social ranking. -/
abbrev Aggregator (Agent : Type ua) (α : Type uα) := Ranking Agent α → α → α → Prop

variable {Agent : Type ua} [Fintype Agent] {α : Type uα}

/-- Pairwise majority: society ranks `preferred` at least as high as
`alternative` when at least as many agents do. Only the two alternatives being
compared are consulted, which is what makes the rule pairwise. -/
def majority (ranks : Ranking Agent α) [∀ agent a b, Decidable (ranks agent a b)] :
    α → α → Prop :=
  fun preferred alternative =>
    (Finset.univ.filter fun agent => ranks agent alternative preferred).card ≤
      (Finset.univ.filter fun agent => ranks agent preferred alternative).card

/-- **Majority rule is total**, whatever the agents think: one of the two counts
is at least the other. Totality is the one Arrovian condition that costs
nothing. -/
theorem total_majority (ranks : Ranking Agent α) [∀ agent a b, Decidable (ranks agent a b)] :
    Rank.Total (majority ranks) := fun _ _ => le_total _ _

end GameTheory
