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

/-! ## Social choice functions

An aggregator returns a social ranking.  A social choice function instead
selects one alternative.  Both consume the same canonical `Ranking` profiles;
there is no second preference or profile type.
-/

/-- A social choice function selects one alternative from each ranking
profile.  Its laws below restrict attention to profiles of linear rankings;
the function remains total on malformed inputs so no capability is stored in
its data. -/
abbrev SocialChoiceFunction (Voter : Type ua) (Alternative : Type uα) :=
  Ranking Voter Alternative → Alternative

namespace SocialChoiceFunction

variable {Voter : Type ua} {Alternative : Type uα}

/-- Replace one voter's reported ranking.  Classical decidable equality is an
implementation detail of this proof-facing operation, not a stored capability
of a social choice function. -/
noncomputable def replaceRanking (ranks : Ranking Voter Alternative)
    (voter : Voter) (report : Alternative → Alternative → Prop) :
    Ranking Voter Alternative := by
  classical
  exact fun current => if current = voter then report else ranks current

@[simp]
theorem replaceRanking_self (ranks : Ranking Voter Alternative)
    (voter : Voter) (report : Alternative → Alternative → Prop) :
    replaceRanking ranks voter report voter = report := by
  classical
  simp [replaceRanking]

theorem replaceRanking_of_ne (ranks : Ranking Voter Alternative)
    {voter current : Voter} (hne : current ≠ voter)
    (report : Alternative → Alternative → Prop) :
    replaceRanking ranks voter report current = ranks current := by
  classical
  simp [replaceRanking, hne]

@[simp]
theorem replaceRanking_restore (ranks : Ranking Voter Alternative)
    (voter : Voter) (report : Alternative → Alternative → Prop) :
    replaceRanking (replaceRanking ranks voter report) voter (ranks voter) = ranks := by
  classical
  funext current
  by_cases hcurrent : current = voter
  · subst current
    simp
  · rw [replaceRanking_of_ne _ hcurrent, replaceRanking_of_ne _ hcurrent]

/-- Strategyproofness on the unrestricted domain of linear rankings: under
the true ranking, no voter strictly prefers the outcome reached by a linear
misreport to the truthful outcome. -/
def IsStrategyProof (choice : SocialChoiceFunction Voter Alternative) : Prop :=
  ∀ ranks, Preference.Linear ranks → ∀ voter report, Rank.Linear report →
    ¬ Rank.strict (ranks voter)
      (choice (replaceRanking ranks voter report)) (choice ranks)

/-- Full range on admissible ranking profiles. -/
def IsOnto (choice : SocialChoiceFunction Voter Alternative) : Prop :=
  ∀ alternative, ∃ ranks, Preference.Linear ranks ∧ choice ranks = alternative

/-- A dictator's reported ranking always places the selected alternative
weakly above every alternative.  On a linear ranking this is the unique top
alternative. -/
def IsDictator (choice : SocialChoiceFunction Voter Alternative)
    (dictator : Voter) : Prop :=
  ∀ ranks, Preference.Linear ranks → ∀ alternative,
    ranks dictator (choice ranks) alternative

/-- A dictator's selected alternative equals any supplied top alternative. -/
theorem IsDictator.eq_of_forall_ranks
    {choice : SocialChoiceFunction Voter Alternative} {dictator : Voter}
    (hdictator : choice.IsDictator dictator)
    {ranks : Ranking Voter Alternative} (hlinear : Preference.Linear ranks)
    {alternative : Alternative}
    (htop : ∀ other, ranks dictator alternative other) :
    choice ranks = alternative :=
  (hlinear dictator).2.2.2 _ _
    (hdictator ranks hlinear alternative) (htop (choice ranks))

end SocialChoiceFunction

end GameTheory
