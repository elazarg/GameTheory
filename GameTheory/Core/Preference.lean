/-
# Weak preferences

Preferences are explicit arguments, never typeclass instances: one form is
routinely studied under several preferences. Preference laws such as
reflexivity are named properties of a particular relation, not fields of the
relation's type.

Most of that vocabulary is relation algebra and says nothing about what is being
compared, so it is stated for an arbitrary carrier. `WeakPreference` names the
case the equilibrium theory uses, comparing outcome *laws*; a theory that ranks
outcomes themselves, as social choice does, gets the same reflexivity,
transitivity, totality, strict part, and coalition lifting without a parallel
copy. Only the two definitions that genuinely need a law — convexity under
mixing, and pullback along a relabeling — are stated at that level.

## Argument orientation

`weaklyPrefers agent preferred alternative` means `agent` weakly prefers
`preferred` to `alternative`. Every public definition below names its two law
arguments, so reversing them is a visible error rather than a silent change of
concept.
-/

import GameTheory.Probability.FinDist

namespace GameTheory

open Probability

universe ua uα uo uo'

/-- A comparison of `α`s held by each agent, with no commitment to what an `α`
is. -/
abbrev Ranking (Agent : Type ua) (α : Type uα) := Agent → α → α → Prop

/-- A weak preference over outcome laws, held by each agent. -/
abbrev WeakPreference (Agent : Type ua) (Outcome : Type uo) := Ranking Agent (FinDist Outcome)

/-! ## One ranking

The laws below are properties of a single comparison. Mathlib states the same
laws as typeclasses, which is the one thing a preference may not be here: a
single carrier is routinely studied under several preferences at once, so the
relation must stay an argument. -/

namespace Rank

variable {α : Type uα}

/-- Nothing is worse than itself. Required exactly when a theorem treats a
no-op as an allowed deviation. -/
def Reflexive (ranks : α → α → Prop) : Prop := ∀ item, ranks item item

/-- Chains compose. -/
def Transitive (ranks : α → α → Prop) : Prop :=
  ∀ preferred middle alternative,
    ranks preferred middle → ranks middle alternative → ranks preferred alternative

/-- Every pair is comparable. -/
def Total (ranks : α → α → Prop) : Prop :=
  ∀ preferred alternative, ranks preferred alternative ∨ ranks alternative preferred

/-- The strict part: better, and not merely as good. -/
def strict (ranks : α → α → Prop) : α → α → Prop :=
  fun preferred alternative => ranks preferred alternative ∧ ¬ ranks alternative preferred

theorem strict_le {ranks : α → α → Prop} {preferred alternative : α}
    (h : strict ranks preferred alternative) : ranks preferred alternative := h.1

theorem strict_irrefl (ranks : α → α → Prop) (item : α) : ¬ strict ranks item item :=
  fun h => h.2 h.1

theorem strict_asymm {ranks : α → α → Prop} {preferred alternative : α}
    (h : strict ranks preferred alternative) : ¬ strict ranks alternative preferred :=
  fun h' => h.2 h'.1

/-- A total ranking compares any two one way or the other, so failing to rank
one item above another means strictly preferring the second. -/
theorem strict_of_not {ranks : α → α → Prop} (htotal : Total ranks)
    {preferred alternative : α}
    (h : ¬ ranks alternative preferred) : strict ranks preferred alternative :=
  ⟨(htotal preferred alternative).resolve_right h, h⟩

end Rank

/-! ## A family of rankings, one per agent

Each law below is its single-ranking counterpart holding for every agent, and is
*definitionally* that: a theorem stated for one ranking transfers by
application. -/

namespace Preference

variable {Agent : Type ua} {α : Type uα} {Outcome : Type uo} {Outcome' : Type uo'}

/-- Every agent weakly prefers a law to itself. -/
def Reflexive (weaklyPrefers : Ranking Agent α) : Prop :=
  ∀ agent, Rank.Reflexive (weaklyPrefers agent)

/-- Weak preference chains compose, for every agent. -/
def Transitive (weaklyPrefers : Ranking Agent α) : Prop :=
  ∀ agent, Rank.Transitive (weaklyPrefers agent)

/-- Every agent compares every pair. -/
def Total (weaklyPrefers : Ranking Agent α) : Prop :=
  ∀ agent, Rank.Total (weaklyPrefers agent)

/-- The strict part of a weak preference. -/
def strict (weaklyPrefers : Ranking Agent α) : Ranking Agent α :=
  fun agent => Rank.strict (weaklyPrefers agent)

theorem strict_le {weaklyPrefers : Ranking Agent α}
    {agent : Agent} {preferred alternative : α}
    (h : strict weaklyPrefers agent preferred alternative) :
    weaklyPrefers agent preferred alternative := h.1

theorem strict_irrefl (weaklyPrefers : Ranking Agent α)
    (agent : Agent) (item : α) :
    ¬ strict weaklyPrefers agent item item := fun h => h.2 h.1

theorem strict_asymm {weaklyPrefers : Ranking Agent α}
    {agent : Agent} {preferred alternative : α}
    (h : strict weaklyPrefers agent preferred alternative) :
    ¬ strict weaklyPrefers agent alternative preferred := fun h' => h.2 h'.1

/-- A preference respects mixing: comparing two pairs the same way compares
their mixtures the same way. Expected utility satisfies it, and it is what makes
a solution concept defined by comparing laws a *convex* set. Nothing forces a
weak preference to be convex, so it is a hypothesis rather than a field. -/
def Convex (weaklyPrefers : WeakPreference Agent Outcome) : Prop :=
  ∀ (agent : Agent) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (firstPreferred firstAlternative secondPreferred secondAlternative : FinDist Outcome),
    weaklyPrefers agent firstPreferred firstAlternative →
    weaklyPrefers agent secondPreferred secondAlternative →
      weaklyPrefers agent (FinDist.mix t h0 h1 firstPreferred secondPreferred)
        (FinDist.mix t h0 h1 firstAlternative secondAlternative)

/-- Pointwise implication between preferences, oriented so that a `Weaker`
preference accepts more equilibria. -/
def Weaker (weaker stronger : Ranking Agent α) : Prop :=
  ∀ agent preferred alternative,
    stronger agent preferred alternative → weaker agent preferred alternative

theorem Weaker.refl (weaklyPrefers : Ranking Agent α) :
    Weaker weaklyPrefers weaklyPrefers := fun _ _ _ h => h

/-- Lift a preference to nonempty coalitions: a coalition weakly prefers the
status quo exactly when at least one member does.

Under a **total** preference this is Aumann's condition "the members do not all
strictly gain"; see `coalition_iff_not_forall_strict`. The two readings come
apart for a partial preference: a deviation leaving every member *incomparable*
to the status quo is refused by this definition even though nobody strictly
gains. That is the deliberate choice, because `WeakPreference` is allowed to be
partial and the safe reading of a coalitional objection is "somebody is not
made worse off". Only the forward implication
(`not_forall_strict_of_coalition`) is unconditional. -/
def coalition (weaklyPrefers : Ranking Agent α) :
    Ranking { members : Finset Agent // members.Nonempty } α :=
  fun coalition preferred alternative =>
    ∃ member ∈ coalition.1, weaklyPrefers member preferred alternative

@[simp]
theorem coalition_apply (weaklyPrefers : Ranking Agent α)
    (coalition' : { members : Finset Agent // members.Nonempty })
    (preferred alternative : α) :
    coalition weaklyPrefers coalition' preferred alternative =
      ∃ member ∈ coalition'.1, weaklyPrefers member preferred alternative := rfl

/-- If one member weakly prefers the status quo then the members do not all
strictly gain. This direction needs no assumption on the preference. -/
theorem not_forall_strict_of_coalition {weaklyPrefers : Ranking Agent α}
    {coalition' : { members : Finset Agent // members.Nonempty }}
    {preferred alternative : α}
    (h : coalition weaklyPrefers coalition' preferred alternative) :
    ¬ ∀ member ∈ coalition'.1, strict weaklyPrefers member alternative preferred := by
  obtain ⟨member, hmember, hpref⟩ := h
  exact fun hall => (hall member hmember).2 hpref

/-- The converse holds exactly when the preference is total: without totality a
member may be incomparable, which blocks both "weakly prefers the status quo"
and "strictly gains". -/
theorem coalition_iff_not_forall_strict (weaklyPrefers : Ranking Agent α)
    (htotal : Total weaklyPrefers)
    (coalition' : { members : Finset Agent // members.Nonempty })
    (preferred alternative : α) :
    coalition weaklyPrefers coalition' preferred alternative ↔
      ¬ ∀ member ∈ coalition'.1, strict weaklyPrefers member alternative preferred := by
  refine ⟨not_forall_strict_of_coalition, fun hnotall => ?_⟩
  by_contra hnone
  refine hnotall fun member hmember => ?_
  have hno : ¬ weaklyPrefers member preferred alternative :=
    fun hpref => hnone ⟨member, hmember, hpref⟩
  exact ⟨(htotal member alternative preferred).resolve_right hno, hno⟩

/-- Pull a preference back along an outcome relabeling. -/
def comapOutcome (relabel : Outcome → Outcome')
    (weaklyPrefers : WeakPreference Agent Outcome') : WeakPreference Agent Outcome :=
  fun agent preferred alternative =>
    weaklyPrefers agent (preferred.map relabel) (alternative.map relabel)

@[simp]
theorem comapOutcome_apply (relabel : Outcome → Outcome')
    (weaklyPrefers : WeakPreference Agent Outcome')
    (agent : Agent) (preferred alternative : FinDist Outcome) :
    comapOutcome relabel weaklyPrefers agent preferred alternative =
      weaklyPrefers agent (preferred.map relabel) (alternative.map relabel) := rfl

end Preference

end GameTheory
