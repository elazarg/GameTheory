/-
# Weak preferences over outcome laws

Preferences are explicit arguments, never typeclass instances: one form is
routinely studied under several preferences. Preference laws such as
reflexivity are named properties of a particular relation, not fields of the
relation's type.

## Argument orientation

`weaklyPrefers agent preferred alternative` means `agent` weakly prefers
`preferred` to `alternative`. Every public definition below names its two law
arguments, so reversing them is a visible error rather than a silent change of
concept.
-/

import GameTheory.Probability.FinDist

namespace GameTheory

open Probability

universe ua uo uo'

/-- A weak preference over outcome laws, held by each agent. -/
abbrev WeakPreference (Agent : Type ua) (Outcome : Type uo) :=
  Agent → FinDist Outcome → FinDist Outcome → Prop

namespace Preference

variable {Agent : Type ua} {Outcome : Type uo} {Outcome' : Type uo'}

/-- Every agent weakly prefers a law to itself. Required exactly when a theorem
treats a no-op as an allowed deviation. -/
def Reflexive (weaklyPrefers : WeakPreference Agent Outcome) : Prop :=
  ∀ agent law, weaklyPrefers agent law law

/-- Weak preference chains compose. -/
def Transitive (weaklyPrefers : WeakPreference Agent Outcome) : Prop :=
  ∀ agent preferred middle alternative,
    weaklyPrefers agent preferred middle →
    weaklyPrefers agent middle alternative →
    weaklyPrefers agent preferred alternative

/-- Every pair of laws is comparable. -/
def Total (weaklyPrefers : WeakPreference Agent Outcome) : Prop :=
  ∀ agent preferred alternative,
    weaklyPrefers agent preferred alternative ∨ weaklyPrefers agent alternative preferred

/-- The strict part of a weak preference. -/
def strict (weaklyPrefers : WeakPreference Agent Outcome) : WeakPreference Agent Outcome :=
  fun agent preferred alternative =>
    weaklyPrefers agent preferred alternative ∧ ¬ weaklyPrefers agent alternative preferred

theorem strict_le {weaklyPrefers : WeakPreference Agent Outcome}
    {agent : Agent} {preferred alternative : FinDist Outcome}
    (h : strict weaklyPrefers agent preferred alternative) :
    weaklyPrefers agent preferred alternative := h.1

theorem strict_irrefl (weaklyPrefers : WeakPreference Agent Outcome)
    (agent : Agent) (law : FinDist Outcome) :
    ¬ strict weaklyPrefers agent law law := fun h => h.2 h.1

theorem strict_asymm {weaklyPrefers : WeakPreference Agent Outcome}
    {agent : Agent} {preferred alternative : FinDist Outcome}
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
def Weaker (weaker stronger : WeakPreference Agent Outcome) : Prop :=
  ∀ agent preferred alternative,
    stronger agent preferred alternative → weaker agent preferred alternative

theorem Weaker.refl (weaklyPrefers : WeakPreference Agent Outcome) :
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
def coalition (weaklyPrefers : WeakPreference Agent Outcome) :
    WeakPreference { members : Finset Agent // members.Nonempty } Outcome :=
  fun coalition preferred alternative =>
    ∃ member ∈ coalition.1, weaklyPrefers member preferred alternative

@[simp]
theorem coalition_apply (weaklyPrefers : WeakPreference Agent Outcome)
    (coalition' : { members : Finset Agent // members.Nonempty })
    (preferred alternative : FinDist Outcome) :
    coalition weaklyPrefers coalition' preferred alternative =
      ∃ member ∈ coalition'.1, weaklyPrefers member preferred alternative := rfl

/-- If one member weakly prefers the status quo then the members do not all
strictly gain. This direction needs no assumption on the preference. -/
theorem not_forall_strict_of_coalition {weaklyPrefers : WeakPreference Agent Outcome}
    {coalition' : { members : Finset Agent // members.Nonempty }}
    {preferred alternative : FinDist Outcome}
    (h : coalition weaklyPrefers coalition' preferred alternative) :
    ¬ ∀ member ∈ coalition'.1, strict weaklyPrefers member alternative preferred := by
  obtain ⟨member, hmember, hpref⟩ := h
  exact fun hall => (hall member hmember).2 hpref

/-- The converse holds exactly when the preference is total: without totality a
member may be incomparable, which blocks both "weakly prefers the status quo"
and "strictly gains". -/
theorem coalition_iff_not_forall_strict (weaklyPrefers : WeakPreference Agent Outcome)
    (htotal : Total weaklyPrefers)
    (coalition' : { members : Finset Agent // members.Nonempty })
    (preferred alternative : FinDist Outcome) :
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
