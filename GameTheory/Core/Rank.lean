/-
# Rankings and relation laws

This is the probability-free preference vocabulary. A `Ranking` is merely one
explicit comparison per agent; reflexivity, transitivity, totality, and
antisymmetry are named hypotheses rather than typeclass instances or stored
fields. `Preference` lifts the same laws pointwise to a family of rankings.

Lottery-specific preferences import this module, not conversely. That physical
direction keeps social choice independent of probability as well as
mathematically unrelated to it.
-/

import Mathlib.Data.Finset.Basic

namespace GameTheory

universe ua uα

/-- A comparison of `α`s held by each agent, with no commitment to what an `α`
is. -/
abbrev Ranking (Agent : Type ua) (α : Type uα) := Agent → α → α → Prop

/-! ## One ranking -/

namespace Rank

variable {α : Type uα}

/-- Nothing is worse than itself. -/
def Reflexive (ranks : α → α → Prop) : Prop :=
  ∀ item, ranks item item

/-- Chains compose. -/
def Transitive (ranks : α → α → Prop) : Prop :=
  ∀ preferred middle alternative,
    ranks preferred middle → ranks middle alternative →
      ranks preferred alternative

/-- Every pair is comparable. -/
def Total (ranks : α → α → Prop) : Prop :=
  ∀ preferred alternative,
    ranks preferred alternative ∨ ranks alternative preferred

/-- Two items that rank at least as high as each other are the same. This is
the no-ties law; it is separate from totality because equilibrium preferences
are allowed to be indifferent. -/
def Antisymmetric (ranks : α → α → Prop) : Prop :=
  ∀ preferred alternative,
    ranks preferred alternative → ranks alternative preferred →
      preferred = alternative

/-- A linear weak ranking: reflexive, transitive, total, and without ties.
This is a transparent conjunction of the existing laws, not a second relation
type. -/
def Linear (ranks : α → α → Prop) : Prop :=
  Reflexive ranks ∧ Transitive ranks ∧ Total ranks ∧ Antisymmetric ranks

/-- The strict part: better, and not merely as good. -/
def strict (ranks : α → α → Prop) : α → α → Prop :=
  fun preferred alternative =>
    ranks preferred alternative ∧ ¬ ranks alternative preferred

/-- The symmetric part of a weak ranking. -/
def Indifferent (ranks : α → α → Prop) (first second : α) : Prop :=
  ranks first second ∧ ranks second first

theorem strict_le
    {ranks : α → α → Prop} {preferred alternative : α}
    (h : strict ranks preferred alternative) :
    ranks preferred alternative :=
  h.1

theorem strict_irrefl (ranks : α → α → Prop) (item : α) :
    ¬ strict ranks item item :=
  fun h => h.2 h.1

theorem strict_asymm
    {ranks : α → α → Prop} {preferred alternative : α}
    (h : strict ranks preferred alternative) :
    ¬ strict ranks alternative preferred :=
  fun h' => h.2 h'.1

/-- A total ranking compares any two one way or the other, so failing to rank
one item above another means strictly preferring the second. -/
theorem strict_of_not
    {ranks : α → α → Prop} (htotal : Total ranks)
    {preferred alternative : α}
    (h : ¬ ranks alternative preferred) :
    strict ranks preferred alternative :=
  ⟨(htotal preferred alternative).resolve_right h, h⟩

/-- In a finite nonempty set, a total transitive ranking has a best element.
This is the relation-valued counterpart of taking a maximum; it avoids
re-encoding ordinal preferences by numerical scores. -/
theorem exists_best_finset
    {ranks : α → α → Prop}
    (htrans : Transitive ranks) (htotal : Total ranks)
    {items : Finset α} (hne : items.Nonempty) :
    ∃ best ∈ items, ∀ alternative ∈ items, ranks best alternative := by
  classical
  induction items using Finset.induction_on with
  | empty => simp at hne
  | @insert item items hnotmem ih =>
      by_cases hempty : items.Nonempty
      · obtain ⟨best, hbest, hmax⟩ := ih hempty
        rcases htotal item best with hib | hbi
        · exact ⟨item, Finset.mem_insert_self item items, fun alternative halt => by
            rcases Finset.mem_insert.mp halt with heq | halt
            · subst alternative
              exact (htotal item item).elim id id
            · exact htrans item best alternative hib (hmax alternative halt)⟩
        · exact ⟨best, Finset.mem_insert_of_mem hbest, fun alternative halt => by
            rcases Finset.mem_insert.mp halt with heq | halt
            · subst alternative
              exact hbi
            · exact hmax alternative halt⟩
      · have hitems : items = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
        exact ⟨item, Finset.mem_insert_self item items, fun alternative halt => by
          rw [hitems] at halt
          have heq : alternative = item := by simpa using halt
          subst alternative
          exact (htotal item item).elim id id⟩

/-- Under antisymmetry, a weak comparison between distinct alternatives is
strict. -/
theorem strict_of_le_of_ne
    {ranks : α → α → Prop} (hantisymm : Antisymmetric ranks)
    {preferred alternative : α} (hle : ranks preferred alternative)
    (hne : preferred ≠ alternative) :
    strict ranks preferred alternative :=
  ⟨hle, fun hreverse => hne (hantisymm preferred alternative hle hreverse)⟩

/-- A strict comparison stays strict after a weakly worse alternative. -/
theorem strict_trans
    {ranks : α → α → Prop} (htrans : Transitive ranks)
    {preferred middle alternative : α}
    (hfirst : strict ranks preferred middle)
    (hsecond : ranks middle alternative) :
    strict ranks preferred alternative :=
  ⟨htrans preferred middle alternative hfirst.1 hsecond,
    fun hreverse => hfirst.2 (htrans middle alternative preferred hsecond hreverse)⟩

/-- A weak improvement followed by a strict improvement is strict. -/
theorem trans_strict
    {ranks : α → α → Prop} (htrans : Transitive ranks)
    {preferred middle alternative : α}
    (hfirst : ranks preferred middle)
    (hsecond : strict ranks middle alternative) :
    strict ranks preferred alternative :=
  ⟨htrans preferred middle alternative hfirst hsecond.1,
    fun hreverse => hsecond.2 (htrans alternative preferred middle hreverse hfirst)⟩

end Rank

/-! ## A family of rankings, one per agent -/

namespace Preference

variable {Agent : Type ua} {α : Type uα}

/-- Every agent weakly prefers an item to itself. -/
def Reflexive (weaklyPrefers : Ranking Agent α) : Prop :=
  ∀ agent, Rank.Reflexive (weaklyPrefers agent)

/-- Weak preference chains compose, for every agent. -/
def Transitive (weaklyPrefers : Ranking Agent α) : Prop :=
  ∀ agent, Rank.Transitive (weaklyPrefers agent)

/-- Every agent compares every pair. -/
def Total (weaklyPrefers : Ranking Agent α) : Prop :=
  ∀ agent, Rank.Total (weaklyPrefers agent)

/-- No agent is indifferent between distinct items. -/
def Antisymmetric (weaklyPrefers : Ranking Agent α) : Prop :=
  ∀ agent, Rank.Antisymmetric (weaklyPrefers agent)

/-- Every agent supplies a linear weak ranking. -/
def Linear (weaklyPrefers : Ranking Agent α) : Prop :=
  ∀ agent, Rank.Linear (weaklyPrefers agent)

/-- The strict part of a weak preference. -/
def strict (weaklyPrefers : Ranking Agent α) : Ranking Agent α :=
  fun agent => Rank.strict (weaklyPrefers agent)

theorem strict_le
    {weaklyPrefers : Ranking Agent α}
    {agent : Agent} {preferred alternative : α}
    (h : strict weaklyPrefers agent preferred alternative) :
    weaklyPrefers agent preferred alternative :=
  h.1

theorem strict_irrefl
    (weaklyPrefers : Ranking Agent α)
    (agent : Agent) (item : α) :
    ¬ strict weaklyPrefers agent item item :=
  fun h => h.2 h.1

theorem strict_asymm
    {weaklyPrefers : Ranking Agent α}
    {agent : Agent} {preferred alternative : α}
    (h : strict weaklyPrefers agent preferred alternative) :
    ¬ strict weaklyPrefers agent alternative preferred :=
  fun h' => h.2 h'.1

/-- Pointwise implication between preferences, oriented so that a `Weaker`
preference accepts more equilibria. -/
def Weaker (weaker stronger : Ranking Agent α) : Prop :=
  ∀ agent preferred alternative,
    stronger agent preferred alternative →
      weaker agent preferred alternative

theorem Weaker.refl (weaklyPrefers : Ranking Agent α) :
    Weaker weaklyPrefers weaklyPrefers :=
  fun _ _ _ h => h

/-- Lift a preference to nonempty coalitions: a coalition weakly prefers the
status quo exactly when at least one member does. -/
def coalition (weaklyPrefers : Ranking Agent α) :
    Ranking { members : Finset Agent // members.Nonempty } α :=
  fun coalition preferred alternative =>
    ∃ member ∈ coalition.1,
      weaklyPrefers member preferred alternative

@[simp]
theorem coalition_apply
    (weaklyPrefers : Ranking Agent α)
    (coalition' : { members : Finset Agent // members.Nonempty })
    (preferred alternative : α) :
    coalition weaklyPrefers coalition' preferred alternative =
      ∃ member ∈ coalition'.1,
        weaklyPrefers member preferred alternative :=
  rfl

/-- If one member weakly prefers the status quo then the members do not all
strictly gain. This direction needs no assumption on the preference. -/
theorem not_forall_strict_of_coalition
    {weaklyPrefers : Ranking Agent α}
    {coalition' : { members : Finset Agent // members.Nonempty }}
    {preferred alternative : α}
    (h : coalition weaklyPrefers coalition' preferred alternative) :
    ¬ ∀ member ∈ coalition'.1,
      strict weaklyPrefers member alternative preferred := by
  obtain ⟨member, hmember, hpref⟩ := h
  exact fun hall => (hall member hmember).2 hpref

/-- Under totality, the coalition lift is equivalent to saying that not every
member strictly gains. -/
theorem coalition_iff_not_forall_strict
    (weaklyPrefers : Ranking Agent α)
    (htotal : Total weaklyPrefers)
    (coalition' : { members : Finset Agent // members.Nonempty })
    (preferred alternative : α) :
    coalition weaklyPrefers coalition' preferred alternative ↔
      ¬ ∀ member ∈ coalition'.1,
        strict weaklyPrefers member alternative preferred := by
  refine ⟨not_forall_strict_of_coalition, fun hnotall => ?_⟩
  by_contra hnone
  refine hnotall fun member hmember => ?_
  have hno : ¬ weaklyPrefers member preferred alternative :=
    fun hpref => hnone ⟨member, hmember, hpref⟩
  exact
    ⟨(htotal member alternative preferred).resolve_right hno, hno⟩

end Preference

end GameTheory
