/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Dominance.DominanceRelations
import Math.Fintype

/-!
# Undominated strategies

Undominated-strategy rationality for the weak-with-strict-witness dominance
relation `KernelGame.WeaklyStrictlyDominates`. This is not the same as
`KernelGame.WeaklyDominates`, which is the reflexive `≥`-everywhere preorder.

This file provides undominated strategies/profiles for that relation, and the
finite ascent lemma used to move from an arbitrary dominated strategy to an
undominated strategy that dominates it.
-/

namespace GameTheory

open Math.Probability

namespace KernelGame

variable {ι : Type} [DecidableEq ι] {G : KernelGame ι}

/-- A strategy is undominated when no other strategy dominates it. -/
def IsUndominated (G : KernelGame ι) (who : ι) (s : G.Strategy who) : Prop :=
  ∀ t : G.Strategy who, ¬ G.WeaklyStrictlyDominates who t s

/-- Profiles whose every coordinate is undominated. -/
def undominatedProfiles (G : KernelGame ι) : Set (Profile G) :=
  {σ | ∀ i, G.IsUndominated i (σ i)}

theorem IsUndominated.not_dominated {who : ι} {s t : G.Strategy who}
    (h : G.IsUndominated who s) : ¬ G.WeaklyStrictlyDominates who t s :=
  h t

/-- A weakly dominant strategy is undominated under weak dominance with a
strict witness. -/
theorem IsDominant.isUndominated {who : ι} {s : G.Strategy who}
    (hdom : G.IsDominant who s) : G.IsUndominated who s := by
  intro t hts
  obtain ⟨_, σ, hstrict⟩ := hts
  have hle := hdom σ t
  linarith

@[simp] theorem mem_undominatedProfiles {σ : Profile G} :
    σ ∈ G.undominatedProfiles ↔ ∀ i, G.IsUndominated i (σ i) := Iff.rfl

/-- On a finite strategy set, every strategy is either itself undominated or is
dominated by an undominated strategy. -/
theorem exists_undominated_or_dominator {who : ι} [Finite (G.Strategy who)]
    (s : G.Strategy who) :
    ∃ t : G.Strategy who,
      G.IsUndominated who t ∧ (t = s ∨ G.WeaklyStrictlyDominates who t s) := by
  obtain ⟨t, htmax, htcand⟩ :=
    Math.exists_maximal_or_rel_of_finite_trans_irrefl
      (G.WeaklyStrictlyDominates who)
      (fun a b c hab hbc => WeaklyStrictlyDominates.trans hab hbc)
      (fun a => WeaklyStrictlyDominates.irrefl (G := G) (who := who) a)
      s
  exact ⟨t, htmax, htcand⟩

/-- On a finite strategy set, any dominated strategy is dominated by an
undominated strategy. -/
theorem exists_undominated_dominator {who : ι} [Finite (G.Strategy who)]
    {s : G.Strategy who}
    (hdominated : ∃ t : G.Strategy who, G.WeaklyStrictlyDominates who t s) :
    ∃ t : G.Strategy who,
      G.IsUndominated who t ∧ G.WeaklyStrictlyDominates who t s := by
  obtain ⟨t, htmax, hts⟩ :=
    Math.exists_maximal_rel_of_finite_trans_irrefl
      (G.WeaklyStrictlyDominates who)
      (fun a b c hab hbc => WeaklyStrictlyDominates.trans hab hbc)
      (fun a => WeaklyStrictlyDominates.irrefl (G := G) (who := who) a)
      hdominated
  exact ⟨t, htmax, hts⟩

/-- Every finite nonempty strategy set has at least one undominated strategy. -/
theorem exists_undominated_strategy (who : ι)
    [Nonempty (G.Strategy who)] [Finite (G.Strategy who)] :
    ∃ s : G.Strategy who, G.IsUndominated who s := by
  obtain ⟨s⟩ := ‹Nonempty (G.Strategy who)›
  obtain ⟨t, htundom, _⟩ := exists_undominated_or_dominator (G := G) (who := who) s
  exact ⟨t, htundom⟩

/-- Finite games with nonempty strategy sets have at least one undominated
profile. -/
theorem undominatedProfiles_nonempty
    [∀ i, Nonempty (G.Strategy i)] [∀ i, Finite (G.Strategy i)] :
    G.undominatedProfiles.Nonempty := by
  classical
  choose s hs using fun i => exists_undominated_strategy (G := G) i
  exact ⟨s, hs⟩

end KernelGame

/- A countable strict-order counterexample showing the finite-ascent lemmas
above genuinely need `Finite`. The isolated point `none` is the only undominated
element, while the chain `some 0 < some 1 < some 2 < ...` has no undominated
dominator. -/
namespace InfiniteAscentCounterexample

/-- Strategies for the infinite-ascent counterexample: an isolated target point
and an infinite ascending chain. -/
abbrev Strategy := Option ℕ

/-- The isolated target point. -/
abbrev target : Strategy := none

/-- `some m` dominates `some n` exactly when it is higher in the infinite chain;
the target is isolated. -/
def Dominates : Strategy → Strategy → Prop
  | some m, some n => n < m
  | _, _ => False

/-- Maximality for the counterexample relation. -/
def IsMaximal (s : Strategy) : Prop :=
  ∀ t : Strategy, ¬ Dominates t s

theorem dominates_trans {a b c : Strategy}
    (hab : Dominates a b) (hbc : Dominates b c) :
    Dominates a c := by
  cases a with
  | none =>
      simp [Dominates] at hab
  | some m =>
      cases b with
      | none =>
          simp [Dominates] at hab
      | some n =>
          cases c with
          | none =>
              simp [Dominates] at hbc
          | some k =>
              have hkn : k < n := by
                simpa [Dominates] using hbc
              have hnm : n < m := by
                simpa [Dominates] using hab
              simpa [Dominates] using Nat.lt_trans hkn hnm

theorem dominates_irrefl (s : Strategy) :
    ¬ Dominates s s := by
  cases s <;> simp [Dominates]

theorem isMaximal_iff_eq_target {s : Strategy} :
    IsMaximal s ↔ s = target := by
  constructor
  · intro h
    cases s with
    | none => rfl
    | some n =>
        exfalso
        exact h (some (n + 1)) (by simp [Dominates])
  · intro hs
    subst hs
    intro t
    cases t <;> simp [Dominates]

theorem zero_dominated :
    ∃ t : Strategy, Dominates t (some 0) := by
  exact ⟨some 1, by simp [Dominates]⟩

/-- The finite-ascent conclusion fails without finiteness: `some 0` is
dominated, but none of its dominators is maximal. -/
theorem zero_dominated_without_maximal_dominator :
    ¬ ∃ t : Strategy, IsMaximal t ∧ Dominates t (some 0) := by
  rintro ⟨t, htmax, htdom⟩
  have ht : t = target := isMaximal_iff_eq_target.mp htmax
  subst t
  simp [Dominates] at htdom

/-- A packaged witness that the dominated-to-undominated-dominator ascent lemma
requires a finiteness hypothesis. -/
theorem finite_ascent_conclusion_fails :
    (∃ t : Strategy, Dominates t (some 0)) ∧
      ¬ ∃ t : Strategy, IsMaximal t ∧ Dominates t (some 0) :=
  ⟨zero_dominated, zero_dominated_without_maximal_dominator⟩

end InfiniteAscentCounterexample

end GameTheory
