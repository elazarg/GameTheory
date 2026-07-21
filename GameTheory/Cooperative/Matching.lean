/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Math.Probability

/-!
# Stable Matching

Formalizes two-sided matching markets (Gale-Shapley, 1962). Players on
two sides of a market are matched one-to-one. A matching is stable if
no unmatched pair would both prefer to be matched with each other.

## Main definitions

* `MatchingMarket` — a two-sided matching market with preferences
* `MatchingMarket.IsMatching` — a valid one-to-one matching
* `MatchingMarket.IsBlockingPair` — a pair that blocks a matching
* `MatchingMarket.IsStable` — a stable matching (no blocking pairs)

## Main results

* `stable_respects_mutual_top` — mutual top choices must be matched in
    any stable matching
-/

namespace GameTheory

open Math.Probability

/-- A two-sided matching market. -/
structure MatchingMarket (α β : Type) where
  /-- Preference of `a ∈ α` for `b ∈ β`. -/
  prefA : α → β → ℤ
  /-- Preference of `b ∈ β` for `a ∈ α`. -/
  prefB : β → α → ℤ
  /-- Reservation value for α agents. -/
  reserveA : α → ℤ
  /-- Reservation value for β agents. -/
  reserveB : β → ℤ

namespace MatchingMarket

variable {α β : Type}

/-- A matching is injective: each β-agent is matched to at most one α-agent. -/
def IsMatching (μ : α → Option β) : Prop :=
  ∀ a₁ a₂ b, μ a₁ = some b → μ a₂ = some b → a₁ = a₂

/-- A blocking pair. -/
def IsBlockingPair (M : MatchingMarket α β) (μ : α → Option β)
    (a : α) (b : β) : Prop :=
  (∀ b', μ a = some b' → M.prefA a b > M.prefA a b') ∧
  (μ a = none → M.prefA a b > M.reserveA a) ∧
  (∀ a', μ a' = some b → M.prefB b a > M.prefB b a') ∧
  ((∀ a', μ a' ≠ some b) → M.prefB b a > M.reserveB b)

/-- Every assigned `α`-agent weakly prefers the assignment to remaining
unmatched. -/
def IsIndividuallyRationalA (M : MatchingMarket α β)
    (μ : α → Option β) : Prop :=
  ∀ a b, μ a = some b → M.reserveA a ≤ M.prefA a b

/-- Every assigned `β`-agent weakly prefers the assignment to remaining
unmatched. -/
def IsIndividuallyRationalB (M : MatchingMarket α β)
    (μ : α → Option β) : Prop :=
  ∀ a b, μ a = some b → M.reserveB b ≤ M.prefB b a

/-- Every possible partner is strictly preferred to remaining unmatched on
both sides of the market. -/
def HasCompleteAcceptability (M : MatchingMarket α β) : Prop :=
  (∀ a b, M.reserveA a < M.prefA a b) ∧
    ∀ b a, M.reserveB b < M.prefB b a

theorem hasCompleteAcceptability_reserveA_ne
    {M : MatchingMarket α β} (h : M.HasCompleteAcceptability) :
    ∀ a b, M.reserveA a ≠ M.prefA a b :=
  fun a b => ne_of_lt (h.1 a b)

theorem hasCompleteAcceptability_reserveB_ne
    {M : MatchingMarket α β} (h : M.HasCompleteAcceptability) :
    ∀ b a, M.reserveB b ≠ M.prefB b a :=
  fun b a => ne_of_lt (h.2 b a)

/-- A stable matching: valid, individually rational, no blocking pairs. -/
def IsStable (M : MatchingMarket α β) (μ : α → Option β) : Prop :=
  IsMatching μ ∧
  (∀ a b, μ a = some b → M.prefA a b ≥ M.reserveA a ∧
    M.prefB b a ≥ M.reserveB b) ∧
  ¬∃ a b, M.IsBlockingPair μ a b

theorem IsStable.isIndividuallyRationalA {M : MatchingMarket α β}
    {μ : α → Option β} (h : M.IsStable μ) :
    M.IsIndividuallyRationalA μ :=
  fun a b hab => (h.2.1 a b hab).1

theorem IsStable.isIndividuallyRationalB {M : MatchingMarket α β}
    {μ : α → Option β} (h : M.IsStable μ) :
    M.IsIndividuallyRationalB μ :=
  fun a b hab => (h.2.1 a b hab).2

/-- Stable matchings of a market, bundled as a subtype. -/
abbrev StableMatching (M : MatchingMarket α β) : Type :=
  { μ : α → Option β // M.IsStable μ }

namespace StableMatching

instance (M : MatchingMarket α β) : CoeFun M.StableMatching (fun _ => α → Option β) where
  coe μ := μ.1

theorem ext {M : MatchingMarket α β} {μ ν : M.StableMatching} (h : ∀ a, μ a = ν a) :
    μ = ν :=
  Subtype.ext (funext h)

end StableMatching

/-- The empty matching is a valid matching. -/
theorem empty_isMatching : IsMatching (fun (_ : α) => (none : Option β)) := by
  intro _ _ b h₁; exact absurd h₁ (by simp)

/-- If every agent on the proposing side prefers being unmatched, the empty
matching is stable: no agent on that side is willing to form a blocking pair. -/
theorem empty_stable_if_all_prefer_unmatched (M : MatchingMarket α β)
    (hA : ∀ a b, M.reserveA a > M.prefA a b) :
    M.IsStable (fun _ => none) := by
  refine ⟨empty_isMatching, ?_, ?_⟩
  · intro _ _ h; exact absurd h (by simp)
  · intro ⟨a, b, hblock⟩
    exact absurd (hblock.2.1 rfl) (not_lt.mpr (le_of_lt (hA a b)))

/-- Mutual strict top choices must be matched in any stable matching. -/
theorem stable_respects_mutual_top
    (M : MatchingMarket α β)
    (μ : α → Option β)
    (a : α) (b : β)
    (ha_top : ∀ b', b' ≠ b → M.prefA a b > M.prefA a b')
    (ha_ir : M.prefA a b > M.reserveA a)
    (hb_top : ∀ a', a' ≠ a → M.prefB b a > M.prefB b a')
    (hb_ir : M.prefB b a > M.reserveB b)
    (hstable : M.IsStable μ) :
    μ a = some b := by
  by_contra h
  apply hstable.2.2
  exact ⟨a, b, by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro b' hb'; exact ha_top b' (fun heq => h (heq ▸ hb'))
    · intro _; exact ha_ir
    · intro a' ha'; exact hb_top a' (fun heq => by subst heq; exact h ha')
    · intro _; exact hb_ir⟩

/-- If `a` is matched to `b` in a stable matching, both weakly prefer the
    match to being unmatched. -/
theorem stable_ir (M : MatchingMarket α β) (μ : α → Option β)
    (hstable : M.IsStable μ) (a : α) (b : β) (hab : μ a = some b) :
    M.prefA a b ≥ M.reserveA a ∧ M.prefB b a ≥ M.reserveB b :=
  hstable.2.1 a b hab

end MatchingMarket

end GameTheory
