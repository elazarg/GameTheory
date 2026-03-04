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

/-- A two-sided matching market. Agents of type `α` are matched to
    agents of type `β`. Preferences are integers (higher = more preferred). -/
structure MatchingMarket (α β : Type) where
  /-- Preference of `a ∈ α` for `b ∈ β`. -/
  prefA : α → β → ℤ
  /-- Preference of `b ∈ β` for `a ∈ α`. -/
  prefB : β → α → ℤ
  /-- Reservation value (utility of being unmatched) for α agents. -/
  reserveA : α → ℤ
  /-- Reservation value for β agents. -/
  reserveB : β → ℤ

namespace MatchingMarket

variable {α β : Type}

/-- A matching is injective: each β-agent is matched to at most one α-agent. -/
def IsMatching (μ : α → Option β) : Prop :=
  ∀ a₁ a₂ b, μ a₁ = some b → μ a₂ = some b → a₁ = a₂

/-- A blocking pair: `a` and `b` both strictly prefer each other to their
    current assignment. -/
def IsBlockingPair (M : MatchingMarket α β) (μ : α → Option β)
    (a : α) (b : β) : Prop :=
  -- a prefers b to their current match (or being unmatched)
  (∀ b', μ a = some b' → M.prefA a b > M.prefA a b') ∧
  (μ a = none → M.prefA a b > M.reserveA a) ∧
  -- b prefers a to their current partner (or being unmatched)
  (∀ a', μ a' = some b → M.prefB b a > M.prefB b a') ∧
  ((∀ a', μ a' ≠ some b) → M.prefB b a > M.reserveB b)

/-- A stable matching: valid, individually rational, no blocking pairs. -/
def IsStable (M : MatchingMarket α β) (μ : α → Option β) : Prop :=
  IsMatching μ ∧
  (∀ a b, μ a = some b → M.prefA a b ≥ M.reserveA a ∧
    M.prefB b a ≥ M.reserveB b) ∧
  ¬∃ a b, M.IsBlockingPair μ a b

/-- The empty matching is a valid matching. -/
theorem empty_isMatching : IsMatching (fun (_ : α) => (none : Option β)) := by
  intro _ _ b h₁; exact absurd h₁ (by simp)

/-- If all agents prefer being unmatched, the empty matching is stable. -/
theorem empty_stable_if_all_prefer_unmatched (M : MatchingMarket α β)
    (hA : ∀ a b, M.reserveA a > M.prefA a b)
    (_hB : ∀ b a, M.reserveB b > M.prefB b a) :
    M.IsStable (fun _ => none) := by
  refine ⟨empty_isMatching, ?_, ?_⟩
  · intro _ _ h; exact absurd h (by simp)
  · intro ⟨a, b, hblock⟩
    exact absurd (hblock.2.1 rfl) (not_lt.mpr (le_of_lt (hA a b)))

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Mutual strict top choices must be matched in any stable matching. -/
theorem stable_respects_mutual_top [DecidableEq α] [DecidableEq β]
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
    match to being unmatched (individual rationality). -/
theorem stable_ir (M : MatchingMarket α β) (μ : α → Option β)
    (hstable : M.IsStable μ) (a : α) (b : β) (hab : μ a = some b) :
    M.prefA a b ≥ M.reserveA a ∧ M.prefB b a ≥ M.reserveB b :=
  hstable.2.1 a b hab

end MatchingMarket

end GameTheory
