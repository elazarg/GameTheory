module

/-
# Stable matchings preserve unmatched agents in incomplete unequal markets

Two ordinary proposers and receivers admit distinct stable assignments. A
third proposer is unacceptable and prefers staying unmatched. Both stable
assignments therefore leave exactly that proposer unmatched. Transposing the
same partial matchings gives the corresponding unmatched-receiver example.
-/

public import GameTheory.Cooperative.GaleShapley.Unmatched
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace GameTheory.Tests.MatchingUnmatched

open MatchingMarket

def leftScore : Option Bool → Option Bool → ℕ
  | none, none => 2
  | none, some false => 1
  | none, some true => 0
  | some _, none => 0
  | some left, some right => if right = left then 2 else 1

def rightScore (right : Bool) : Option (Option Bool) → ℕ
  | none => 1
  | some none => 0
  | some (some left) => if left = right then 2 else 3

def market : MatchingMarket (Option Bool) Bool where
  prefersLeft left first second := leftScore left second ≤ leftScore left first
  prefersRight right first second := rightScore right second ≤ rightScore right first

private theorem linear_of_score {α : Type*} (score : α → ℕ)
    (injective : Function.Injective score) :
    Rank.Linear (fun first second => score second ≤ score first) :=
  ⟨fun _ => le_rfl, fun _ _ _ h₁ h₂ => h₂.trans h₁,
    fun _ _ => le_total _ _, fun _ _ h₁ h₂ => injective (le_antisymm h₂ h₁)⟩

theorem market_linear : market.HasLinearPreferences := by
  constructor
  · intro left
    apply linear_of_score
    intro first second equality
    fin_cases left <;> fin_cases first <;> fin_cases second <;> simp_all [leftScore]
  · intro right
    apply linear_of_score
    intro first second equality
    fin_cases right <;> fin_cases first <;> fin_cases second <;> simp_all [rightScore]

def diagonal : Matching (Option Bool) Bool
  | none => none
  | some left => some left

def crossed : Matching (Option Bool) Bool
  | none => none
  | some left => some (!left)

theorem diagonal_stable : market.IsStable diagonal := by
  unfold IsStable IsMatching IsIndividuallyRational IsBlockingPair
    Preference.strict Rank.strict market
  decide

theorem crossed_stable : market.IsStable crossed := by
  unfold IsStable IsMatching IsIndividuallyRational IsBlockingPair
    Preference.strict Rank.strict market
  decide

theorem stable_endpoints_distinct : diagonal ≠ crossed := by
  intro equal
  have same := congrFun equal (some false)
  simp [diagonal, crossed] at same

/-- Complete acceptability is false: the extra proposer prefers the outside
option to either receiver. -/
theorem not_completeAcceptability : ¬ market.HasCompleteAcceptability := by
  intro acceptable
  have falsePreference := (acceptable.1 none false).1
  norm_num [market, leftScore] at falsePreference

theorem unequal_market_sizes :
    Fintype.card (Option Bool) ≠ Fintype.card Bool := by decide

/-- Every stable assignment leaves precisely the additional proposer unmatched. -/
theorem unmatched_proposer_exact {matching : Matching (Option Bool) Bool}
    (stable : market.IsStable matching) (left : Option Bool) :
    matching left = none ↔ left = none := by
  have same := market.stable_unmatched_left_iff market_linear stable diagonal_stable left
  cases left <;> simpa [diagonal] using same

theorem transposed_endpoints_stable :
    market.transpose.IsStable (transposeMatching diagonal) ∧
      market.transpose.IsStable (transposeMatching crossed) :=
  ⟨diagonal_stable.transpose, crossed_stable.transpose⟩

/-- Every stable assignment in the transposed unequal market leaves precisely
the additional receiver unmatched. -/
theorem unmatched_receiver_exact {matching : Matching Bool (Option Bool)}
    (stable : market.transpose.IsStable matching) (right : Option Bool) :
    (∀ left, matching left ≠ some right) ↔ right = none := by
  have same := market.transpose.stable_unmatched_right_iff market_linear.transpose
    stable diagonal_stable.transpose right
  have baseline : (∀ left, transposeMatching diagonal left ≠ some right) ↔ right = none := by
    rw [← transposeMatching_apply_none_iff, transposeMatching_transposeMatching
      diagonal diagonal_stable.isMatching]
    cases right <;> simp [diagonal]
  exact same.trans baseline

/-- The reciprocal maps retain partial assignments without assuming perfectness. -/
theorem reciprocal_outside_option :
    transposeMatching (transposeMatching diagonal) none = none := by
  rw [transposeMatching_transposeMatching diagonal diagonal_stable.isMatching]
  rfl

end GameTheory.Tests.MatchingUnmatched
