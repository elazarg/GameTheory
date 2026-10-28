module

/-
# Quotas and responsive matching stability

A capacitated market adds right-side quotas to individual ordinal rankings.
Each cohort is the fiber of the partial assignment. Extended cardinality
bounds enforce finite quotas even when the agent carriers are infinite.
Responsive blocking fills an acceptable vacancy or replaces an inferior
incumbent. One-to-one stability is the unit-quota specialization.
-/

public import GameTheory.Cooperative.Matching.Basic
public import Mathlib.Data.Set.Card

@[expose] public section

namespace GameTheory

universe uLeft uRight

/-- Individual ordinal preferences and intrinsic right-side quotas. -/
structure CapacitatedMarket (Left : Type uLeft) (Right : Type uRight) where
  /-- The existing individual preference data. -/
  rankings : MatchingMarket Left Right
  /-- How many partners each right-side agent may receive. -/
  capacity : Right → ℕ

namespace MatchingMarket

/-- Supply quotas for the right side of an ordinal market. -/
def withCapacities {Left : Type uLeft} {Right : Type uRight}
    (market : MatchingMarket Left Right) (capacity : Right → ℕ) :
    CapacitatedMarket Left Right := ⟨market, capacity⟩

end MatchingMarket

namespace CapacitatedMarket

open MatchingMarket

variable {Left : Type uLeft} {Right : Type uRight}

/-- Every assignment fiber fits its finite quota. -/
def IsFeasible (market : CapacitatedMarket Left Right) (matching : Matching Left Right) : Prop :=
  ∀ right, (cohort matching right).encard ≤ (market.capacity right : ℕ∞)

/-- A pair can fill an acceptable vacancy or replace an inferior incumbent. -/
def IsBlockingPair (market : CapacitatedMarket Left Right) (matching : Matching Left Right)
    (left : Left) (right : Right) : Prop :=
  Preference.strict market.rankings.prefersLeft left (some right) (matching left) ∧
    (((cohort matching right).encard < (market.capacity right : ℕ∞) ∧
      Preference.strict market.rankings.prefersRight right (some left) none) ∨
      ∃ incumbent ∈ cohort matching right,
        Preference.strict market.rankings.prefersRight right (some left) (some incumbent))

/-- Feasible, individually rational assignments with no responsive blocking pair. -/
def IsStable (market : CapacitatedMarket Left Right) (matching : Matching Left Right) : Prop :=
  market.IsFeasible matching ∧ market.rankings.IsIndividuallyRational matching ∧
    ¬ ∃ left right, market.IsBlockingPair matching left right

theorem IsStable.isFeasible {market : CapacitatedMarket Left Right}
    {matching : Matching Left Right} (stable : market.IsStable matching) :
    market.IsFeasible matching := stable.1

theorem IsStable.isIndividuallyRational {market : CapacitatedMarket Left Right}
    {matching : Matching Left Right} (stable : market.IsStable matching) :
    market.rankings.IsIndividuallyRational matching := stable.2.1

theorem IsStable.not_isBlockingPair {market : CapacitatedMarket Left Right}
    {matching : Matching Left Right} (stable : market.IsStable matching)
    (left : Left) (right : Right) : ¬ market.IsBlockingPair matching left right :=
  fun blocks => stable.2.2 ⟨left, right, blocks⟩

theorem IsFeasible.finite_cohort {market : CapacitatedMarket Left Right}
    {matching : Matching Left Right} (feasible : market.IsFeasible matching) (right : Right) :
    (cohort matching right).Finite := Set.finite_of_encard_le_coe (feasible right)

theorem IsFeasible.not_assigned_of_capacity_zero {market : CapacitatedMarket Left Right}
    {matching : Matching Left Right} (feasible : market.IsFeasible matching) {right : Right}
    (zero : market.capacity right = 0) (left : Left) : matching left ≠ some right := by
  have empty : cohort matching right = ∅ := by
    simpa only [zero, Nat.cast_zero, nonpos_iff_eq_zero, Set.encard_eq_zero] using feasible right
  intro assigned
  have member : left ∈ cohort matching right := assigned
  rw [empty] at member
  exact member

/-- Unit quotas recover the ordinary one-to-one assignment invariant. -/
theorem isFeasible_iff_isMatching_of_unitCapacity (market : CapacitatedMarket Left Right)
    (unitCapacity : ∀ right, market.capacity right = 1) (matching : Matching Left Right) :
    market.IsFeasible matching ↔ MatchingMarket.IsMatching matching := by
  simp only [IsFeasible, unitCapacity, Nat.cast_one, Set.encard_le_one_iff, mem_cohort]
  constructor
  · intro feasible first second right firstAssigned secondAssigned
    exact feasible right first second firstAssigned secondAssigned
  · intro valid right first second firstAssigned secondAssigned
    exact valid first second right firstAssigned secondAssigned

end CapacitatedMarket
end GameTheory
