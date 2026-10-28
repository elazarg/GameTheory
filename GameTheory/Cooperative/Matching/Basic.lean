module

/-
# Individual rankings and partial assignments

Two sides rank optional partners, including the outside option. Assignment
validity and individual rationality are separate properties; the preference
data store no finiteness, decidability, utility or order-law assumptions.
-/

public import GameTheory.Core.Rank

@[expose] public section

namespace GameTheory

universe uLeft uRight

/-- Individual ordinal rankings over partners and the outside option. -/
structure MatchingMarket (Left : Type uLeft) (Right : Type uRight) where
  /-- The left agents' weak comparisons, preferred alternative first. -/
  prefersLeft : Ranking Left (Option Right)
  /-- The right agents' weak comparisons, preferred alternative first. -/
  prefersRight : Ranking Right (Option Left)

namespace MatchingMarket

variable {Left : Type uLeft} {Right : Type uRight}

/-- A partial assignment from the left side to optional right partners. -/
abbrev Matching (Left : Type uLeft) (Right : Type uRight) := Left → Option Right

/-- No right partner is assigned to two distinct left agents. -/
def IsMatching (matching : Matching Left Right) : Prop :=
  ∀ first second right,
    matching first = some right → matching second = some right → first = second

/-- The complete fiber assigned to a right-side agent. -/
def cohort (matching : Matching Left Right) (right : Right) : Set Left :=
  {left | matching left = some right}

@[simp]
theorem mem_cohort (matching : Matching Left Right) (left : Left) (right : Right) :
    left ∈ cohort matching right ↔ matching left = some right := Iff.rfl

/-- Each assigned pair weakly prefers its partner to remaining unmatched. -/
def IsIndividuallyRational (market : MatchingMarket Left Right)
    (matching : Matching Left Right) : Prop :=
  ∀ left right, matching left = some right →
    market.prefersLeft left (some right) none ∧ market.prefersRight right (some left) none

/-- Every cross-side pair strictly prefers matching to remaining unmatched. -/
def HasCompleteAcceptability (market : MatchingMarket Left Right) : Prop :=
  (∀ left right, Preference.strict market.prefersLeft left (some right) none) ∧
    ∀ right left, Preference.strict market.prefersRight right (some left) none

theorem empty_isMatching : IsMatching (fun _ : Left => (none : Option Right)) := by
  intro _ _ right equal
  simp at equal

end MatchingMarket
end GameTheory
