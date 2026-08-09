/-
# Ordinal two-sided matching

One-to-one matching is a native market-design object.  Preferences compare
optional partners, so remaining unmatched is an ordinary alternative rather
than a separately scaled reservation value.  The market stores no finiteness,
decidability, utility representation, probability, or strategic game.

The orientation

`prefersLeft agent preferred alternative`

means that the agent weakly prefers `preferred` to `alternative`.
-/

import GameTheory.Core.Rank

namespace GameTheory

universe uLeft uRight

/-- A two-sided market with ordinal preferences over possible partners and
the explicit outside option `none`. -/
structure MatchingMarket (Left : Type uLeft) (Right : Type uRight) where
  prefersLeft : Ranking Left (Option Right)
  prefersRight : Ranking Right (Option Left)

namespace MatchingMarket

variable {Left : Type uLeft} {Right : Type uRight}

/-- A one-to-one partial assignment, represented from the left side. -/
abbrev Matching (Left : Type uLeft) (Right : Type uRight) :=
  Left → Option Right

/-- No right-side agent is assigned to two left-side agents. -/
def IsMatching (matching : Matching Left Right) : Prop :=
  ∀ left₁ left₂ right,
    matching left₁ = some right → matching left₂ = some right → left₁ = left₂

/-- Both agents strictly prefer one another to their current assignments. -/
def IsBlockingPair
    (market : MatchingMarket Left Right) (matching : Matching Left Right)
    (left : Left) (right : Right) : Prop :=
  Preference.strict market.prefersLeft left (some right) (matching left) ∧
    (∀ left', matching left' = some right →
      Preference.strict market.prefersRight right (some left) (some left')) ∧
    ((∀ left', matching left' ≠ some right) →
      Preference.strict market.prefersRight right (some left) none)

/-- Every assigned agent weakly prefers the assignment to remaining
unmatched. -/
def IsIndividuallyRational
    (market : MatchingMarket Left Right) (matching : Matching Left Right) : Prop :=
  ∀ left right, matching left = some right →
    market.prefersLeft left (some right) none ∧
      market.prefersRight right (some left) none

/-- Every cross-side pair strictly prefers matching to remaining unmatched. -/
def HasCompleteAcceptability (market : MatchingMarket Left Right) : Prop :=
  (∀ left right,
    Preference.strict market.prefersLeft left (some right) none) ∧
  ∀ right left,
    Preference.strict market.prefersRight right (some left) none

/-- Stability means a valid, individually rational assignment with no
blocking pair. -/
def IsStable
    (market : MatchingMarket Left Right) (matching : Matching Left Right) : Prop :=
  IsMatching matching ∧ market.IsIndividuallyRational matching ∧
    ¬ ∃ left right, market.IsBlockingPair matching left right

theorem IsStable.isMatching
    {market : MatchingMarket Left Right} {matching : Matching Left Right}
    (stable : market.IsStable matching) : IsMatching matching :=
  stable.1

theorem IsStable.isIndividuallyRational
    {market : MatchingMarket Left Right} {matching : Matching Left Right}
    (stable : market.IsStable matching) : market.IsIndividuallyRational matching :=
  stable.2.1

theorem IsStable.not_isBlockingPair
    {market : MatchingMarket Left Right} {matching : Matching Left Right}
    (stable : market.IsStable matching) (left : Left) (right : Right) :
    ¬ market.IsBlockingPair matching left right :=
  fun blocks => stable.2.2 ⟨left, right, blocks⟩

/-- Stable matchings of a fixed market. -/
abbrev StableMatching (market : MatchingMarket Left Right) :=
  { matching : Matching Left Right // market.IsStable matching }

namespace StableMatching

instance (market : MatchingMarket Left Right) :
    CoeFun market.StableMatching (fun _ => Matching Left Right) where
  coe matching := matching.1

@[ext]
theorem ext
    {market : MatchingMarket Left Right} {first second : market.StableMatching}
    (h : ∀ left, first left = second left) : first = second :=
  Subtype.ext (funext h)

end StableMatching

/-- The empty partial assignment is one-to-one. -/
theorem empty_isMatching :
    IsMatching (fun _ : Left => (none : Option Right)) := by
  intro _ _ right h
  simp at h

/-- If every left-side agent strictly prefers remaining unmatched to every
partner, the empty matching is stable. -/
theorem empty_stable_if_all_prefer_unmatched
    (market : MatchingMarket Left Right)
    (hleft : ∀ left right,
      Preference.strict market.prefersLeft left none (some right)) :
    market.IsStable (fun _ => none) := by
  refine ⟨empty_isMatching, ?_, ?_⟩
  · intro left right h
    simp at h
  · rintro ⟨left, right, blocks⟩
    exact (hleft left right).2 blocks.1.1

/-- Mutual strict top choices must be paired in every stable matching. -/
theorem stable_respects_mutual_top
    (market : MatchingMarket Left Right) (matching : Matching Left Right)
    (left : Left) (right : Right)
    (leftTop : ∀ alternative, alternative ≠ some right →
      Preference.strict market.prefersLeft left (some right) alternative)
    (rightTop : ∀ alternative, alternative ≠ some left →
      Preference.strict market.prefersRight right (some left) alternative)
    (stable : market.IsStable matching) :
    matching left = some right := by
  by_contra hmatch
  apply stable.2.2
  refine ⟨left, right, leftTop (matching left) hmatch, ?_, ?_⟩
  · intro left' hleft'
    apply rightTop (some left')
    intro heq
    have : left = left' := (Option.some.inj heq).symm
    subst left'
    exact hmatch hleft'
  · intro _
    exact rightTop none (by simp)

/-- Assigned partners in a stable matching weakly prefer the match to their
outside options. -/
theorem stable_individually_rational
    (market : MatchingMarket Left Right) (matching : Matching Left Right)
    (stable : market.IsStable matching) {left : Left} {right : Right}
    (hmatch : matching left = some right) :
    market.prefersLeft left (some right) none ∧
      market.prefersRight right (some left) none :=
  stable.2.1 left right hmatch

end MatchingMarket

end GameTheory
