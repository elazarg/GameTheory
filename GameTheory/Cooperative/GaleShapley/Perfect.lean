/-
# Perfect stable matchings

In a balanced finite market where every possible partner is strictly better
than the outside option, stability forces every agent to be matched.
-/

import GameTheory.Cooperative.GaleShapley

namespace GameTheory

namespace MatchingMarket

universe uLeft uRight

variable {Left : Type uLeft} {Right : Type uRight}

/-- Both sides of a partial one-to-one assignment are fully matched. -/
def IsPerfect (matching : Matching Left Right) : Prop :=
  (∀ left, ∃ right, matching left = some right) ∧
    ∀ right, ∃ left, matching left = some right

variable [Fintype Left] [Fintype Right]

/-- In a balanced market, an unmatched left-side agent forces an unmatched
right-side agent. -/
theorem exists_unmatched_right_of_unmatched_left
    {matching : Matching Left Right}
    (hcard : Fintype.card Left = Fintype.card Right)
    {left₀ : Left} (hunmatched : matching left₀ = none) :
    ∃ right : Right, ∀ left : Left, matching left ≠ some right := by
  classical
  by_contra hall
  push Not at hall
  let preimage : Right → Left := fun right => Classical.choose (hall right)
  have hpreimage : ∀ right, matching (preimage right) = some right :=
    fun right => Classical.choose_spec (hall right)
  have hinjective : Function.Injective preimage := by
    intro right₁ right₂ heq
    have hmatching := congrArg matching heq
    rw [hpreimage right₁, hpreimage right₂] at hmatching
    exact Option.some.inj hmatching
  have hnotsurjective : ¬ Function.Surjective preimage := by
    intro hsurjective
    obtain ⟨right, hright⟩ := hsurjective left₀
    have := hpreimage right
    rw [hright, hunmatched] at this
    contradiction
  have := Fintype.card_lt_of_injective_not_surjective
    preimage hinjective hnotsurjective
  omega

/-- In a valid balanced matching, an unmatched right-side agent forces an
unmatched left-side agent. -/
theorem exists_unmatched_left_of_unmatched_right
    {matching : Matching Left Right} (valid : IsMatching matching)
    (hcard : Fintype.card Left = Fintype.card Right) {right₀ : Right}
    (hunmatched : ∀ left, matching left ≠ some right₀) :
    ∃ left : Left, matching left = none := by
  classical
  by_contra hall
  push Not at hall
  have hsome : ∀ left, ∃ right, matching left = some right := by
    intro left
    cases hmatch : matching left with
    | none => exact False.elim (hall left hmatch)
    | some right => exact ⟨right, rfl⟩
  let partner : Left → Right := fun left => Classical.choose (hsome left)
  have hpartner : ∀ left, matching left = some (partner left) :=
    fun left => Classical.choose_spec (hsome left)
  have hinjective : Function.Injective partner := by
    intro left₁ left₂ heq
    exact valid left₁ left₂ (partner left₁) (hpartner left₁) (by
      rw [heq]
      exact hpartner left₂)
  have hnotsurjective : ¬ Function.Surjective partner := by
    intro hsurjective
    obtain ⟨left, hleft⟩ := hsurjective right₀
    apply hunmatched left
    rw [hpartner left, hleft]
  have := Fintype.card_lt_of_injective_not_surjective
    partner hinjective hnotsurjective
  omega

omit [Fintype Left] [Fintype Right] in
/-- A stable matching cannot leave a mutually acceptable pair unmatched on
both sides. -/
theorem not_unmatched_acceptable_pair_of_stable
    (market : MatchingMarket Left Right) {matching : Matching Left Right}
    (stable : market.IsStable matching) {left : Left} {right : Right}
    (leftUnmatched : matching left = none)
    (rightUnmatched : ∀ left', matching left' ≠ some right)
    (leftAccepts : Preference.strict market.prefersLeft left (some right) none)
    (rightAccepts : Preference.strict market.prefersRight right (some left) none) :
    False := by
  apply stable.2.2
  refine ⟨left, right, ?_, ?_, ?_⟩
  · simpa [leftUnmatched] using leftAccepts
  · intro left' hmatch
    exact False.elim (rightUnmatched left' hmatch)
  · intro _
    exact rightAccepts

/-- In a balanced completely acceptable market, every stable matching is
perfect. -/
theorem stable_matching_perfect
    (market : MatchingMarket Left Right) {matching : Matching Left Right}
    (stable : market.IsStable matching)
    (hcard : Fintype.card Left = Fintype.card Right)
    (acceptable : market.HasCompleteAcceptability) :
    IsPerfect matching := by
  constructor
  · intro left
    cases hmatch : matching left with
    | some right => exact ⟨right, rfl⟩
    | none =>
        obtain ⟨right, hright⟩ :=
          exists_unmatched_right_of_unmatched_left hcard hmatch
        exact False.elim (market.not_unmatched_acceptable_pair_of_stable
          stable hmatch hright (acceptable.1 left right)
          (acceptable.2 right left))
  · intro right
    by_contra hunmatched
    push Not at hunmatched
    obtain ⟨left, hleft⟩ := exists_unmatched_left_of_unmatched_right
      stable.1 hcard hunmatched
    exact market.not_unmatched_acceptable_pair_of_stable stable hleft hunmatched
      (acceptable.1 left right) (acceptable.2 right left)

/-- The right-side partner selected from a perfect matching. -/
noncomputable def rightPartner
    {matching : Matching Left Right} (perfect : IsPerfect matching)
    (left : Left) : Right :=
  Classical.choose (perfect.1 left)

/-- The left-side partner selected from a perfect matching. -/
noncomputable def leftPartner
    {matching : Matching Left Right} (perfect : IsPerfect matching)
    (right : Right) : Left :=
  Classical.choose (perfect.2 right)

omit [Fintype Left] [Fintype Right] in
theorem match_rightPartner
    {matching : Matching Left Right} (perfect : IsPerfect matching)
    (left : Left) :
    matching left = some (rightPartner perfect left) :=
  Classical.choose_spec (perfect.1 left)

omit [Fintype Left] [Fintype Right] in
theorem match_leftPartner
    {matching : Matching Left Right} (perfect : IsPerfect matching)
    (right : Right) :
    matching (leftPartner perfect right) = some right :=
  Classical.choose_spec (perfect.2 right)

omit [Fintype Left] [Fintype Right] in
/-- The extracted partner maps of a perfect valid matching are inverse. -/
theorem rightPartner_eq_iff_leftPartner_eq
    {matching : Matching Left Right} (valid : IsMatching matching)
    (perfect : IsPerfect matching) {left : Left} {right : Right} :
    rightPartner perfect left = right ↔ leftPartner perfect right = left := by
  constructor
  · intro hright
    have h₁ : matching left = some right := by
      rw [← hright]
      exact match_rightPartner perfect left
    have h₂ : matching (leftPartner perfect right) = some right :=
      match_leftPartner perfect right
    exact valid (leftPartner perfect right) left right h₂ h₁
  · intro hleft
    have h₁ : matching left = some right := by
      rw [← hleft]
      exact match_leftPartner perfect right
    have h₂ : matching left = some (rightPartner perfect left) :=
      match_rightPartner perfect left
    exact (Option.some.inj (h₁.symm.trans h₂)).symm

/-- Every finite balanced market with completely acceptable linear
preferences admits a perfect stable matching. -/
theorem exists_perfect_stable
    (market : MatchingMarket Left Right)
    (linear : market.HasLinearPreferences)
    (hcard : Fintype.card Left = Fintype.card Right)
    (acceptable : market.HasCompleteAcceptability) :
    ∃ matching : Matching Left Right,
      market.IsStable matching ∧ IsPerfect matching := by
  exact ⟨market.deferredAcceptance linear,
    market.deferredAcceptance_isStable linear,
    market.stable_matching_perfect
      (market.deferredAcceptance_isStable linear) hcard acceptable⟩

end MatchingMarket

end GameTheory
