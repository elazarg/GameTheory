module

/-
# Transposing partial two-sided matchings

Swapping the two sides swaps their preference families. A partial matching
has a reciprocal optional partner map without requiring every agent to be
matched. Validity makes the two maps inverse on matched pairs, and stability
is invariant under this transposition.
-/

public import GameTheory.Cooperative.Matching

@[expose] public section

noncomputable section

namespace GameTheory.MatchingMarket

universe uLeft uRight

variable {Left : Type uLeft} {Right : Type uRight}

/-- Swap the two preference families of a market. -/
def transpose (market : MatchingMarket Left Right) : MatchingMarket Right Left where
  prefersLeft := market.prefersRight
  prefersRight := market.prefersLeft

@[simp]
theorem transpose_transpose (market : MatchingMarket Left Right) :
    market.transpose.transpose = market := rfl

/-- The reciprocal optional partner map. Nonmatching input still has a
selected reciprocal map, but the paired equivalence requires validity. -/
def transposeMatching (matching : Matching Left Right) : Matching Right Left := by
  classical
  exact fun right =>
    if paired : ∃ left, matching left = some right then some paired.choose else none

theorem transposeMatching_apply_some_iff (matching : Matching Left Right)
    (valid : IsMatching matching) {left : Left} {right : Right} :
    transposeMatching matching right = some left ↔ matching left = some right := by
  classical
  unfold transposeMatching
  split
  next paired =>
    constructor
    · intro same
      have equal : paired.choose = left := Option.some.inj same
      simpa only [equal] using paired.choose_spec
    · intro pair
      have equal := valid paired.choose left right paired.choose_spec pair
      exact congrArg some equal
  next absent =>
    constructor
    · intro impossible
      cases impossible
    · intro pair
      exact False.elim (absent ⟨left, pair⟩)

theorem transposeMatching_apply_none_iff (matching : Matching Left Right) (right : Right) :
    transposeMatching matching right = none ↔ ∀ left, matching left ≠ some right := by
  classical
  simp only [transposeMatching]
  split
  next paired =>
    simp only [Option.some_ne_none, false_iff, not_forall, not_not]
    exact paired
  next absent =>
    simp only [true_iff]
    exact fun left paired => absent ⟨left, paired⟩

/-- A selected reciprocal map is a valid matching even before validity is
assumed for the original assignment. -/
theorem isMatching_transposeMatching (matching : Matching Left Right) :
    IsMatching (transposeMatching matching) := by
  classical
  intro first second left pairedFirst pairedSecond
  have original (right : Right) (paired : transposeMatching matching right = some left) :
      matching left = some right := by
    unfold transposeMatching at paired
    split at paired
    next existsPair =>
      have equal := Option.some.inj paired
      simpa only [equal] using existsPair.choose_spec
    next absent => cases paired
  exact Option.some.inj ((original first pairedFirst).symm.trans (original second pairedSecond))

@[simp]
theorem transposeMatching_transposeMatching (matching : Matching Left Right)
    (valid : IsMatching matching) :
    transposeMatching (transposeMatching matching) = matching := by
  funext left
  cases paired : matching left with
  | some right =>
      exact (transposeMatching_apply_some_iff _ (isMatching_transposeMatching matching)).mpr
        ((transposeMatching_apply_some_iff matching valid).mpr paired)
  | none =>
      apply (transposeMatching_apply_none_iff _ left).mpr
      intro right inversePair
      have pair := (transposeMatching_apply_some_iff matching valid).mp inversePair
      rw [paired] at pair
      cases pair

/-- A blocking pair compares each side with its reciprocal optional partner. -/
theorem isBlockingPair_iff_partners (market : MatchingMarket Left Right)
    {matching : Matching Left Right} (valid : IsMatching matching) (left : Left) (right : Right) :
    market.IsBlockingPair matching left right ↔
      Preference.strict market.prefersLeft left (some right) (matching left) ∧
        Preference.strict market.prefersRight right
          (some left) (transposeMatching matching right) := by
  constructor
  · intro blocks
    refine ⟨blocks.1, ?_⟩
    cases partner : transposeMatching matching right with
    | none => exact blocks.2.2 ((transposeMatching_apply_none_iff matching right).mp partner)
    | some other =>
        exact blocks.2.1 other ((transposeMatching_apply_some_iff matching valid).mp partner)
  · rintro ⟨leftStrict, rightStrict⟩
    refine ⟨leftStrict, ?_, ?_⟩
    · intro other paired
      rwa [(transposeMatching_apply_some_iff matching valid).mpr paired] at rightStrict
    · intro unmatched
      rwa [(transposeMatching_apply_none_iff matching right).mpr unmatched] at rightStrict

theorem isBlockingPair_transpose_iff (market : MatchingMarket Left Right)
    {matching : Matching Left Right} (valid : IsMatching matching) (left : Left) (right : Right) :
    market.transpose.IsBlockingPair (transposeMatching matching) right left ↔
      market.IsBlockingPair matching left right := by
  rw [isBlockingPair_iff_partners _ (isMatching_transposeMatching matching),
    transposeMatching_transposeMatching matching valid, isBlockingPair_iff_partners _ valid]
  exact and_comm

/-- Stability is unchanged when the market and its partial assignment are
both viewed from the other side. -/
theorem IsStable.transpose {market : MatchingMarket Left Right}
    {matching : Matching Left Right} (stable : market.IsStable matching) :
    market.transpose.IsStable (transposeMatching matching) := by
  refine ⟨isMatching_transposeMatching matching, ?_, ?_⟩
  · intro right left paired
    have pair := (transposeMatching_apply_some_iff matching stable.isMatching).mp paired
    exact (stable.isIndividuallyRational left right pair).symm
  · rintro ⟨right, left, blocks⟩
    exact stable.not_isBlockingPair left right
      ((market.isBlockingPair_transpose_iff stable.isMatching left right).mp blocks)

end GameTheory.MatchingMarket
