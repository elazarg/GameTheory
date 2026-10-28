module

/-
# One-to-one ordinal matching

One-to-one blocking and stability specialize the shared responsive capacity
semantics to unit quotas. Individual preferences and the outside option retain
their native ordinal representation, with order laws required only by the
operations and theorems that use them.
-/

public import GameTheory.Cooperative.Matching.Capacitated

@[expose] public section

namespace GameTheory.MatchingMarket

universe uLeft uRight

variable {Left : Type uLeft} {Right : Type uRight}

/-- The unit-quota specialization of responsive blocking. -/
abbrev IsBlockingPair (market : MatchingMarket Left Right) (matching : Matching Left Right)
    (left : Left) (right : Right) : Prop :=
  (market.withCapacities (fun _ => 1)).IsBlockingPair matching left right

/-- The unit-quota specialization of responsive stability. -/
abbrev IsStable (market : MatchingMarket Left Right) (matching : Matching Left Right) : Prop :=
  (market.withCapacities (fun _ => 1)).IsStable matching

/-- One-to-one stability exposes injectivity as its assignment certificate. -/
theorem isStable_iff (market : MatchingMarket Left Right) (matching : Matching Left Right) :
    market.IsStable matching ↔ IsMatching matching ∧ market.IsIndividuallyRational matching ∧
      ¬ ∃ left right, market.IsBlockingPair matching left right := by
  have valid := (market.withCapacities (fun _ => 1)).isFeasible_iff_isMatching_of_unitCapacity
    (fun _ => rfl) matching
  exact and_congr valid Iff.rfl

theorem IsStable.isMatching {market : MatchingMarket Left Right}
    {matching : Matching Left Right} (stable : market.IsStable matching) : IsMatching matching :=
  ((market.withCapacities (fun _ => 1)).isFeasible_iff_isMatching_of_unitCapacity
    (fun _ => rfl) matching).mp stable.1

theorem IsStable.isIndividuallyRational {market : MatchingMarket Left Right}
    {matching : Matching Left Right} (stable : market.IsStable matching) :
    market.IsIndividuallyRational matching := stable.2.1

theorem IsStable.not_isBlockingPair {market : MatchingMarket Left Right}
    {matching : Matching Left Right} (stable : market.IsStable matching) (left : Left)
    (right : Right) : ¬ market.IsBlockingPair matching left right :=
  fun blocks => stable.2.2 ⟨left, right, blocks⟩

/-- On a valid one-to-one assignment, responsive acceptance is comparison
with its unique incumbent, or with the outside option when it has none. -/
theorem isBlockingPair_iff_pairwise (market : MatchingMarket Left Right)
    {matching : Matching Left Right} (valid : IsMatching matching) (left : Left) (right : Right) :
    market.IsBlockingPair matching left right ↔
      Preference.strict market.prefersLeft left (some right) (matching left) ∧
        (∀ incumbent, matching incumbent = some right →
          Preference.strict market.prefersRight right (some left) (some incumbent)) ∧
        ((∀ incumbent, matching incumbent ≠ some right) →
          Preference.strict market.prefersRight right (some left) none) := by
  have vacant : (cohort matching right).encard < (1 : ℕ∞) ↔
      ∀ incumbent, matching incumbent ≠ some right := by
    simp only [Set.encard_lt_one, Set.eq_empty_iff_forall_notMem, mem_cohort]
  constructor
  · rintro ⟨preferred, vacancy | replacement⟩
    · refine ⟨preferred, ?_, fun _ => vacancy.2⟩
      intro incumbent assigned
      exact False.elim ((vacant.mp vacancy.1 incumbent) assigned)
    · obtain ⟨incumbent, assigned, preferredIncumbent⟩ := replacement
      refine ⟨preferred, ?_, ?_⟩
      · intro other paired
        have same := valid other incumbent right paired assigned
        subst other
        exact preferredIncumbent
      · intro empty
        exact False.elim (empty incumbent assigned)
  · intro blocks
    classical
    by_cases occupied : ∃ incumbent, matching incumbent = some right
    · obtain ⟨incumbent, assigned⟩ := occupied
      exact ⟨blocks.1, Or.inr ⟨incumbent, assigned, blocks.2.1 incumbent assigned⟩⟩
    · have empty : ∀ incumbent, matching incumbent ≠ some right := by
        intro incumbent assigned
        exact occupied ⟨incumbent, assigned⟩
      exact ⟨blocks.1, Or.inl ⟨vacant.mpr empty, blocks.2.2 empty⟩⟩

/-- If every proposer strictly prefers remaining unmatched, the empty
assignment is stable. -/
theorem empty_stable_if_all_prefer_unmatched (market : MatchingMarket Left Right)
    (outside : ∀ left right, Preference.strict market.prefersLeft left none (some right)) :
    market.IsStable (fun _ => none) := by
  apply (market.isStable_iff _).mpr
  refine ⟨empty_isMatching, ?_, ?_⟩
  · intro left right paired
    simp at paired
  · rintro ⟨left, right, blocks⟩
    exact (outside left right).2 blocks.1.1

/-- Mutual strict top choices must be paired in every stable matching. -/
theorem stable_respects_mutual_top (market : MatchingMarket Left Right)
    (matching : Matching Left Right) (left : Left) (right : Right)
    (leftTop : ∀ alternative, alternative ≠ some right →
      Preference.strict market.prefersLeft left (some right) alternative)
    (rightTop : ∀ alternative, alternative ≠ some left →
      Preference.strict market.prefersRight right (some left) alternative)
    (stable : market.IsStable matching) : matching left = some right := by
  by_contra different
  apply stable.not_isBlockingPair left right
  apply (market.isBlockingPair_iff_pairwise stable.isMatching left right).mpr
  refine ⟨leftTop (matching left) different, ?_, ?_⟩
  · intro other paired
    apply rightTop (some other)
    intro same
    have equal : left = other := (Option.some.inj same).symm
    subst other
    exact different paired
  · intro _
    exact rightTop none (by simp)

/-- Assigned partners in a stable matching prefer the match weakly to the outside option. -/
theorem stable_individually_rational (market : MatchingMarket Left Right)
    (matching : Matching Left Right) (stable : market.IsStable matching)
    {left : Left} {right : Right} (paired : matching left = some right) :
    market.prefersLeft left (some right) none ∧ market.prefersRight right (some left) none :=
  stable.isIndividuallyRational left right paired

end GameTheory.MatchingMarket
