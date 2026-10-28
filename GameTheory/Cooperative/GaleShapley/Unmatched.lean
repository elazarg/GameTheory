module

/-
# Unmatched agents are invariant across stable matchings

Proposer optimality gives one inclusion between the matched proposer sets.
Stability then makes the proposer-optimal assignment receiver-pessimal,
giving the opposite inclusion on matched receivers. Each partial matching
matches the same number of agents on both sides, so both inclusions are
equalities. No balancedness or complete-acceptability assumption is needed.
-/

public import GameTheory.Cooperative.GaleShapley.Optimality
public import GameTheory.Cooperative.Matching.Transpose

@[expose] public section

noncomputable section

namespace GameTheory.MatchingMarket

universe uLeft uRight

variable {Left : Type uLeft} {Right : Type uRight}

/-- Swapping the market preserves strict linear preferences. -/
theorem HasLinearPreferences.transpose {market : MatchingMarket Left Right}
    (linear : market.HasLinearPreferences) : market.transpose.HasLinearPreferences :=
  ⟨linear.right, linear.left⟩

private def matched [Fintype Left] (matching : Matching Left Right) : Finset Left := by
  classical
  exact Finset.univ.filter fun left => matching left ≠ none

private theorem exists_partner {matching : Matching Left Right} {left : Left}
    (assigned : matching left ≠ none) : ∃ right, matching left = some right := by
  cases paired : matching left with
  | none => exact False.elim (assigned paired)
  | some right => exact ⟨right, rfl⟩

variable [Fintype Left] [Fintype Right] (market : MatchingMarket Left Right)

/-- Left-proposing deferred acceptance is weakly worst for each receiver among
stable matchings, with unmatchedness represented by the same outside option. -/
theorem deferredAcceptance_receiverPessimal (linear : market.HasLinearPreferences)
    {matching : Matching Left Right} (stable : market.IsStable matching) (right : Right) :
    market.prefersRight right (transposeMatching matching right)
      (transposeMatching (market.deferredAcceptance linear) right) := by
  have deferredStable := market.deferredAcceptance_isStable linear
  cases deferredPartner : transposeMatching (market.deferredAcceptance linear) right with
  | none =>
      cases partner : transposeMatching matching right with
      | none => exact (linear.right right).1 none
      | some left =>
          exact (stable.isIndividuallyRational left right
            ((transposeMatching_apply_some_iff matching stable.isMatching).mp partner)).2
  | some left =>
      by_contra notPreferred
      have receiverStrict := Rank.strict_of_not (linear.right right).2.2.1 notPreferred
      have deferredPair :=
        (transposeMatching_apply_some_iff _ deferredStable.isMatching).mp deferredPartner
      have proposerWeak := market.deferredAcceptance_proposerOptimal linear stable left
      rw [deferredPair] at proposerWeak
      have different : some right ≠ matching left := by
        intro paired
        have partner := (transposeMatching_apply_some_iff matching stable.isMatching).mpr
          paired.symm
        rw [partner] at receiverStrict
        exact receiverStrict.2 ((linear.right right).1 _)
      have proposerStrict :=
        Rank.strict_of_le_of_ne (linear.left left).2.2.2 proposerWeak different
      exact stable.not_isBlockingPair left right
        ((market.isBlockingPair_iff_partners stable.isMatching left right).mpr
          ⟨proposerStrict, receiverStrict⟩)

private theorem matched_card_transpose {matching : Matching Left Right}
    (valid : IsMatching matching) :
    (matched matching).card = (matched (transposeMatching matching)).card := by
  classical
  let partner (left : Left) (assigned : left ∈ matched matching) : Right :=
    Classical.choose (exists_partner ((Finset.mem_filter.mp assigned).2))
  have paired (left : Left) (assigned : left ∈ matched matching) :
      matching left = some (partner left assigned) :=
    Classical.choose_spec (exists_partner ((Finset.mem_filter.mp assigned).2))
  apply Finset.card_bij partner
  · intro left assigned
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [(transposeMatching_apply_some_iff matching valid).mpr (paired left assigned)]
    simp
  · intro first assignedFirst second assignedSecond equal
    apply valid first second (partner first assignedFirst) (paired first assignedFirst)
    rw [equal]
    exact paired second assignedSecond
  · intro right assigned
    obtain ⟨left, inversePair⟩ := exists_partner ((Finset.mem_filter.mp assigned).2)
    have pair := (transposeMatching_apply_some_iff matching valid).mp inversePair
    have assignedLeft : left ∈ matched matching := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, by rw [pair]; simp⟩
    exact ⟨left, assignedLeft, Option.some.inj ((paired left assignedLeft).symm.trans pair)⟩

omit [Fintype Right] in
private theorem matched_subset_of_preferred (linear : market.HasLinearPreferences)
    {first second : Matching Left Right} (rational : market.IsIndividuallyRational first)
    (preferred : ∀ left, market.prefersLeft left (second left) (first left)) :
    matched first ⊆ matched second := by
  classical
  intro left assigned
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro unmatched
  obtain ⟨right, pair⟩ := exists_partner ((Finset.mem_filter.mp assigned).2)
  have improvement := preferred left
  rw [unmatched, pair] at improvement
  have equal := (linear.left left).2.2.2 _ _ improvement (rational left right pair).1
  cases equal

private theorem matched_eq_deferredAcceptance (linear : market.HasLinearPreferences)
    {matching : Matching Left Right} (stable : market.IsStable matching) :
    matched matching = matched (market.deferredAcceptance linear) := by
  have deferredStable := market.deferredAcceptance_isStable linear
  have proposerSubset := market.matched_subset_of_preferred linear stable.isIndividuallyRational
    (market.deferredAcceptance_proposerOptimal linear stable)
  have receiverSubset := market.transpose.matched_subset_of_preferred linear.transpose
    deferredStable.transpose.isIndividuallyRational
    (market.deferredAcceptance_receiverPessimal linear stable)
  apply Finset.eq_of_subset_of_card_le proposerSubset
  rw [matched_card_transpose deferredStable.isMatching, matched_card_transpose stable.isMatching]
  exact Finset.card_le_card receiverSubset

/-- Every stable matching leaves exactly the same proposers unmatched. -/
theorem stable_unmatched_left_iff (linear : market.HasLinearPreferences)
    {first second : Matching Left Right}
    (stableFirst : market.IsStable first) (stableSecond : market.IsStable second) (left : Left) :
    first left = none ↔ second left = none := by
  classical
  have equal : matched first = matched second :=
    (market.matched_eq_deferredAcceptance linear stableFirst).trans
      (market.matched_eq_deferredAcceptance linear stableSecond).symm
  have membership : left ∈ matched first ↔ left ∈ matched second := by rw [equal]
  simpa only [matched, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using
    not_congr membership

/-- Every stable matching leaves exactly the same receivers unmatched. -/
theorem stable_unmatched_right_iff (linear : market.HasLinearPreferences)
    {first second : Matching Left Right}
    (stableFirst : market.IsStable first) (stableSecond : market.IsStable second) (right : Right) :
    (∀ left, first left ≠ some right) ↔ (∀ left, second left ≠ some right) := by
  rw [← transposeMatching_apply_none_iff first right,
    ← transposeMatching_apply_none_iff second right]
  exact market.transpose.stable_unmatched_left_iff linear.transpose
    stableFirst.transpose stableSecond.transpose right

end GameTheory.MatchingMarket
