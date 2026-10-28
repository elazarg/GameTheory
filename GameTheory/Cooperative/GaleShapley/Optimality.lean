module

/-
# Proposer optimality of deferred acceptance

Every rejected pair is absent from every stable matching. This invariant is
preserved by simultaneous rejection rounds: if a receiver rejects a possible
stable partner, its preferred held proposer and that receiver would block the
stable matching. At termination every proposer therefore chooses its best
partner among all stable matchings, including the outside option.
-/

public import GameTheory.Cooperative.GaleShapley

@[expose] public section

namespace GameTheory.MatchingMarket

universe uLeft uRight

variable {Left : Type uLeft} {Right : Type uRight}
    [Fintype Left] [Fintype Right] (market : MatchingMarket Left Right)

omit [Fintype Left] in
private theorem topChoice_prefers_none (linear : market.HasLinearPreferences)
    (rejected : Left → Finset Right) (left : Left) :
    market.prefersLeft left (market.topChoice linear rejected left) none := by
  cases chosen : market.topChoice linear rejected left with
  | none => exact (linear.left left).1 none
  | some right => exact market.acceptableToLeft_of_topChoice linear chosen

omit [Fintype Left] in
private theorem topChoice_prefers_available (linear : market.HasLinearPreferences)
    {rejected : Left → Finset Right} {left : Left} {right : Right}
    (available : right ∈ market.available rejected left) :
    market.prefersLeft left (market.topChoice linear rejected left) (some right) := by
  classical
  have nonempty : (market.available rejected left).Nonempty := ⟨right, available⟩
  have existsChoice : ∃ chosen, market.topChoice linear rejected left = some chosen := by
    unfold topChoice
    rw [dite_eq_left nonempty]
    exact ⟨_, rfl⟩
  obtain ⟨chosen, choice⟩ := existsChoice
  rw [choice]
  exact (market.topChoice_spec linear choice).2 right available

/-- No pair occurring in a stable matching is ever rejected by a simultaneous
deferred-acceptance round starting from the empty rejection state. -/
theorem stable_partner_not_rejected_iterate (linear : market.HasLinearPreferences)
    (rounds : ℕ) {matching : Matching Left Right} (stable : market.IsStable matching)
    {left : Left} {right : Right} (paired : matching left = some right) :
    right ∉ ((market.daStep linear)^[rounds] (fun _ => ∅)) left := by
  classical
  induction rounds generalizing left right with
  | zero => simp
  | succ rounds ih =>
      rw [Function.iterate_succ_apply']
      intro rejected
      simp only [daStep, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
        true_and] at rejected
      rcases rejected with rejected | ⟨choice, notHeld⟩
      · exact ih paired rejected
      · have acceptable := (stable.isIndividuallyRational left right paired).2
        have suitor : left ∈ market.suitors linear
            ((market.daStep linear)^[rounds] (fun _ => ∅)) right :=
          (market.mem_suitors linear).mpr ⟨choice, acceptable⟩
        obtain ⟨held, heldChoice⟩ : ∃ held, market.holder linear
            ((market.daStep linear)^[rounds] (fun _ => ∅)) right = some held :=
          Option.isSome_iff_exists.mp (market.holder_isSome_of_suitors linear ⟨left, suitor⟩)
        have heldDifferent : held ≠ left := by
          intro equal
          subst held
          exact notHeld heldChoice
        have holderSpec := market.holder_spec linear heldChoice
        have heldProposes := (market.mem_suitors linear).mp holderSpec.1 |>.1
        have receiverStrict : Preference.strict market.prefersRight right (some held)
            (some left) :=
          Rank.strict_of_le_of_ne (linear.right right).2.2.2
            (holderSpec.2 left suitor) (by simpa using heldDifferent)
        have proposerWeak : market.prefersLeft held (some right) (matching held) := by
          rw [← heldProposes]
          cases partner : matching held with
          | none => exact market.topChoice_prefers_none linear _ held
          | some other =>
              apply market.topChoice_prefers_available linear
              exact market.mem_available.mpr
                ⟨ih partner, (stable.isIndividuallyRational held other partner).1⟩
        have proposerStrict : Preference.strict market.prefersLeft held (some right)
            (matching held) :=
          Rank.strict_of_le_of_ne (linear.left held).2.2.2 proposerWeak (by
            intro equal
            exact heldDifferent (stable.isMatching held left right equal.symm paired))
        apply stable.not_isBlockingPair held right
        refine ⟨proposerStrict, ?_, ?_⟩
        · intro other otherPaired
          have equal := stable.isMatching other left right otherPaired paired
          subst other
          exact receiverStrict
        · intro unmatched
          exact False.elim (unmatched left paired)

/-- Every proposer weakly prefers its deferred-acceptance partner to its
partner in any stable matching. Outside options and unacceptable partners are
included; neither balanced market sizes nor complete acceptability is needed. -/
theorem deferredAcceptance_proposerOptimal (linear : market.HasLinearPreferences)
    {matching : Matching Left Right} (stable : market.IsStable matching) (left : Left) :
    market.prefersLeft left (market.deferredAcceptance linear left) (matching left) := by
  change market.prefersLeft left
    (market.topChoice linear (market.daFixedPoint linear) left) (matching left)
  cases paired : matching left with
  | none => exact market.topChoice_prefers_none linear _ left
  | some right =>
      apply market.topChoice_prefers_available linear
      exact market.mem_available.mpr
        ⟨market.stable_partner_not_rejected_iterate linear _ stable paired,
          (stable.isIndividuallyRational left right paired).1⟩

end GameTheory.MatchingMarket
