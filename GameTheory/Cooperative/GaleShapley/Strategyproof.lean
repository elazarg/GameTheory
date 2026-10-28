module

/-
# Truthful reporting by deferred-acceptance proposers

A proposer cannot obtain a better partner by unilaterally changing its strict
ranking, including the position of the outside option. The proof uses
proposer optimality and invariance of unmatched agents across stable matchings:
truncate the true list at the allegedly improved partner, then retain only
that partner as acceptable. Stability transfers between these two reports
would otherwise give stable matchings with different unmatched proposers.
-/

public import GameTheory.Cooperative.GaleShapley.Unmatched
public import GameTheory.Core.Rank.Truncation

@[expose] public section

noncomputable section

namespace GameTheory.MatchingMarket

universe uLeft uRight

variable {Left : Type uLeft} {Right : Type uRight}

/-- Replace one proposer's reported ranking, preserving every other ranking
on both sides of the market. -/
def withLeftReport [DecidableEq Left] (market : MatchingMarket Left Right)
    (who : Left) (report : Option Right → Option Right → Prop) : MatchingMarket Left Right where
  prefersLeft left := if left = who then report else market.prefersLeft left
  prefersRight := market.prefersRight

@[simp]
theorem withLeftReport_self [DecidableEq Left] (market : MatchingMarket Left Right)
    (who : Left) (report : Option Right → Option Right → Prop) :
    (market.withLeftReport who report).prefersLeft who = report := by
  simp only [withLeftReport, ite_true]

@[simp]
theorem withLeftReport_other [DecidableEq Left] (market : MatchingMarket Left Right)
    (who : Left) (report : Option Right → Option Right → Prop)
    {other : Left} (different : other ≠ who) :
    (market.withLeftReport who report).prefersLeft other = market.prefersLeft other := by
  simp only [withLeftReport, ite_eq_right different]

/-- A unilateral linear ranking report preserves strict preferences. -/
theorem withLeftReport_linear [DecidableEq Left] (market : MatchingMarket Left Right)
    (linear : market.HasLinearPreferences) (who : Left)
    (report : Option Right → Option Right → Prop) (reportLinear : Rank.Linear report) :
    (market.withLeftReport who report).HasLinearPreferences := by
  refine ⟨?_, linear.right⟩
  intro left
  by_cases same : left = who
  · subst left
    simpa only [withLeftReport_self] using reportLinear
  · simpa only [withLeftReport_other market who report same] using linear.left left

private theorem stable_transfer {source target : MatchingMarket Left Right}
    {matching : Matching Left Right} (who : Left) (stable : source.IsStable matching)
    (sameRight : source.prefersRight = target.prefersRight)
    (sameOther : ∀ other, other ≠ who → source.prefersLeft other = target.prefersLeft other)
    (rational : ∀ right, matching who = some right → target.prefersLeft who (some right) none)
    (strict : ∀ right, Preference.strict target.prefersLeft who (some right) (matching who) →
      Preference.strict source.prefersLeft who (some right) (matching who)) :
    target.IsStable matching := by
  apply (target.isStable_iff _).mpr
  refine ⟨stable.isMatching, ?_, ?_⟩
  · intro left right paired
    have original := stable.isIndividuallyRational left right paired
    constructor
    · by_cases same : left = who
      · subst left
        exact rational right paired
      · simpa only [← sameOther left same] using original.1
    · simpa only [sameRight] using original.2
  · rintro ⟨left, right, blocks⟩
    have blocks := (target.isBlockingPair_iff_pairwise stable.isMatching left right).mp blocks
    apply stable.not_isBlockingPair left right
    apply (source.isBlockingPair_iff_pairwise stable.isMatching left right).mpr
    refine ⟨?_, ?_, ?_⟩
    · by_cases same : left = who
      · subst left
        exact strict right blocks.1
      · simpa only [Preference.strict, sameOther left same] using blocks.1
    · simpa only [sameRight] using blocks.2.1
    · simpa only [sameRight] using blocks.2.2

variable [Fintype Left] [Fintype Right] (market : MatchingMarket Left Right)

/-- Truthful deferred acceptance is weakly preferred to every stable outcome
under a unilateral proposer report. The other proposers' rankings and all
receivers' rankings remain fixed. -/
theorem deferredAcceptance_prefers_of_unilateral_report_stable
    (linear : market.HasLinearPreferences) (who : Left)
    {reported : MatchingMarket Left Right}
    (sameRight : reported.prefersRight = market.prefersRight)
    (sameOther : ∀ other, other ≠ who → reported.prefersLeft other = market.prefersLeft other)
    {matching : Matching Left Right} (stable : reported.IsStable matching) :
    market.prefersLeft who (market.deferredAcceptance linear who) (matching who) := by
  classical
  have truthfulStable := market.deferredAcceptance_isStable linear
  have truthfulRational : market.prefersLeft who (market.deferredAcceptance linear who) none := by
    cases paired : market.deferredAcceptance linear who with
    | none => exact (linear.left who).1 none
    | some right => exact (truthfulStable.isIndividuallyRational who right paired).1
  by_contra notPreferred
  cases reportedPartner : matching who with
  | none => exact notPreferred (by simpa only [reportedPartner] using truthfulRational)
  | some partner =>
      have improvement : Rank.strict (market.prefersLeft who) (some partner)
          (market.deferredAcceptance linear who) :=
        Rank.strict_of_not (linear.left who).2.2.1
          (by simpa only [reportedPartner] using notPreferred)
      have acceptable : market.prefersLeft who (some partner) none :=
        (linear.left who).2.1 _ _ _ improvement.1 truthfulRational
      let truncated := market.withLeftReport who (Rank.truncate (market.prefersLeft who) partner)
      have truncatedLinear : truncated.HasLinearPreferences :=
        market.withLeftReport_linear linear who _ (Rank.truncate_linear (linear.left who) partner)
      let outcome := truncated.deferredAcceptance truncatedLinear
      have outcomeStable : truncated.IsStable outcome :=
        truncated.deferredAcceptance_isStable truncatedLinear
      have unmatched : outcome who = none := by
        cases assigned : outcome who with
        | none => rfl
        | some assignedPartner =>
            have above : market.prefersLeft who (some assignedPartner) (some partner) := by
              have rational := (outcomeStable.isIndividuallyRational who assignedPartner assigned).1
              simpa only [truncated, withLeftReport_self, Rank.truncate_some_none] using rational
            have trueStable : market.IsStable outcome := by
              apply stable_transfer (target := market) who outcomeStable rfl
              · intro other different
                exact withLeftReport_other market who _ different
              · intro right paired
                have equal : right = assignedPartner := Option.some.inj (paired.symm.trans assigned)
                subst right
                exact (linear.left who).2.1 _ _ _ above acceptable
              · intro right strict
                simpa only [truncated, withLeftReport_self, assigned,
                  Preference.strict, Rank.strict, Rank.truncate_some_some] using strict
            have optimal := market.deferredAcceptance_proposerOptimal linear trueStable who
            have dominates : market.prefersLeft who (market.deferredAcceptance linear who)
                (some partner) := (linear.left who).2.1 _ _ _
                  (by simpa only [assigned] using optimal) above
            exact False.elim (improvement.2 dominates)
      let singleton := market.withLeftReport who (Rank.onlyAccept (market.prefersLeft who) partner)
      have singletonLinear : singleton.HasLinearPreferences :=
        market.withLeftReport_linear linear who _ (Rank.onlyAccept_linear (linear.left who) partner)
      have reportedStable : singleton.IsStable matching := by
        apply stable_transfer (target := singleton) who stable sameRight
        · intro other different
          rw [withLeftReport_other market who _ different]
          exact sameOther other different
        · intro right paired
          have equal : right = partner := Option.some.inj (paired.symm.trans reportedPartner)
          subst right
          simp only [singleton, withLeftReport_self, Rank.onlyAccept_some_none_iff]
        · intro right strict
          simp only [Preference.strict, singleton, withLeftReport_self] at strict
          rw [reportedPartner] at strict
          exact False.elim (strict.2 (Rank.onlyAccept_top _ partner (some right)))
      have truncatedStable : singleton.IsStable outcome := by
        apply stable_transfer (target := singleton) who outcomeStable rfl
        · intro other different
          simp only [truncated, singleton, withLeftReport_other market who _ different]
        · intro right paired
          rw [unmatched] at paired
          cases paired
        · intro right strict
          simp only [Preference.strict, singleton, withLeftReport_self] at strict
          rw [unmatched] at strict
          have equal : right = partner := (Rank.onlyAccept_some_none_iff _ _ _).mp strict.1
          subst right
          simp only [Preference.strict, truncated, withLeftReport_self]
          rw [unmatched]
          simp only [Rank.strict, Rank.truncate_some_none, Rank.truncate_none_some]
          exact ⟨(linear.left who).1 _, not_not_intro ((linear.left who).1 _)⟩
      have equivalent := singleton.stable_unmatched_left_iff singletonLinear
        truncatedStable reportedStable who
      cases reportedPartner.symm.trans (equivalent.mp unmatched)

/-- Unilaterally misreporting a strict proposer ranking cannot improve that
proposer's deferred-acceptance partner, including through truncation or changes
to which partners are acceptable. -/
theorem deferredAcceptance_strategyproof [DecidableEq Left]
    (linear : market.HasLinearPreferences) (who : Left)
    (report : Option Right → Option Right → Prop) (reportLinear : Rank.Linear report) :
    market.prefersLeft who (market.deferredAcceptance linear who)
      ((market.withLeftReport who report).deferredAcceptance
        (market.withLeftReport_linear linear who report reportLinear) who) := by
  apply market.deferredAcceptance_prefers_of_unilateral_report_stable linear who
    (reported := market.withLeftReport who report)
    (matching := (market.withLeftReport who report).deferredAcceptance
      (market.withLeftReport_linear linear who report reportLinear)) rfl
  · intro other different
    exact withLeftReport_other market who report different
  · exact (market.withLeftReport who report).deferredAcceptance_isStable
      (market.withLeftReport_linear linear who report reportLinear)

end GameTheory.MatchingMarket
