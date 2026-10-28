module

/-
# Proposer reports, rejection, and outside options

A contested proposer cannot recover a rejected first choice by declaring every
other partner unacceptable. In an unbalanced market a proposer can instead
harm itself by reporting a truly unacceptable partner as its sole acceptable
choice. The general comparison also accepts arbitrary strict ranking reports.
-/

public import GameTheory.Cooperative.GaleShapley.Strategyproof
public import GameTheory.Tests.MatchingOptimality

@[expose] public section

noncomputable section

namespace GameTheory.Tests.MatchingStrategyproof

open MatchingMarket

/-- The comparison accepts every strict unilateral report in the contested
three-proposer market. -/
theorem contested_no_profitable_report (who : Matching.Left)
    (report : Option Matching.Right → Option Matching.Right → Prop)
    (linear : Rank.Linear report) :
    Matching.fixture.prefersLeft who
      (Matching.fixture.deferredAcceptance Matching.fixtureLinear who)
      ((Matching.fixture.withLeftReport who report).deferredAcceptance
        (Matching.fixture.withLeftReport_linear Matching.fixtureLinear who report linear) who) :=
  Matching.fixture.deferredAcceptance_strategyproof Matching.fixtureLinear who report linear

/-- Proposer zero's truthful assignment is its second choice, following the
actual rejection in the existing simultaneous DA process. -/
theorem truthful_contested_assignment :
    Matching.fixture.deferredAcceptance Matching.fixtureLinear 0 = some 1 := by
  have best := Matching.fixture.deferredAcceptance_proposerOptimal Matching.fixtureLinear
    Matching.finalMatching_isStable 0
  have rejected := MatchingOptimality.contested_rejection_excludes_every_stable_matching
    (Matching.fixture.deferredAcceptance_isStable Matching.fixtureLinear)
  cases chosen : Matching.fixture.deferredAcceptance Matching.fixtureLinear 0 with
  | none =>
      rw [chosen] at best
      norm_num [Matching.fixture, Matching.leftScore, Matching.finalMatching] at best
  | some right =>
      fin_cases right
      · exact False.elim (rejected chosen)
      · rfl
      · rw [chosen] at best
        norm_num [Matching.fixture, Matching.leftScore, Matching.finalMatching] at best

/-- The losing proposer declares only its rejected first choice acceptable. -/
abbrev rejectedOnly : MatchingMarket Matching.Left Matching.Right :=
  Matching.fixture.withLeftReport 0 (Rank.onlyAccept (Matching.fixture.prefersLeft 0) 0)

theorem rejectedOnly_linear : rejectedOnly.HasLinearPreferences :=
  Matching.fixture.withLeftReport_linear Matching.fixtureLinear 0 _
    (Rank.onlyAccept_linear (Matching.fixtureLinear.left 0) 0)

/-- Truncation at the rejected first choice causes the proposer to remain
unmatched, rather than recovering that choice. -/
theorem truncation_at_rejected_choice_unmatched :
    rejectedOnly.deferredAcceptance rejectedOnly_linear 0 = none := by
  have truthful := contested_no_profitable_report 0
    (Rank.onlyAccept (Matching.fixture.prefersLeft 0) 0)
    (Rank.onlyAccept_linear (Matching.fixtureLinear.left 0) 0)
  have stable := rejectedOnly.deferredAcceptance_isStable rejectedOnly_linear
  cases chosen : rejectedOnly.deferredAcceptance rejectedOnly_linear 0 with
  | none => rfl
  | some right =>
      have accepted := (stable.isIndividuallyRational 0 right chosen).1
      have equal : right = 0 := by
        simpa only [rejectedOnly, withLeftReport_self, Rank.onlyAccept_some_none_iff] using accepted
      subst right
      rw [truthful_contested_assignment, chosen] at truthful
      norm_num [Matching.fixture, Matching.leftScore] at truthful

/-- This market has one proposer, two receivers, and no truly acceptable
partner; arbitrary strict reports still cannot yield a preferred assignment. -/
theorem unacceptable_no_profitable_report (report : Option Bool → Option Bool → Prop)
    (linear : Rank.Linear report) :
    MatchingOptimality.unbalanced.prefersLeft () none
      ((MatchingOptimality.unbalanced.withLeftReport () report).deferredAcceptance
        (MatchingOptimality.unbalanced.withLeftReport_linear
          MatchingOptimality.unbalanced_linear () report linear) ()) := by
  simpa only [MatchingOptimality.unbalanced_da_unmatched] using
    MatchingOptimality.unbalanced.deferredAcceptance_strategyproof
      MatchingOptimality.unbalanced_linear () report linear

/-- A false report makes the truly worst partner the sole acceptable choice. -/
abbrev outsideReport : MatchingMarket Unit Bool :=
  MatchingOptimality.unbalanced.withLeftReport ()
    (Rank.onlyAccept (MatchingOptimality.unbalanced.prefersLeft ()) true)

theorem outsideReport_linear : outsideReport.HasLinearPreferences :=
  MatchingOptimality.unbalanced.withLeftReport_linear MatchingOptimality.unbalanced_linear () _
    (Rank.onlyAccept_linear (MatchingOptimality.unbalanced_linear.left ()) true)

private theorem outsideReport_partner_stable : outsideReport.IsStable (fun _ => some true) := by
  refine ⟨fun _ _ _ _ _ => Subsingleton.elim _ _, ?_, ?_⟩
  · intro left right paired
    cases left
    have equal : right = true := Option.some.inj paired.symm
    subst right
    constructor
    · simp only [outsideReport, withLeftReport_self, Rank.onlyAccept_some_none_iff]
    · exact Or.inl rfl
  · rintro ⟨left, right, blocks⟩
    cases left
    apply blocks.1.2
    change Rank.onlyAccept (MatchingOptimality.unbalanced.prefersLeft ()) true
      (some true) (some right)
    exact Rank.onlyAccept_top _ true (some right)

theorem outsideReport_assignment :
    outsideReport.deferredAcceptance outsideReport_linear () = some true := by
  have best := outsideReport.deferredAcceptance_proposerOptimal outsideReport_linear
    outsideReport_partner_stable ()
  apply (outsideReport_linear.left ()).2.2.2 _ _ best
  change Rank.onlyAccept (MatchingOptimality.unbalanced.prefersLeft ()) true
    (some true) (outsideReport.deferredAcceptance outsideReport_linear ())
  exact Rank.onlyAccept_top _ true _

/-- Changing acceptability can strictly harm a proposer: the outside option is
compared using the original ranking, even after a report excludes it. -/
theorem outsideReport_strictly_worse :
    Preference.strict MatchingOptimality.unbalanced.prefersLeft ()
      (MatchingOptimality.unbalanced.deferredAcceptance MatchingOptimality.unbalanced_linear ())
      (outsideReport.deferredAcceptance outsideReport_linear ()) := by
  rw [MatchingOptimality.unbalanced_da_unmatched, outsideReport_assignment]
  norm_num [Preference.strict, Rank.strict, MatchingOptimality.unbalanced,
    MatchingOptimality.unacceptableScore]

end GameTheory.Tests.MatchingStrategyproof
