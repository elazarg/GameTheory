/-
# Hostile stable-matching fixture

Three agents on each side force both an initial rejection and a later partner
replacement.  The final assertions distinguish stability from mere
one-to-one validity and perfectness from stability in an unbalanced or
unacceptable market.
-/

import GameTheory.Cooperative.GaleShapley.Perfect
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

namespace GameTheory.Tests.Matching

open GameTheory
open MatchingMarket

abbrev Left := Fin 3
abbrev Right := Fin 3

def leftScore (left : Left) : Option Right → Nat
  | none => 0
  | some right =>
      match left.val, right.val with
      | 0, 0 => 3
      | 0, 1 => 2
      | 0, _ => 1
      | 1, 0 => 3
      | 1, 1 => 2
      | 1, _ => 1
      | _, 1 => 3
      | _, 0 => 2
      | _, _ => 1

def rightScore (right : Right) : Option Left → Nat
  | none => 0
  | some left =>
      match right.val, left.val with
      | 0, 1 => 3
      | 0, 0 => 2
      | 0, _ => 1
      | 1, 0 => 3
      | 1, 2 => 2
      | 1, _ => 1
      | _, 2 => 3
      | _, 1 => 2
      | _, _ => 1

def fixture : MatchingMarket Left Right where
  prefersLeft left preferred alternative :=
    leftScore left preferred ≥ leftScore left alternative
  prefersRight right preferred alternative :=
    rightScore right preferred ≥ rightScore right alternative

theorem fixtureLinear : fixture.HasLinearPreferences := by
  have leftInjective : ∀ left, Function.Injective (leftScore left) := by
    intro left first second heq
    fin_cases left <;> fin_cases first <;> fin_cases second <;>
      simp [leftScore] at heq ⊢
  have rightInjective : ∀ right, Function.Injective (rightScore right) := by
    intro right first second heq
    fin_cases right <;> fin_cases first <;> fin_cases second <;>
      simp [rightScore] at heq ⊢
  constructor
  · intro left
    refine ⟨fun _ => by simp [fixture], ?_, ?_, ?_⟩
    · intro preferred middle alternative h₁ h₂
      exact Nat.le_trans h₂ h₁
    · intro preferred alternative
      exact Nat.le_total _ _ |>.symm
    · intro preferred alternative h₁ h₂
      apply leftInjective left
      exact Nat.le_antisymm h₂ h₁
  · intro right
    refine ⟨fun _ => by simp [fixture], ?_, ?_, ?_⟩
    · intro preferred middle alternative h₁ h₂
      exact Nat.le_trans h₂ h₁
    · intro preferred alternative
      exact Nat.le_total _ _ |>.symm
    · intro preferred alternative h₁ h₂
      apply rightInjective right
      exact Nat.le_antisymm h₂ h₁

theorem fixtureAcceptable : fixture.HasCompleteAcceptability := by
  constructor
  · intro left right
    fin_cases left <;> fin_cases right <;>
      norm_num [fixture, Preference.strict, Rank.strict, leftScore]
  · intro right left
    fin_cases right <;> fin_cases left <;>
      norm_num [fixture, Preference.strict, Rank.strict, rightScore]

def emptyRejections : Left → Finset Right := fun _ => ∅

theorem left0_top_empty :
    fixture.topChoice fixtureLinear emptyRejections 0 = some 0 := by
  apply fixture.topChoice_eq_of_isBest fixtureLinear
  · rw [fixture.mem_available]
    norm_num [emptyRejections, MatchingMarket.AcceptableToLeft, fixture, leftScore]
  · intro alternative hmem
    rw [fixture.mem_available] at hmem
    fin_cases alternative <;>
      norm_num [emptyRejections, MatchingMarket.AcceptableToLeft,
        fixture, leftScore] at hmem ⊢

theorem left1_top_empty :
    fixture.topChoice fixtureLinear emptyRejections 1 = some 0 := by
  apply fixture.topChoice_eq_of_isBest fixtureLinear
  · rw [fixture.mem_available]
    norm_num [emptyRejections, MatchingMarket.AcceptableToLeft, fixture, leftScore]
  · intro alternative hmem
    rw [fixture.mem_available] at hmem
    fin_cases alternative <;>
      norm_num [emptyRejections, MatchingMarket.AcceptableToLeft,
        fixture, leftScore] at hmem ⊢

theorem left2_top_empty :
    fixture.topChoice fixtureLinear emptyRejections 2 = some 1 := by
  apply fixture.topChoice_eq_of_isBest fixtureLinear
  · rw [fixture.mem_available]
    norm_num [emptyRejections, MatchingMarket.AcceptableToLeft, fixture, leftScore]
  · intro alternative hmem
    rw [fixture.mem_available] at hmem
    fin_cases alternative <;>
      norm_num [emptyRejections, MatchingMarket.AcceptableToLeft,
        fixture, leftScore] at hmem ⊢

theorem right0_holds_left1_empty :
    fixture.holder fixtureLinear emptyRejections 0 = some 1 := by
  apply fixture.holder_eq_of_isBest fixtureLinear
  · rw [fixture.mem_suitors fixtureLinear]
    exact ⟨left1_top_empty, by
      norm_num [MatchingMarket.AcceptableToRight, fixture, rightScore]⟩
  · intro alternative _
    fin_cases alternative <;> norm_num [fixture, rightScore]

theorem right1_holds_left2_empty :
    fixture.holder fixtureLinear emptyRejections 1 = some 2 := by
  apply fixture.holder_eq_of_isBest fixtureLinear
  · rw [fixture.mem_suitors fixtureLinear]
    exact ⟨left2_top_empty, by
      norm_num [MatchingMarket.AcceptableToRight, fixture, rightScore]⟩
  · intro alternative hmem
    rw [fixture.mem_suitors fixtureLinear] at hmem
    fin_cases alternative
    · have htop : fixture.topChoice fixtureLinear emptyRejections 0 = some 1 := by
        simpa using hmem.1
      have hcontr := left0_top_empty.symm.trans htop
      norm_num at hcontr
    · have htop : fixture.topChoice fixtureLinear emptyRejections 1 = some 1 := by
        simpa using hmem.1
      have hcontr := left1_top_empty.symm.trans htop
      norm_num at hcontr
    · norm_num [fixture, rightScore]

/-- The first simultaneous round rejects left agent zero from right agent
zero: two agents proposed there, and right zero retains left one. -/
theorem first_round_rejects_left0 :
    (0 : Right) ∈ fixture.daStep fixtureLinear emptyRejections 0 := by
  simp [MatchingMarket.daStep, left0_top_empty, right0_holds_left1_empty]

def afterFirstRejection : Left → Finset Right := fun left =>
  if left = 0 then {0} else ∅

/-- The named state is the actual result of the first simultaneous round, not
an arbitrary state chosen to make the replacement possible. -/
theorem firstRound_eq_afterFirstRejection :
    fixture.daStep fixtureLinear emptyRejections = afterFirstRejection := by
  funext left
  fin_cases left <;> ext right <;> fin_cases right <;>
    simp [MatchingMarket.daStep, emptyRejections, afterFirstRejection,
      left0_top_empty, left1_top_empty, left2_top_empty,
      right0_holds_left1_empty, right1_holds_left2_empty]

theorem left0_top_afterFirst :
    fixture.topChoice fixtureLinear afterFirstRejection 0 = some 1 := by
  apply fixture.topChoice_eq_of_isBest fixtureLinear
  · rw [fixture.mem_available]
    norm_num [afterFirstRejection, MatchingMarket.AcceptableToLeft, fixture, leftScore]
  · intro alternative hmem
    rw [fixture.mem_available] at hmem
    fin_cases alternative
    · simp [afterFirstRejection] at hmem
    · norm_num [fixture, leftScore]
    · norm_num [fixture, leftScore]

theorem left1_top_afterFirst :
    fixture.topChoice fixtureLinear afterFirstRejection 1 = some 0 := by
  apply fixture.topChoice_eq_of_isBest fixtureLinear
  · rw [fixture.mem_available]
    simp [afterFirstRejection, MatchingMarket.AcceptableToLeft, fixture, leftScore]
  · intro alternative hmem
    rw [fixture.mem_available] at hmem
    fin_cases alternative <;> norm_num [fixture, leftScore]

theorem left2_top_afterFirst :
    fixture.topChoice fixtureLinear afterFirstRejection 2 = some 1 := by
  apply fixture.topChoice_eq_of_isBest fixtureLinear
  · rw [fixture.mem_available]
    simp [afterFirstRejection, MatchingMarket.AcceptableToLeft, fixture, leftScore]
  · intro alternative hmem
    rw [fixture.mem_available] at hmem
    fin_cases alternative <;> norm_num [fixture, leftScore]

theorem right1_holds_left0_afterFirst :
    fixture.holder fixtureLinear afterFirstRejection 1 = some 0 := by
  apply fixture.holder_eq_of_isBest fixtureLinear
  · rw [fixture.mem_suitors fixtureLinear]
    exact ⟨left0_top_afterFirst, by
      norm_num [MatchingMarket.AcceptableToRight, fixture, rightScore]⟩
  · intro alternative hmem
    rw [fixture.mem_suitors fixtureLinear] at hmem
    fin_cases alternative <;>
      norm_num [left0_top_afterFirst, left1_top_afterFirst,
        left2_top_afterFirst, fixture, rightScore] at hmem ⊢

/-- After that rejection, left zero proposes to right one, who replaces left
two by the strictly preferred left zero. -/
theorem hostile_partner_replacement :
    fixture.holder fixtureLinear emptyRejections 1 = some 2 ∧
      fixture.holder fixtureLinear afterFirstRejection 1 = some 0 :=
  ⟨right1_holds_left2_empty, right1_holds_left0_afterFirst⟩

def finalMatching : Matching Left Right
  | 0 => some 1
  | 1 => some 0
  | _ => some 2

theorem finalMatching_isStable : fixture.IsStable finalMatching := by
  refine ⟨?_, ?_, ?_⟩
  · intro left₁ left₂ right h₁ h₂
    fin_cases left₁ <;> fin_cases left₂ <;> fin_cases right <;>
      simp [finalMatching] at h₁ h₂ ⊢
  · intro left right hmatch
    fin_cases left <;> fin_cases right <;>
      simp [finalMatching] at hmatch
    all_goals norm_num [fixture, leftScore, rightScore]
  · rintro ⟨left, right, _, rightMatched, _⟩
    have hcurrent : ∃ current,
        finalMatching current = some right ∧
          fixture.prefersRight right (some current) (some left) := by
      fin_cases right
      · refine ⟨1, rfl, ?_⟩
        fin_cases left <;> norm_num [fixture, rightScore]
      · refine ⟨0, rfl, ?_⟩
        fin_cases left <;> norm_num [fixture, rightScore]
      · refine ⟨2, rfl, ?_⟩
        fin_cases left <;> norm_num [fixture, rightScore]
    obtain ⟨current, hmatch, htop⟩ := hcurrent
    exact (rightMatched current hmatch).2 htop

theorem finalMatching_isPerfect : IsPerfect finalMatching := by
  constructor
  · intro left
    fin_cases left
    · exact ⟨1, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨2, rfl⟩
  · intro right
    fin_cases right
    · exact ⟨1, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨2, rfl⟩

def unstableMatching : Matching Left Right
  | 0 => some 0
  | 1 => some 1
  | _ => some 2

/-- Left one and right zero are a concrete blocking pair. -/
theorem unstable_has_blocking_pair :
    fixture.IsBlockingPair unstableMatching 1 0 := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [unstableMatching, fixture, Preference.strict, Rank.strict,
      leftScore]
  · intro left hmatch
    fin_cases left
    · norm_num [fixture, Preference.strict, Rank.strict, rightScore]
    · simp [unstableMatching] at hmatch
    · simp [unstableMatching] at hmatch
  · intro hunmatched
    exact False.elim (hunmatched 0 rfl)

theorem unstableMatching_not_stable :
    ¬ fixture.IsStable unstableMatching := by
  intro stable
  exact stable.not_isBlockingPair 1 0 unstable_has_blocking_pair

/-- The general finite theorem specializes to this genuinely contested
market. -/
theorem fixture_exists_perfect_stable :
    ∃ matching : Matching Left Right,
      fixture.IsStable matching ∧ IsPerfect matching :=
  fixture.exists_perfect_stable fixtureLinear (by decide) fixtureAcceptable

#print axioms Rank.exists_best_finset
#print axioms MatchingMarket.exists_stable
#print axioms MatchingMarket.stable_matching_perfect
#print axioms fixture_exists_perfect_stable

end GameTheory.Tests.Matching
