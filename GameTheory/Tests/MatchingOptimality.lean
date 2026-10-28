module

/-
# Distinct stable matchings and proposer optimality

Both the diagonal and crossed matchings are stable. Every proposer strictly
prefers the diagonal, while every receiver strictly prefers the crossed
matching. The deferred-acceptance theorem must select the proposer endpoint,
not merely certify the existence of an arbitrary stable matching.
-/

public import GameTheory.Cooperative.GaleShapley.Optimality
public import GameTheory.Tests.Matching
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace GameTheory.Tests.MatchingOptimality

open MatchingMarket

def leftScore (left : Bool) : Option Bool → ℕ
  | none => 0
  | some right => if right = left then 2 else 1

def rightScore (right : Bool) : Option Bool → ℕ
  | none => 0
  | some left => if left = right then 1 else 2

def market : MatchingMarket Bool Bool where
  prefersLeft left first second := leftScore left second ≤ leftScore left first
  prefersRight right first second := rightScore right second ≤ rightScore right first

private theorem linear_of_score {α : Type*} (score : α → ℕ)
    (injective : Function.Injective score) :
    Rank.Linear (fun first second => score second ≤ score first) :=
  ⟨fun _ => le_rfl, fun _ _ _ h₁ h₂ => h₂.trans h₁,
    fun _ _ => le_total _ _, fun _ _ h₁ h₂ => injective (le_antisymm h₂ h₁)⟩

theorem market_linear : market.HasLinearPreferences := by
  constructor
  · intro left
    apply linear_of_score
    intro first second equality
    cases left <;> fin_cases first <;> fin_cases second <;> simp_all [leftScore]
  · intro right
    apply linear_of_score
    intro first second equality
    cases right <;> fin_cases first <;> fin_cases second <;> simp_all [rightScore]

def diagonal : Matching Bool Bool := some

def crossed : Matching Bool Bool := fun left => some (!left)

theorem diagonal_stable : market.IsStable diagonal := by
  refine ⟨?_, ?_, ?_⟩
  · intro first second right firstMatch secondMatch
    exact Option.some.inj (firstMatch.trans secondMatch.symm)
  · intro left right _
    change 0 ≤ leftScore left (some right) ∧ 0 ≤ rightScore right (some left)
    exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  · rintro ⟨left, right, blocking⟩
    have improves := blocking.1.2
    cases left <;> cases right <;>
      norm_num [market, leftScore, diagonal] at improves

theorem crossed_stable : market.IsStable crossed := by
  refine ⟨?_, ?_, ?_⟩
  · intro first second right firstMatch secondMatch
    have same := Option.some.inj (firstMatch.trans secondMatch.symm)
    cases first <;> cases second <;> simp_all [crossed]
  · intro left right _
    change 0 ≤ leftScore left (some right) ∧ 0 ≤ rightScore right (some left)
    exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  · rintro ⟨left, right, blocking⟩
    have improves := (blocking.2.1 (!right) (by simp [crossed])).2
    cases left <;> cases right <;>
      norm_num [market, rightScore] at improves

theorem stable_endpoints_distinct : diagonal ≠ crossed := by
  intro equal
  have := congrFun equal false
  simp [diagonal, crossed] at this

theorem proposer_strictly_prefers_diagonal (left : Bool) :
    Preference.strict market.prefersLeft left (diagonal left) (crossed left) := by
  cases left <;> norm_num [Preference.strict, Rank.strict, market, leftScore, diagonal, crossed]

theorem receiver_strictly_prefers_crossed (right : Bool) :
    Preference.strict market.prefersRight right (some (!right)) (some right) := by
  cases right <;> norm_num [Preference.strict, Rank.strict, market, rightScore]

/-- The general comparison theorem selects the proposers' endpoint among two
distinct stable matchings. -/
theorem deferredAcceptance_eq_diagonal :
    market.deferredAcceptance market_linear = diagonal := by
  funext left
  have best (alternative : Option Bool) : market.prefersLeft left (diagonal left) alternative := by
    cases left <;> fin_cases alternative <;> norm_num [market, leftScore, diagonal]
  exact (market_linear.left left).2.2.2 _ _
    (market.deferredAcceptance_proposerOptimal market_linear diagonal_stable left) (best _)

/-- Stability alone does not imply proposer optimality. -/
theorem crossed_not_proposerOptimal :
    ¬ (∀ matching, market.IsStable matching →
      ∀ left, market.prefersLeft left (crossed left) (matching left)) := by
  intro optimal
  exact (proposer_strictly_prefers_diagonal false).2 (optimal diagonal diagonal_stable false)

/-- A rejection in the existing contested three-agent market excludes the
pair from every stable matching, rather than just the algorithm's output. -/
theorem contested_rejection_excludes_every_stable_matching
    {matching : Matching Matching.Left Matching.Right}
    (stable : Matching.fixture.IsStable matching) : matching 0 ≠ some 0 := by
  intro paired
  apply Matching.fixture.stable_partner_not_rejected_iterate Matching.fixtureLinear 1 stable paired
  exact Matching.first_round_rejects_left0

def unacceptableScore : Option Bool → ℕ
  | none => 2
  | some false => 1
  | some true => 0

/-- One proposer, two receivers, and no acceptable partner for the proposer. -/
def unbalanced : MatchingMarket Unit Bool where
  prefersLeft _ first second := unacceptableScore second ≤ unacceptableScore first
  prefersRight _ first second := second = none ∨ first = some ()

theorem unbalanced_linear : unbalanced.HasLinearPreferences := by
  constructor
  · intro _
    apply linear_of_score
    intro first second equality
    fin_cases first <;> fin_cases second <;> simp_all [unacceptableScore]
  · intro _
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro item; fin_cases item <;> simp [unbalanced]
    · intro first middle last h₁ h₂
      fin_cases first <;> fin_cases middle <;> fin_cases last <;> simp_all [unbalanced]
    · intro first second
      fin_cases first <;> fin_cases second <;> simp [unbalanced]
    · intro first second h₁ h₂
      fin_cases first <;> fin_cases second <;> simp_all [unbalanced]

theorem unbalanced_empty_stable : unbalanced.IsStable (fun _ => none) := by
  apply unbalanced.empty_stable_if_all_prefer_unmatched
  intro left right
  cases right <;>
    norm_num [Preference.strict, Rank.strict, unbalanced, unacceptableScore]

/-- Optional partners are compared directly; no balancedness or complete
acceptability premise is hidden in proposer optimality. -/
theorem unbalanced_da_unmatched : unbalanced.deferredAcceptance unbalanced_linear () = none := by
  have optimal := unbalanced.deferredAcceptance_proposerOptimal unbalanced_linear
    unbalanced_empty_stable ()
  cases chosen : unbalanced.deferredAcceptance unbalanced_linear () with
  | none => rfl
  | some right =>
      rw [chosen] at optimal
      cases right <;> norm_num [unbalanced, unacceptableScore] at optimal

end GameTheory.Tests.MatchingOptimality
