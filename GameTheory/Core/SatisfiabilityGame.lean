import GameTheory.Core.BimatrixGame
import GameTheory.Math.Probability.Uniform

/-! A finite literal/clause game turns satisfiability into existence of a mixed
Nash equilibrium giving both players payoff at least one. This is the
Conitzer–Sandholm literal/clause gadget: actions name literals, variables,
clauses, or a fallback; no action encodes a whole assignment. -/

noncomputable section

namespace GameTheory.SatisfiabilityGame

open GameTheory.Math.Probability

/-- Literal, variable, clause, and fallback actions. -/
abbrev Action (n m : ℕ) := (Fin n × Bool) ⊕ (Fin n ⊕ (Fin m ⊕ Unit))

/-- Play the signed literal of a variable. -/
def literal {n m : ℕ} (v : Fin n) (b : Bool) : Action n m := .inl (v, b)
/-- Challenge the opponent's probability mass on a variable. -/
def variableAction {n m : ℕ} (v : Fin n) : Action n m := .inr (.inl v)
/-- Challenge the opponent's probability mass on literals satisfying a clause. -/
def clause {n m : ℕ} (c : Fin m) : Action n m := .inr (.inr (.inl c))
/-- The safe action sustaining a zero-payoff equilibrium. -/
def fallback {n m : ℕ} : Action n m := .inr (.inr (.inr ()))

/-- Clause incidence records whether the signed variable occurs in the clause. -/
abbrev Clauses (n m : ℕ) := Fin m → Fin n → Bool → Bool

/-- An assignment satisfies every clause when each contains a true literal. -/
def Satisfies {n m : ℕ} (C : Clauses n m) (τ : Fin n → Bool) : Prop :=
  ∀ c, ∃ v, C c v (τ v) = true

/-- Integer row payoff; the column player receives the same function with the
action arguments swapped. -/
def payoffInt {n m : ℕ} (C : Clauses n m) : Action n m → Action n m → ℤ
  | .inl (v, b), .inl (w, d) => if v = w ∧ b ≠ d then -2 else 1
  | .inr (.inl v), .inl (w, _) => if v = w then 2 - n else 2
  | .inr (.inr (.inl c)), .inl (v, b) => if C c v b then 2 - n else 2
  | .inr (.inr (.inr _)), .inr (.inr (.inr _)) => 0
  | .inr (.inr (.inr _)), _ => 1
  | _, _ => -2

/-- Interpret the executable integer payoff in real expected-utility semantics. -/
def payoff {n m : ℕ} (C : Clauses n m) (a b : Action n m) : ℝ := payoffInt C a b

/-- The gadget is an ordinary canonical two-player utility game. -/
@[reducible] def game {n m : ℕ} (C : Clauses n m) : UtilityGame (Fin 2) :=
  MatrixGame.bimatrixGame (payoff C) (fun a b => payoff C b a)

/-- Expected row payoff under independent mixed actions. -/
def value {n m : ℕ} (C : Clauses n m) (p q : PMF (Action n m)) : ℝ :=
  expect (bindPairLaw p (fun _ => q)) (fun x => payoff C x.1 x.2)

/-- The canonical Nash predicate needs only the two pure-deviation tests. -/
theorem isNash_iff {n m : ℕ} (C : Clauses n m) (p q : PMF (Action n m)) :
    IsNash (game C).form.mixed (euPreference (game C).utility) (MatrixGame.mixedProfile p q) ↔
      (∀ a, expect q (payoff C a) ≤ value C p q) ∧
      (∀ b, expect p (payoff C b) ≤ value C q p) := by
  have heq : expect (bindPairLaw p (fun _ => q)) (fun x => payoff C x.2 x.1) =
      value C q p := by
    rw [value, ← bindPairLaw_const_map_swap p q, expect_map]
    rfl
  rw [MatrixGame.isNash_bimatrix_iff, heq]
  rfl

end GameTheory.SatisfiabilityGame
