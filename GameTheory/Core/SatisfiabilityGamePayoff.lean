import GameTheory.Core.SatisfiabilityGameEncoding

/-! Natural indices compute the literal/clause payoff by numeric case analysis.
The numeric evaluator agrees with the canonical payoff after action lookup. -/

namespace GameTheory.SatisfiabilityGame

/-- Extend finite clause incidence to natural indices, returning false outside
the declared variable and clause ranges. -/
def clauseAt {n m : ℕ} (C : Clauses n m) (c v : ℕ) (b : Bool) : Bool :=
  if hc : c < m then if hv : v < n then C ⟨c, hc⟩ ⟨v, hv⟩ b else false else false

@[simp] theorem clauseAt_fin {n m : ℕ} (C : Clauses n m) (c : Fin m) (v : Fin n) (b : Bool) :
    clauseAt C c v b = C c v b := by simp [clauseAt, c.isLt, v.isLt]

/-- The row-major payoff computation uses only numeric action-range tests and
the canonical clause-incidence lookup. -/
def indexedPayoff {n m : ℕ} (C : Clauses n m) (i j : ℕ) : ℤ :=
  let rowVar := if i < n then i else i - n
  let colVar := if j < n then j else j - n
  if i = 3 * n + m then if j = 3 * n + m then 0 else 1
  else if i < 2 * n then
    if j < 2 * n then
      if rowVar = colVar ∧ decide (i < n) ≠ decide (j < n) then -2 else 1
    else -2
  else if i < 3 * n then
    if j < 2 * n then if i - 2 * n = colVar then 2 - n else 2 else -2
  else if i < 3 * n + m then
    if j < 2 * n then
      if clauseAt C (i - 3 * n) colVar (decide (j < n)) then 2 - n else 2
    else -2
  else -2

/-- Every in-range numeric payoff is the canonical payoff of the corresponding
enumerated actions. No nonemptiness assumption on either carrier is needed. -/
theorem payoffInt_actionAt {n m : ℕ} (C : Clauses n m) (i j : ℕ)
    (hi : i < 3 * n + m + 1) (hj : j < 3 * n + m + 1) :
    payoffInt C (actionAt n m i) (actionAt n m j) = indexedPayoff C i j := by
  unfold actionAt
  split_ifs
  all_goals
    dsimp only [literal, variableAction, clause, fallback, payoffInt, indexedPayoff]
    try simp only [Fin.ext_iff]
    try split_ifs
    all_goals try omega
  all_goals simp_all [clauseAt] <;> omega

end GameTheory.SatisfiabilityGame
