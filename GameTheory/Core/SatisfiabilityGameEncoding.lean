import GameTheory.Core.SatisfiabilityGame
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod

/-! Explicit row indices for the literal/clause game: positive literals,
negative literals, variables, clauses, and the fallback action. -/

namespace GameTheory.SatisfiabilityGame

/-- Enumerate the actions in the order used by the explicit payoff table. -/
def actionEquiv (n m : ℕ) : Action n m ≃ Fin (3 * n + m + 1) :=
  (Equiv.sumCongr
    ((Equiv.prodComm (Fin n) Bool).trans
      ((Equiv.boolProdEquivSum (Fin n)).trans
        ((Equiv.sumComm _ _).trans finSumFinEquiv)))
    ((Equiv.sumCongr (Equiv.refl (Fin n))
      ((Equiv.sumCongr (Equiv.refl (Fin m)) finOneEquiv.symm).trans finSumFinEquiv)).trans
      finSumFinEquiv)).trans (finSumFinEquiv.trans (finCongr (by omega)))

/-- Total table lookup; indices outside the action range select the fallback. -/
def actionAt (n m i : ℕ) : Action n m :=
  if h₀ : i < n then literal ⟨i, h₀⟩ true
  else if h₁ : i < 2 * n then literal ⟨i - n, by omega⟩ false
  else if h₂ : i < 3 * n then variableAction ⟨i - 2 * n, by omega⟩
  else if h₃ : i < 3 * n + m then clause ⟨i - 3 * n, by omega⟩
  else fallback

@[simp] theorem actionEquiv_literal_true {n m : ℕ} (v : Fin n) :
    (actionEquiv n m (literal v true)).val = v.val := rfl

@[simp] theorem actionEquiv_literal_false {n m : ℕ} (v : Fin n) :
    (actionEquiv n m (literal v false)).val = n + v.val := by
  rfl

@[simp] theorem actionEquiv_variable {n m : ℕ} (v : Fin n) :
    (actionEquiv n m (variableAction v)).val = 2 * n + v.val := by
  change n + n + v.val = _
  omega

@[simp] theorem actionEquiv_clause {n m : ℕ} (c : Fin m) :
    (actionEquiv n m (clause c)).val = 3 * n + c.val := by
  change n + n + (n + c.val) = _
  omega

@[simp] theorem actionEquiv_fallback {n m : ℕ} :
    (actionEquiv n m (fallback : Action n m)).val = 3 * n + m := by
  change n + n + (n + (m + 0)) = _
  omega

/-- The executable lookup is inverse to the explicit action enumeration. -/
theorem actionAt_index {n m : ℕ} (a : Action n m) :
    actionAt n m (actionEquiv n m a).val = a := by
  rcases a with ⟨v, b⟩ | (v | (c | u))
  · cases b
    · change actionAt n m (actionEquiv n m (literal v false)).val = literal v false
      rw [actionEquiv_literal_false]
      simp only [actionAt]
      split_ifs <;> try omega
      congr 2
      omega
    · change actionAt n m (actionEquiv n m (literal v true)).val = literal v true
      rw [actionEquiv_literal_true]
      simp [actionAt, v.isLt, literal]
  · change actionAt n m (actionEquiv n m (variableAction v)).val = variableAction v
    rw [actionEquiv_variable]
    simp only [actionAt]
    split_ifs <;> try omega
    congr 2
    omega
  · change actionAt n m (actionEquiv n m (clause c)).val = clause c
    rw [actionEquiv_clause]
    simp only [actionAt]
    split_ifs <;> try omega
    congr 2
    omega
  · cases u
    change actionAt n m (actionEquiv n m (fallback : Action n m)).val = fallback
    rw [actionEquiv_fallback]
    simp only [actionAt]
    split_ifs <;> try omega
    rfl

theorem actionAt_eq_symm {n m : ℕ} (i : Fin (3 * n + m + 1)) :
    actionAt n m i.val = (actionEquiv n m).symm i := by
  have h := actionAt_index ((actionEquiv n m).symm i)
  rwa [Equiv.apply_symm_apply] at h

end GameTheory.SatisfiabilityGame
