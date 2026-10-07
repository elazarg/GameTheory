import GameTheory.Core.SatisfiabilityGame

/-! A satisfying assignment yields a mixed equilibrium of the literal/clause
game by drawing its selected literals uniformly over the variables. -/

noncomputable section

namespace GameTheory.SatisfiabilityGame

open GameTheory.Math.Probability
open scoped BigOperators

/-- The assignment-selected literal of a uniformly chosen variable. -/
def assignmentLaw {n m : ℕ} [NeZero n] (τ : Fin n → Bool) : PMF (Action n m) :=
  (PMF.uniformOfFintype (Fin n)).map (fun v => literal v (τ v))

theorem payoff_assignment_literals {n m : ℕ} (C : Clauses n m) (τ : Fin n → Bool)
    (v w : Fin n) : payoff C (literal v (τ v)) (literal w (τ w)) = 1 := by
  by_cases h : v = w
  · subst w; simp [payoff, payoffInt, literal]
  · simp [payoff, payoffInt, literal, h]

theorem expect_variable_assignment {n m : ℕ} [NeZero n] (C : Clauses n m)
    (τ : Fin n → Bool) (v : Fin n) :
    expect (assignmentLaw (m := m) τ) (payoff C (variableAction v)) = 1 := by
  rw [assignmentLaw, expect_map, expect_uniformOfFintype]
  have hsum : (∑ w : Fin n, payoff C (variableAction v) (literal w (τ w))) = (n : ℝ) := by
    calc
      _ = ∑ w : Fin n, (2 - if w = v then (n : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro w _
        by_cases h : w = v
        · subst w; simp [payoff, payoffInt, variableAction, literal]
        · simp [payoff, payoffInt, variableAction, literal, h, Ne.symm h]
      _ = _ := by simp [Finset.sum_sub_distrib]; ring
  change (∑ w : Fin n, payoff C (variableAction v) (literal w (τ w))) / Fintype.card (Fin n) = 1
  rw [hsum, Fintype.card_fin, div_self (by exact_mod_cast NeZero.ne n)]

theorem value_assignment {n m : ℕ} [NeZero n] (C : Clauses n m) (τ : Fin n → Bool) :
    value C (assignmentLaw τ) (assignmentLaw τ) = 1 := by
  rw [value, expect_bindPairLaw_tower _ _ _ (payoffIntegrable_of_finite _ _)]
  rw [assignmentLaw, expect_map]
  have hinner (v : Fin n) :
      expect (assignmentLaw (m := m) τ) (payoff C (literal v (τ v))) = 1 := by
    rw [assignmentLaw, expect_map]
    simpa only [Function.comp_def, payoff_assignment_literals] using
      expect_constant (PMF.uniformOfFintype (Fin n)) 1
  change expect (PMF.uniformOfFintype (Fin n)) (fun v =>
    expect (assignmentLaw τ) (payoff C (literal v (τ v)))) = 1
  simp only [hinner, expect_constant]

/-- Every pure deviation has payoff at most one against a satisfying assignment. -/
theorem deviation_le_one {n m : ℕ} [NeZero n] (C : Clauses n m) (τ : Fin n → Bool)
    (hτ : Satisfies C τ) (a : Action n m) : expect (assignmentLaw τ) (payoff C a) ≤ 1 := by
  rcases a with ⟨v, b⟩ | v | c | u
  · rw [assignmentLaw, expect_map]
    apply expect_le_const _ _ (payoffIntegrable_of_finite _ _) 1
    intro w _
    change payoff C (literal v b) (literal w (τ w)) ≤ 1
    simp only [payoff, payoffInt, literal]
    split_ifs <;> norm_num
  · exact (expect_variable_assignment C τ v).le
  · obtain ⟨v, hv⟩ := hτ c
    rw [← expect_variable_assignment C τ v]
    rw [assignmentLaw, expect_map, expect_map]
    apply expect_mono _ (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)
    intro w _
    change payoff C (clause c) (literal w (τ w)) ≤ payoff C (variableAction v) (literal w (τ w))
    by_cases h : v = w
    · subst w; simp [payoff, payoffInt, clause, variableAction, literal, hv]
    · simp only [payoff, payoffInt, clause, variableAction, literal, ite_eq_right h]
      split_ifs <;> push_cast <;> linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
  · rw [assignmentLaw, expect_map]
    have h : ∀ w : Fin n, payoff C (.inr (.inr (.inr u))) (literal w (τ w)) = 1 := by
      intro w; simp [payoff, payoffInt, literal]
    simpa only [Function.comp_def, h] using (expect_constant (PMF.uniformOfFintype (Fin n)) 1).le

/-- A satisfying assignment provides an ordinary mixed Nash equilibrium with
both payoffs equal to one. -/
theorem assignment_isNash {n m : ℕ} [NeZero n] (C : Clauses n m) (τ : Fin n → Bool)
    (hτ : Satisfies C τ) :
    IsNash (game C).form.mixed (euPreference (game C).utility)
      (MatrixGame.mixedProfile (assignmentLaw τ) (assignmentLaw τ)) := by
  apply (isNash_iff C _ _).mpr
  rw [value_assignment]
  exact ⟨deviation_le_one C τ hτ, deviation_le_one C τ hτ⟩

end GameTheory.SatisfiabilityGame
