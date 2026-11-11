module

public import GameTheory.Math.FiniteChoice
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

@[expose] public section

noncomputable section

namespace GameTheory.Experimental.RestrictedBudget

open GameTheory.Math

abbrev Bundle := ℕ × ℕ

def quantities : Finset Bundle := {(0, 0), (1, 0), (0, 1), (2, 0), (1, 1), (0, 2)}
def smallMenu : Finset Bundle := {(0, 0), (1, 0), (0, 1)}
def u (q : Bundle) : ℕ := 5 * q.1 + 2 * q.2
def v (q : Bundle) : ℕ := 5 * q.1 + 2 * q.2 ^ 2

def budget (p0 p1 : ℕ) (wealth : ℝ) : Finset Bundle :=
  quantities.filter fun q => ((p0 * q.1 + p1 * q.2 : ℕ) : ℝ) ≤ wealth

def choices (score : Bundle → ℕ) (p0 p1 : ℕ) (wealth : ℝ) : Set Bundle :=
  FiniteChoice.best (fun chosen alternative => score alternative ≤ score chosen)
    (budget p0 p1 wealth)

private theorem best_eq_singleton (score : Bundle → ℕ) (menu : Finset Bundle)
    (winner : Bundle) (member : winner ∈ menu)
    (bound : ∀ alternative ∈ menu, score alternative ≤ score winner)
    (unique : ∀ alternative ∈ menu, score winner ≤ score alternative → alternative = winner) :
    FiniteChoice.best (fun chosen alternative => score alternative ≤ score chosen) menu =
      {winner} := by
  ext chosen
  constructor
  · rintro ⟨offered, maximal⟩
    exact unique chosen offered (maximal winner member)
  · rintro rfl
    exact ⟨member, bound⟩

theorem budget_negative {wealth : ℝ} (negative : wealth < 0) : budget 1 1 wealth = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro q member
  have affordable := (Finset.mem_filter.mp member).2
  have nonnegative : (0 : ℝ) ≤ ((1 * q.1 + 1 * q.2 : ℕ) : ℝ) := Nat.cast_nonneg _
  linarith

theorem budget_below_one {wealth : ℝ} (nonnegative : 0 ≤ wealth) (below : wealth < 1) :
    budget 1 1 wealth = {(0, 0)} := by
  ext q
  constructor
  · intro offered
    obtain ⟨member, affordable⟩ := Finset.mem_filter.mp offered
    simp only [quantities, Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num at affordable ⊢ <;> linarith
  · intro offered
    obtain rfl := Finset.mem_singleton.mp offered
    simpa [budget, quantities] using nonnegative

theorem budget_below_two {wealth : ℝ} (above : 1 ≤ wealth) (below : wealth < 2) :
    budget 1 1 wealth = smallMenu := by
  ext q
  constructor
  · intro offered
    obtain ⟨member, affordable⟩ := Finset.mem_filter.mp offered
    simp only [quantities, Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [smallMenu] at affordable ⊢ <;> linarith
  · intro member
    simp only [smallMenu, Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl | rfl <;>
      norm_num [budget, quantities] <;> linarith

theorem budget_above_two {wealth : ℝ} (above : 2 ≤ wealth) :
    budget 1 1 wealth = quantities := by
  apply Finset.filter_eq_self.mpr
  intro q member
  simp only [quantities, Finset.mem_insert, Finset.mem_singleton] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num <;> linarith

theorem best_u_smallMenu :
    FiniteChoice.best (fun chosen alternative => u alternative ≤ u chosen)
      smallMenu = {(1, 0)} := by
  apply best_eq_singleton u smallMenu (1, 0) (by simp [smallMenu])
  · intro alternative member
    simp only [smallMenu, Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl | rfl <;> norm_num [u]
  · intro alternative member lower
    simp only [smallMenu, Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl | rfl <;> norm_num [u] at *

theorem best_u_quantities :
    FiniteChoice.best (fun chosen alternative => u alternative ≤ u chosen)
      quantities = {(2, 0)} := by
  apply best_eq_singleton u quantities (2, 0) (by simp [quantities])
  · intro alternative member
    simp only [quantities, Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [u]
  · intro alternative member lower
    simp only [quantities, Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [u] at *

theorem best_v_smallMenu :
    FiniteChoice.best (fun chosen alternative => v alternative ≤ v chosen)
      smallMenu = {(1, 0)} := by
  apply best_eq_singleton v smallMenu (1, 0) (by simp [smallMenu])
  · intro alternative member
    simp only [smallMenu, Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl | rfl <;> norm_num [v]
  · intro alternative member lower
    simp only [smallMenu, Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl | rfl <;> norm_num [v] at *

theorem best_v_quantities :
    FiniteChoice.best (fun chosen alternative => v alternative ≤ v chosen)
      quantities = {(2, 0)} := by
  apply best_eq_singleton v quantities (2, 0) (by simp [quantities])
  · intro alternative member
    simp only [quantities, Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [v]
  · intro alternative member lower
    simp only [quantities, Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [v] at *

/-- Every real wealth level at the observed price vector gives the same
choices, including empty budgets and the two price thresholds. -/
theorem all_wealth_observational_equality (wealth : ℝ) : choices u 1 1 wealth = choices v 1 1 wealth := by
  by_cases negative : wealth < 0
  · simp [choices, budget_negative negative, FiniteChoice.best]
  · have nonnegative : 0 ≤ wealth := le_of_not_gt negative
    by_cases belowOne : wealth < 1
    · have singleton (score : Bundle → ℕ) :
          FiniteChoice.best (fun chosen alternative => score alternative ≤ score chosen)
            {(0, 0)} = {(0, 0)} := by
        apply best_eq_singleton score {(0, 0)} (0, 0) (by simp)
        · intro alternative member
          obtain rfl := Finset.mem_singleton.mp member
          exact le_rfl
        · intro alternative member _
          exact Finset.mem_singleton.mp member
      simp only [choices, budget_below_one nonnegative belowOne, singleton]
    · have aboveOne : 1 ≤ wealth := le_of_not_gt belowOne
      by_cases belowTwo : wealth < 2
      · simp only [choices, budget_below_two aboveOne belowTwo,
          best_u_smallMenu, best_v_smallMenu]
      · have aboveTwo : 2 ≤ wealth := le_of_not_gt belowTwo
        simp only [choices, budget_above_two aboveTwo, best_u_quantities, best_v_quantities]

/-- The observations do not identify the ranking of these two feasible bundles. -/
theorem strict_ranking_reversal : u (0, 2) < u (1, 1) ∧ v (1, 1) < v (0, 2) := by
  norm_num [u, v]

theorem changed_prices_select_u : choices u 2 1 3 = {(1, 1)} := by
  apply best_eq_singleton u (budget 2 1 3) (1, 1)
    (by norm_num [budget, quantities])
  · intro alternative offered
    obtain ⟨member, affordable⟩ := Finset.mem_filter.mp offered
    simp only [quantities, Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [u] at *
  · intro alternative offered lower
    obtain ⟨member, affordable⟩ := Finset.mem_filter.mp offered
    simp only [quantities, Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [u] at *

theorem changed_prices_select_v : choices v 2 1 3 = {(0, 2)} := by
  apply best_eq_singleton v (budget 2 1 3) (0, 2)
    (by norm_num [budget, quantities])
  · intro alternative offered
    obtain ⟨member, affordable⟩ := Finset.mem_filter.mp offered
    simp only [quantities, Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [v] at *
  · intro alternative offered lower
    obtain ⟨member, affordable⟩ := Finset.mem_filter.mp offered
    simp only [quantities, Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [v] at *

/-- Both scores strictly value a one-unit increase of either commodity. -/
theorem positive_coordinate_increments (x y : ℕ) :
    u (x, y) < u (x + 1, y) ∧ u (x, y) < u (x, y + 1) ∧
      v (x, y) < v (x + 1, y) ∧ v (x, y) < v (x, y + 1) := by
  dsimp [u, v]
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · nlinarith [Nat.zero_le y]

/-- Both observations arise from globally rationalizable choice; the failure
is identification, not the existence of a consistent rationalization. -/
theorem both_global_choices_consistent :
    FiniteChoice.WeakAxiom (FiniteChoice.best
      (fun chosen alternative : Bundle => u alternative ≤ u chosen)) ∧
    FiniteChoice.WeakAxiom (FiniteChoice.best
      (fun chosen alternative : Bundle => v alternative ≤ v chosen)) := by
  constructor <;> apply FiniteChoice.best_weakAxiom <;>
    exact fun _ _ _ first second => second.trans first

end GameTheory.Experimental.RestrictedBudget
