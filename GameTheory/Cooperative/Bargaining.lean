import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Math.Probability

/-!
# Nash Bargaining Solution

The Nash bargaining solution (1950) selects a unique outcome for two-player
bargaining problems. Given a feasible set and a disagreement point, the
solution maximizes the product of utility gains.

## Main definitions

* `BargainingProblem` — a two-player bargaining problem
* `BargainingProblem.IsNashSolution` — the Nash bargaining solution
* `BargainingProblem.IsPareto` — Pareto optimality in the feasible set

## Main results

* `nashSolution_pareto` — Nash bargaining solution is Pareto optimal
* `nashSolution_symmetric` — symmetric bargaining yields equal gains
* `nashSolution_affine_invariant` — invariance under affine transformations
-/

namespace GameTheory

open Math.Probability

/-- A two-player bargaining problem. -/
structure BargainingProblem where
  /-- Feasible utility pairs. -/
  feasible : ℝ × ℝ → Prop
  /-- Disagreement point: player 1's fallback utility. -/
  d₁ : ℝ
  /-- Disagreement point: player 2's fallback utility. -/
  d₂ : ℝ
  /-- The disagreement point is feasible. -/
  d_feasible : feasible (d₁, d₂)

namespace BargainingProblem

variable (B : BargainingProblem)

/-- Individual rationality: both players get at least their disagreement payoff. -/
def IsIR (u : ℝ × ℝ) : Prop := u.1 ≥ B.d₁ ∧ u.2 ≥ B.d₂

/-- An outcome is Pareto optimal if no feasible outcome is strictly better
    for both players. -/
def IsPareto (u : ℝ × ℝ) : Prop :=
  B.feasible u ∧ ¬∃ v, B.feasible v ∧ v.1 > u.1 ∧ v.2 > u.2

/-- The Nash bargaining solution: a feasible, individually rational outcome
    that maximizes the Nash product `(u₁ - d₁) * (u₂ - d₂)`. -/
def IsNashSolution (u : ℝ × ℝ) : Prop :=
  B.feasible u ∧ B.IsIR u ∧
  ∀ v, B.feasible v → B.IsIR v →
    (u.1 - B.d₁) * (u.2 - B.d₂) ≥ (v.1 - B.d₁) * (v.2 - B.d₂)

/-- The Nash bargaining solution is individually rational. -/
theorem nashSolution_IR (u : ℝ × ℝ) (h : B.IsNashSolution u) : B.IsIR u :=
  h.2.1

/-- The Nash bargaining solution is Pareto optimal among IR-feasible outcomes. -/
theorem nashSolution_pareto (u : ℝ × ℝ) (h : B.IsNashSolution u) :
    ¬∃ v, B.feasible v ∧ B.IsIR v ∧ v.1 > u.1 ∧ v.2 > u.2 := by
  intro ⟨v, hfv, hir, h1, h2⟩
  have hiu := h.2.1
  have hmax := h.2.2 v hfv hir
  have hu1 : u.1 - B.d₁ ≥ 0 := by linarith [hiu.1]
  have hv2 : v.2 - B.d₂ > u.2 - B.d₂ := by linarith
  have hv2_pos : v.2 - B.d₂ > 0 := by linarith [hiu.2]
  have hv1 : v.1 - B.d₁ > u.1 - B.d₁ := by linarith
  nlinarith [mul_lt_mul_of_pos_right hv1 hv2_pos]

/-- A symmetric bargaining problem. -/
def IsSymmetric : Prop :=
  B.d₁ = B.d₂ ∧ ∀ u : ℝ × ℝ, B.feasible u → B.feasible (u.2, u.1)

/-- In a symmetric bargaining problem, the Nash solution gives equal gains
    to both players. -/
theorem nashSolution_symmetric (u : ℝ × ℝ) (hsym : B.IsSymmetric)
    (hns : B.IsNashSolution u)
    (huniq : ∀ v w, B.IsNashSolution v → B.IsNashSolution w → v = w) :
    u.1 - B.d₁ = u.2 - B.d₂ := by
  have hswap : B.IsNashSolution (u.2, u.1) := by
    refine ⟨hsym.2 u hns.1, ?_, ?_⟩
    · constructor
      · rw [hsym.1]; exact hns.2.1.2
      · rw [← hsym.1]; exact hns.2.1.1
    · intro v hfv hirv
      have hirv_swap : B.IsIR (v.2, v.1) := by
        constructor
        · rw [hsym.1]; exact hirv.2
        · rw [← hsym.1]; exact hirv.1
      have hfv_swap := hsym.2 v hfv
      have := hns.2.2 (v.2, v.1) hfv_swap hirv_swap
      rw [hsym.1] at this ⊢
      linarith [mul_comm (v.1 - B.d₂) (v.2 - B.d₂),
                mul_comm (u.2 - B.d₂) (u.1 - B.d₂)]
  have heq := huniq _ _ hns hswap
  have h1 : u.1 = (u.2, u.1).1 := by rw [← heq]
  simp at h1
  linarith [hsym.1]

/-- Scale invariance: affine transformations preserve the Nash solution. -/
theorem nashSolution_affine_invariant
    (α₁ α₂ : ℝ) (hα₁ : α₁ > 0) (hα₂ : α₂ > 0) (β₁ β₂ : ℝ)
    (u : ℝ × ℝ) (hns : B.IsNashSolution u) :
    let B' : BargainingProblem := {
      feasible := fun v => B.feasible ((v.1 - β₁) / α₁, (v.2 - β₂) / α₂)
      d₁ := α₁ * B.d₁ + β₁
      d₂ := α₂ * B.d₂ + β₂
      d_feasible := by simp [hα₁.ne', hα₂.ne', B.d_feasible]
    }
    B'.IsNashSolution (α₁ * u.1 + β₁, α₂ * u.2 + β₂) := by
  intro B'
  refine ⟨?_, ?_, ?_⟩
  · simp only [B']
    have h1 : (α₁ * u.1 + β₁ - β₁) / α₁ = u.1 := by
      rw [add_sub_cancel_right]; exact mul_div_cancel_left₀ u.1 hα₁.ne'
    have h2 : (α₂ * u.2 + β₂ - β₂) / α₂ = u.2 := by
      rw [add_sub_cancel_right]; exact mul_div_cancel_left₀ u.2 hα₂.ne'
    rw [h1, h2]
    exact hns.1
  · constructor
    · simp only [B']; nlinarith [hns.2.1.1]
    · simp only [B']; nlinarith [hns.2.1.2]
  · intro v hfv hirv
    simp only [B'] at hfv hirv ⊢
    have hv := hns.2.2 ((v.1 - β₁) / α₁, (v.2 - β₂) / α₂) hfv
    have hirv_orig : B.IsIR ((v.1 - β₁) / α₁, (v.2 - β₂) / α₂) := by
      constructor
      · rw [ge_iff_le]; rw [le_div_iff₀ hα₁]; nlinarith [hirv.1]
      · rw [ge_iff_le]; rw [le_div_iff₀ hα₂]; nlinarith [hirv.2]
    have hv' := hv hirv_orig
    have lhs : (α₁ * u.1 + β₁ - (α₁ * B.d₁ + β₁)) * (α₂ * u.2 + β₂ - (α₂ * B.d₂ + β₂)) =
        α₁ * α₂ * ((u.1 - B.d₁) * (u.2 - B.d₂)) := by ring
    have rhs : (v.1 - (α₁ * B.d₁ + β₁)) * (v.2 - (α₂ * B.d₂ + β₂)) =
        α₁ * α₂ * (((v.1 - β₁) / α₁ - B.d₁) * ((v.2 - β₂) / α₂ - B.d₂)) := by
      field_simp; ring
    rw [lhs, rhs]
    exact mul_le_mul_of_nonneg_left hv' (by positivity)

end BargainingProblem

end GameTheory
