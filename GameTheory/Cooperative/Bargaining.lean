/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Math.Probability

/-!
# Nash Bargaining Solution

The Nash bargaining solution (1950) characterizes the outcome of a two-player
bargaining problem as the feasible, individually-rational point maximizing the
product of utility gains. This file formalizes that characterization as a
predicate `IsNashSolution` over arbitrary bargaining problems; uniqueness is not
asserted, and theorems that need it (e.g. symmetry) take it as an explicit
hypothesis.

## Main definitions

* `BargainingProblem` — a two-player bargaining problem
* `BargainingProblem.IsNashSolution` — the Nash bargaining solution
* `BargainingProblem.IsPareto` — Pareto optimality (strong) in the feasible set,
  with the weaker `IsWeaklyPareto`
* `BargainingProblem.posAffineMap` — the positive-affine image of a problem (the
  shared transform behind the Nash and Kalai–Smorodinsky scale-invariance results)

## Main results

* `nashSolution_weaklyPareto` — Nash bargaining solution is weakly Pareto optimal
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

/-- An outcome is *Pareto optimal* if no feasible outcome is at least as good for
    both players and strictly better for at least one. This is the standard
    (strong) notion that the unqualified name denotes; the weaker variant is
    `IsWeaklyPareto`. -/
def IsPareto (u : ℝ × ℝ) : Prop :=
  B.feasible u ∧ ¬∃ v, B.feasible v ∧ v.1 ≥ u.1 ∧ v.2 ≥ u.2 ∧ (v.1 > u.1 ∨ v.2 > u.2)

/-- An outcome is *weakly* Pareto optimal if no feasible outcome is strictly
    better for both players (a weaker condition than `IsPareto`). -/
def IsWeaklyPareto (u : ℝ × ℝ) : Prop :=
  B.feasible u ∧ ¬∃ v, B.feasible v ∧ v.1 > u.1 ∧ v.2 > u.2

/-- Pareto optimality implies the weak form. -/
theorem isWeaklyPareto_of_isPareto {u : ℝ × ℝ} (h : B.IsPareto u) :
    B.IsWeaklyPareto u :=
  ⟨h.1, fun ⟨v, hfv, h1, h2⟩ => h.2 ⟨v, hfv, le_of_lt h1, le_of_lt h2, Or.inl h1⟩⟩

/-- The Nash bargaining solution: a feasible, individually rational outcome
    that maximizes the Nash product `(u₁ - d₁) * (u₂ - d₂)`. -/
def IsNashSolution (u : ℝ × ℝ) : Prop :=
  B.feasible u ∧ B.IsIR u ∧
  ∀ v, B.feasible v → B.IsIR v →
    (u.1 - B.d₁) * (u.2 - B.d₂) ≥ (v.1 - B.d₁) * (v.2 - B.d₂)

/-- The Nash bargaining solution is individually rational. -/
theorem nashSolution_IR (u : ℝ × ℝ) (h : B.IsNashSolution u) : B.IsIR u :=
  h.2.1

/-- The Nash bargaining solution is weakly Pareto optimal: no feasible outcome is
    strictly better for both players. (In this general non-convex setting the
    strong form can fail on the disagreement boundary.) A strict improvement over
    the IR Nash solution is itself IR, so no IR restriction on the dominator is
    needed. -/
theorem nashSolution_weaklyPareto (u : ℝ × ℝ) (h : B.IsNashSolution u) :
    B.IsWeaklyPareto u := by
  refine ⟨h.1, ?_⟩
  rintro ⟨v, hfv, h1, h2⟩
  have hiu := h.2.1
  have hir : B.IsIR v := ⟨by linarith [hiu.1], by linarith [hiu.2]⟩
  have hmax := h.2.2 v hfv hir
  have hu1 : u.1 - B.d₁ ≥ 0 := by linarith [hiu.1]
  have hv2 : v.2 - B.d₂ > u.2 - B.d₂ := by linarith
  have hv2_pos : v.2 - B.d₂ > 0 := by linarith [hiu.2]
  have hv1 : v.1 - B.d₁ > u.1 - B.d₁ := by linarith
  nlinarith [mul_lt_mul_of_pos_right hv1 hv2_pos]

/-- A symmetric bargaining problem. -/
def IsSymmetric : Prop :=
  B.d₁ = B.d₂ ∧ ∀ u : ℝ × ℝ, B.feasible u → B.feasible (u.2, u.1)

/-- In a symmetric bargaining problem, a Nash solution that is unique (the
    explicit `huniq` hypothesis) gives equal gains to both players. -/
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

/-- The **positive-affine image** of a bargaining problem: rescale player `i`'s
utility by `αᵢ > 0` and shift by `βᵢ`. Feasibility pulls back along the inverse
transform; the disagreement point maps forward. The Nash and Kalai–Smorodinsky
solutions are invariant under this map (scale invariance). -/
def posAffineMap (α₁ α₂ : ℝ) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) (β₁ β₂ : ℝ) :
    BargainingProblem where
  feasible := fun v => B.feasible ((v.1 - β₁) / α₁, (v.2 - β₂) / α₂)
  d₁ := α₁ * B.d₁ + β₁
  d₂ := α₂ * B.d₂ + β₂
  d_feasible := by simp [hα₁.ne', hα₂.ne', B.d_feasible]

/-- Feasibility transports along `posAffineMap`: the affine image of `u` is feasible
in the image problem iff `u` is feasible in the original. -/
theorem posAffineMap_feasible_image {α₁ α₂ : ℝ} (hα₁ : 0 < α₁) (hα₂ : 0 < α₂)
    {β₁ β₂ : ℝ} (u : ℝ × ℝ) :
    (B.posAffineMap α₁ α₂ hα₁ hα₂ β₁ β₂).feasible (α₁ * u.1 + β₁, α₂ * u.2 + β₂)
      ↔ B.feasible u := by
  have e₁ : (α₁ * u.1 + β₁ - β₁) / α₁ = u.1 := by
    rw [add_sub_cancel_right]; exact mul_div_cancel_left₀ u.1 hα₁.ne'
  have e₂ : (α₂ * u.2 + β₂ - β₂) / α₂ = u.2 := by
    rw [add_sub_cancel_right]; exact mul_div_cancel_left₀ u.2 hα₂.ne'
  simp only [posAffineMap, e₁, e₂]

/-- Individual rationality transports along `posAffineMap`. -/
theorem posAffineMap_isIR_image {α₁ α₂ : ℝ} (hα₁ : 0 < α₁) (hα₂ : 0 < α₂)
    {β₁ β₂ : ℝ} (u : ℝ × ℝ) :
    (B.posAffineMap α₁ α₂ hα₁ hα₂ β₁ β₂).IsIR (α₁ * u.1 + β₁, α₂ * u.2 + β₂)
      ↔ B.IsIR u := by
  simp only [posAffineMap, IsIR]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨le_of_mul_le_mul_left (by linarith) hα₁,
      le_of_mul_le_mul_left (by linarith) hα₂⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by nlinarith [mul_le_mul_of_nonneg_left h1 hα₁.le],
      by nlinarith [mul_le_mul_of_nonneg_left h2 hα₂.le]⟩

/-- Scale invariance: positive-affine transformations preserve the Nash solution. -/
theorem nashSolution_affine_invariant
    (α₁ α₂ : ℝ) (hα₁ : α₁ > 0) (hα₂ : α₂ > 0) (β₁ β₂ : ℝ)
    (u : ℝ × ℝ) (hns : B.IsNashSolution u) :
    (B.posAffineMap α₁ α₂ hα₁ hα₂ β₁ β₂).IsNashSolution
      (α₁ * u.1 + β₁, α₂ * u.2 + β₂) := by
  refine ⟨(B.posAffineMap_feasible_image hα₁ hα₂ u).mpr hns.1,
    (B.posAffineMap_isIR_image hα₁ hα₂ u).mpr hns.2.1, ?_⟩
  intro v hfv hirv
  simp only [posAffineMap] at hfv hirv ⊢
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

/-! ### Egalitarian bargaining solution

The egalitarian solution (Kalai 1977) selects the unique feasible
individually-rational point on the 45° line through the disagreement
point. Both players gain the same amount from cooperation, which is
the *largest* common gain that remains feasible. This is a
non-utility-comparable alternative to Nash bargaining; the chief
difference is that the egalitarian solution is **not** scale
invariant — it depends on the cardinal utility scale. -/

/-- An outcome is the *egalitarian* (Kalai) solution of `B` if it is feasible,
individually rational, gives both players equal gain over the disagreement point,
and is the feasible equal-gain point with the *largest* common gain. -/
def IsEgalitarian (u : ℝ × ℝ) : Prop :=
  B.feasible u ∧ B.IsIR u ∧ u.1 - B.d₁ = u.2 - B.d₂ ∧
    ∀ v, B.feasible v → v.1 - B.d₁ = v.2 - B.d₂ → v.1 ≤ u.1

/-- The egalitarian solution is individually rational by definition. -/
theorem egalitarian_IR (u : ℝ × ℝ) (h : B.IsEgalitarian u) : B.IsIR u :=
  h.2.1

/-- The egalitarian solution gives equal gain to both players. -/
theorem egalitarian_equal_gain (u : ℝ × ℝ) (h : B.IsEgalitarian u) :
    u.1 - B.d₁ = u.2 - B.d₂ :=
  h.2.2.1

/-- The egalitarian solution gives the largest common gain among feasible
equal-gain outcomes. -/
theorem egalitarian_maximal (u : ℝ × ℝ) (h : B.IsEgalitarian u)
    {v : ℝ × ℝ} (hfv : B.feasible v) (hv : v.1 - B.d₁ = v.2 - B.d₂) :
    v.1 ≤ u.1 :=
  h.2.2.2 v hfv hv

/-- In a symmetric problem the egalitarian solution gives each player at least the
common gain of the (unique) symmetric Nash solution: the latter also lies on the
equal-gains line, where the egalitarian solution maximizes the common gain. -/
theorem nashSolution_le_egalitarian
    (u v : ℝ × ℝ) (hsym : B.IsSymmetric)
    (heg : B.IsEgalitarian u) (hns : B.IsNashSolution v)
    (huniq : ∀ x w, B.IsNashSolution x → B.IsNashSolution w → x = w) :
    v.1 ≤ u.1 :=
  heg.2.2.2 v hns.1 (B.nashSolution_symmetric v hsym hns huniq)

/-! ### Kalai–Smorodinsky bargaining solution

The Kalai–Smorodinsky solution (1975) replaces Nash's *independence of
irrelevant alternatives* with a *monotonicity* axiom. It selects the
Pareto-optimal outcome at which both players' gains are **proportional to
their maximal feasible gains** — the gains at the *ideal* (utopia) point
`a = (a₁, a₂)`, where `aᵢ` is the most player `i` could obtain among
individually-rational feasible outcomes. Unlike the egalitarian solution it
**is** scale invariant; unlike the Nash solution it is monotone. -/

/-- `a` is an *ideal* (utopia) point of `B`: each coordinate is the least
upper bound of that player's payoff over individually-rational feasible
outcomes. The Kalai–Smorodinsky solution is defined relative to such a point. -/
def IsIdealPoint (a : ℝ × ℝ) : Prop :=
  IsLUB {x | ∃ u, B.feasible u ∧ B.IsIR u ∧ u.1 = x} a.1 ∧
  IsLUB {x | ∃ u, B.feasible u ∧ B.IsIR u ∧ u.2 = x} a.2

/-- The Kalai–Smorodinsky outcome *relative to* a point `a`: a Pareto-optimal,
individually-rational, feasible outcome whose gains over the disagreement point
are proportional to the `a`-gains, i.e.
`(u₁ - d₁) / (a₁ - d₁) = (u₂ - d₂) / (a₂ - d₂)`, written in the division-free form
`(u₁ - d₁)(a₂ - d₂) = (u₂ - d₂)(a₁ - d₁)`. The properties below hold for any `a`;
the Kalai–Smorodinsky *solution* additionally fixes `a` to be the ideal point. -/
def IsKalaiSmorodinskyRelativeTo (a u : ℝ × ℝ) : Prop :=
  B.feasible u ∧ B.IsIR u ∧ B.IsPareto u ∧
    (u.1 - B.d₁) * (a.2 - B.d₂) = (u.2 - B.d₂) * (a.1 - B.d₁)

/-- The **Kalai–Smorodinsky solution**: the Kalai–Smorodinsky outcome relative to
the *ideal* (utopia) point `a`, so proportionality is measured against each
player's maximal feasible gain. -/
def IsKalaiSmorodinsky (a u : ℝ × ℝ) : Prop :=
  B.IsIdealPoint a ∧ B.IsKalaiSmorodinskyRelativeTo a u

/-- The Kalai–Smorodinsky outcome is individually rational by definition. -/
theorem kalaiSmorodinskyRelativeTo_IR (a u : ℝ × ℝ)
    (h : B.IsKalaiSmorodinskyRelativeTo a u) : B.IsIR u :=
  h.2.1

/-- The Kalai–Smorodinsky outcome is Pareto optimal by definition. -/
theorem kalaiSmorodinskyRelativeTo_pareto (a u : ℝ × ℝ)
    (h : B.IsKalaiSmorodinskyRelativeTo a u) : B.IsPareto u :=
  h.2.2.1

/-- The Kalai–Smorodinsky outcome equalizes the ratio of each player's gain
to their `a`-gain. -/
theorem kalaiSmorodinskyRelativeTo_proportional (a u : ℝ × ℝ)
    (h : B.IsKalaiSmorodinskyRelativeTo a u) :
    (u.1 - B.d₁) * (a.2 - B.d₂) = (u.2 - B.d₂) * (a.1 - B.d₁) :=
  h.2.2.2

/-- With a symmetric point (`a₁ = a₂`), the Kalai–Smorodinsky outcome gives equal
gains to both players, provided the problem is nondegenerate (`a₁ ≠ d₁`). -/
theorem kalaiSmorodinskyRelativeTo_symmetric (a u : ℝ × ℝ)
    (hsym : B.IsSymmetric) (ha : a.1 = a.2) (hnd : a.1 - B.d₁ ≠ 0)
    (h : B.IsKalaiSmorodinskyRelativeTo a u) :
    u.1 - B.d₁ = u.2 - B.d₂ := by
  have hd : B.d₂ = B.d₁ := hsym.1.symm
  have hprop := h.2.2.2
  rw [← ha, hd] at hprop
  have hcancel : u.1 - B.d₁ = u.2 - B.d₁ := mul_right_cancel₀ hnd hprop
  rw [hd]
  exact hcancel

/-- **Scale invariance.** The Kalai–Smorodinsky outcome is preserved under
independent positive-affine rescaling of the two players' utilities, with the
reference point rescaled along with the problem. This is the axiom distinguishing
KS from the (scale-dependent) egalitarian solution. -/
theorem kalaiSmorodinskyRelativeTo_affine_invariant
    (α₁ α₂ : ℝ) (hα₁ : α₁ > 0) (hα₂ : α₂ > 0) (β₁ β₂ : ℝ)
    (a u : ℝ × ℝ) (h : B.IsKalaiSmorodinskyRelativeTo a u) :
    (B.posAffineMap α₁ α₂ hα₁ hα₂ β₁ β₂).IsKalaiSmorodinskyRelativeTo
      (α₁ * a.1 + β₁, α₂ * a.2 + β₂) (α₁ * u.1 + β₁, α₂ * u.2 + β₂) := by
  obtain ⟨hfu, hiru, hpu, hprop⟩ := h
  refine ⟨(B.posAffineMap_feasible_image hα₁ hα₂ u).mpr hfu,
    (B.posAffineMap_isIR_image hα₁ hα₂ u).mpr hiru,
    ⟨(B.posAffineMap_feasible_image hα₁ hα₂ u).mpr hfu, ?_⟩, ?_⟩
  · -- strong Pareto: a weakly-dominating image gives a weakly-dominating preimage
    rintro ⟨w, hfw, hw1, hw2, hwstrict⟩
    simp only [posAffineMap] at hfw
    apply hpu.2
    refine ⟨((w.1 - β₁) / α₁, (w.2 - β₂) / α₂), hfw, ?_, ?_, ?_⟩
    · rw [ge_iff_le, le_div_iff₀ hα₁]; nlinarith [hw1]
    · rw [ge_iff_le, le_div_iff₀ hα₂]; nlinarith [hw2]
    · rcases hwstrict with hs | hs
      · exact Or.inl (by rw [gt_iff_lt, lt_div_iff₀ hα₁]; nlinarith [hs])
      · exact Or.inr (by rw [gt_iff_lt, lt_div_iff₀ hα₂]; nlinarith [hs])
  · -- proportionality is preserved: both sides scale by α₁ * α₂
    simp only [posAffineMap]
    have lhs : (α₁ * u.1 + β₁ - (α₁ * B.d₁ + β₁)) * (α₂ * a.2 + β₂ - (α₂ * B.d₂ + β₂)) =
        α₁ * α₂ * ((u.1 - B.d₁) * (a.2 - B.d₂)) := by ring
    have rhs : (α₂ * u.2 + β₂ - (α₂ * B.d₂ + β₂)) * (α₁ * a.1 + β₁ - (α₁ * B.d₁ + β₁)) =
        α₁ * α₂ * ((u.2 - B.d₂) * (a.1 - B.d₁)) := by ring
    rw [lhs, rhs, hprop]

/-- The Kalai–Smorodinsky solution is dominated by the ideal point: neither player
can exceed its maximal feasible (utopia) payoff. Together with individual
rationality this places each player's gain in `[0, ideal gain]`. -/
theorem kalaiSmorodinsky_le_ideal (a u : ℝ × ℝ) (h : B.IsKalaiSmorodinsky a u) :
    u.1 ≤ a.1 ∧ u.2 ≤ a.2 := by
  obtain ⟨hideal, hfeas, hIR, _, _⟩ := h
  exact ⟨hideal.1.1 ⟨u, hfeas, hIR, rfl⟩, hideal.2.1 ⟨u, hfeas, hIR, rfl⟩⟩

end BargainingProblem

end GameTheory
