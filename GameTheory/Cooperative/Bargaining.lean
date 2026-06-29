/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Math.Probability

/-!
# Nash Bargaining Solution

The Nash bargaining solution (1950) characterizes the outcome of an `n`-player
bargaining problem as the feasible, individually-rational point maximizing the
product of utility gains. This file formalizes that characterization as a
predicate `IsNashSolution` over arbitrary bargaining problems indexed by a
finite player type `ι`; uniqueness is not asserted, and theorems that need it
(e.g. symmetry) take it as an explicit hypothesis.

Players are indexed by a `Fintype ι`; a utility profile is a function
`ι → ℝ`. The feasible set is `feasible : (ι → ℝ) → Prop` and the disagreement
point is `d : ι → ℝ`. Specializing `ι := Fin 2` (or `Bool`) recovers the
classical two-player theory.

## Main definitions

* `BargainingProblem ι` — an `n`-player bargaining problem
* `BargainingProblem.IsNashSolution` — the Nash bargaining solution: maximizer of
  the Nash product `∏ i, (u i - d i)` over individually-rational feasible points
* `BargainingProblem.IsPareto` — Pareto optimality (strong) in the feasible set,
  with the weaker `IsWeaklyPareto`
* `BargainingProblem.posAffineMap` — the positive-affine image of a problem (the
  shared transform behind the Nash and Kalai–Smorodinsky scale-invariance results)
* `BargainingProblem.IsEgalitarian` — the egalitarian (Kalai) solution
* `BargainingProblem.IsKalaiSmorodinsky` — the Kalai–Smorodinsky solution

## Main results

* `nashSolution_weaklyPareto` — Nash bargaining solution is weakly Pareto optimal
* `nashSolution_symmetric` — symmetric bargaining yields equal gains to all players
* `nashSolution_affine_invariant` — invariance under positive-affine transformations
-/

namespace GameTheory

open Math.Probability

variable {ι : Type*}

/-- An `n`-player bargaining problem over a player type `ι`. The disagreement
point and feasible set are unconstrained; only the Nash-product results below
require `ι` finite. -/
structure BargainingProblem (ι : Type*) where
  /-- Feasible utility profiles. -/
  feasible : (ι → ℝ) → Prop
  /-- Disagreement point: each player's fallback utility. -/
  d : ι → ℝ
  /-- The disagreement point is feasible. -/
  d_feasible : feasible d

namespace BargainingProblem

variable (B : BargainingProblem ι)

/-- Individual rationality: every player gets at least their disagreement payoff. -/
def IsIR (u : ι → ℝ) : Prop := ∀ i, u i ≥ B.d i

/-- An outcome is *Pareto optimal* if no feasible outcome is at least as good for
    every player and strictly better for at least one. This is the standard
    (strong) notion that the unqualified name denotes; the weaker variant is
    `IsWeaklyPareto`. -/
def IsPareto (u : ι → ℝ) : Prop :=
  B.feasible u ∧ ¬∃ v, B.feasible v ∧ (∀ i, v i ≥ u i) ∧ (∃ i, v i > u i)

/-- An outcome is *weakly* Pareto optimal if no feasible outcome is strictly
    better for *every* player (a weaker condition than `IsPareto`). -/
def IsWeaklyPareto (u : ι → ℝ) : Prop :=
  B.feasible u ∧ ¬∃ v, B.feasible v ∧ ∀ i, v i > u i

/-- Pareto optimality implies the weak form (when there is at least one player). -/
theorem isWeaklyPareto_of_isPareto [Nonempty ι] {u : ι → ℝ} (h : B.IsPareto u) :
    B.IsWeaklyPareto u := by
  refine ⟨h.1, ?_⟩
  rintro ⟨v, hfv, hstrict⟩
  exact h.2 ⟨v, hfv, fun i => le_of_lt (hstrict i), Classical.arbitrary ι, hstrict _⟩

/-- The Nash bargaining solution: a feasible, individually rational outcome
    that maximizes the Nash product `∏ i, (u i - d i)`. -/
def IsNashSolution [Fintype ι] (u : ι → ℝ) : Prop :=
  B.feasible u ∧ B.IsIR u ∧
  ∀ v, B.feasible v → B.IsIR v →
    ∏ i, (u i - B.d i) ≥ ∏ i, (v i - B.d i)

/-- The Nash bargaining solution is individually rational. -/
theorem nashSolution_IR [Fintype ι] (u : ι → ℝ) (h : B.IsNashSolution u) : B.IsIR u :=
  h.2.1

/-- The Nash bargaining solution is weakly Pareto optimal: no feasible outcome is
    strictly better for *every* player. (In this general non-convex setting the
    strong form can fail on the disagreement boundary.) A strict improvement over
    the IR Nash solution is itself IR, so no IR restriction on the dominator is
    needed. -/
theorem nashSolution_weaklyPareto [Fintype ι] [Nonempty ι] (u : ι → ℝ) (h : B.IsNashSolution u) :
    B.IsWeaklyPareto u := by
  refine ⟨h.1, ?_⟩
  rintro ⟨v, hfv, hstrict⟩
  have hu := h.2.1
  have hir : B.IsIR v := fun i => le_of_lt (lt_of_le_of_lt (hu i) (hstrict i))
  have hmax := h.2.2 v hfv hir
  have hvpos : ∀ i, 0 < v i - B.d i := fun i => by linarith [hu i, hstrict i]
  have hvprodpos : 0 < ∏ i, (v i - B.d i) := Finset.prod_pos (fun i _ => hvpos i)
  by_cases hupos : ∀ i, 0 < u i - B.d i
  · have hlt : ∏ i, (u i - B.d i) < ∏ i, (v i - B.d i) :=
      Finset.prod_lt_prod_of_nonempty (fun i _ => hupos i)
        (fun i _ => by linarith [hstrict i]) Finset.univ_nonempty
    linarith
  · obtain ⟨i₀, hi₀⟩ := not_forall.mp hupos
    rw [not_lt] at hi₀
    have hz : u i₀ - B.d i₀ = 0 := le_antisymm hi₀ (by linarith [hu i₀])
    have huprod0 : ∏ i, (u i - B.d i) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i₀) hz
    rw [huprod0] at hmax
    linarith

/-- A symmetric bargaining problem: every player has the same disagreement payoff
and the feasible set is invariant under permutations of players. -/
def IsSymmetric : Prop :=
  (∀ i j, B.d i = B.d j) ∧
    ∀ (σ : Equiv.Perm ι) (u : ι → ℝ), B.feasible u → B.feasible (u ∘ σ)

/-- In a symmetric bargaining problem, a Nash solution that is unique (the
explicit `huniq` hypothesis) gives equal gains to all players. -/
theorem nashSolution_symmetric [Fintype ι] (u : ι → ℝ) (hsym : B.IsSymmetric)
    (hns : B.IsNashSolution u)
    (huniq : ∀ v w, B.IsNashSolution v → B.IsNashSolution w → v = w) :
    ∀ i j, u i - B.d i = u j - B.d j := by
  classical
  obtain ⟨hdconst, hinv⟩ := hsym
  -- For any permutation `σ`, the permuted profile is again a Nash solution.
  have hperm : ∀ σ : Equiv.Perm ι, B.IsNashSolution (u ∘ σ) := by
    intro σ
    have hprod : ∏ i, ((u ∘ σ) i - B.d i) = ∏ i, (u i - B.d i) := by
      calc ∏ i, ((u ∘ σ) i - B.d i)
          = ∏ i, (u (σ i) - B.d (σ i)) := by
            apply Finset.prod_congr rfl
            intro i _
            simp only [Function.comp_apply]
            rw [hdconst i (σ i)]
        _ = ∏ i, (u i - B.d i) := Equiv.prod_comp σ (fun j => u j - B.d j)
    refine ⟨hinv σ u hns.1, ?_, ?_⟩
    · intro i
      change u (σ i) ≥ B.d i
      rw [hdconst i (σ i)]
      exact hns.2.1 (σ i)
    · intro v hfv hirv
      rw [hprod]
      exact hns.2.2 v hfv hirv
  intro i j
  have heq : u = u ∘ Equiv.swap i j := huniq u (u ∘ Equiv.swap i j) hns (hperm _)
  have huij : u i = u j := by
    have hci := congrFun heq i
    simpa [Equiv.swap_apply_left] using hci
  rw [huij, hdconst i j]

/-- The **positive-affine image** of a bargaining problem: rescale player `i`'s
utility by `α i > 0` and shift by `β i`. Feasibility pulls back along the inverse
transform; the disagreement point maps forward. The Nash and Kalai–Smorodinsky
solutions are invariant under this map (scale invariance). -/
def posAffineMap (α : ι → ℝ) (hα : ∀ i, 0 < α i) (β : ι → ℝ) :
    BargainingProblem ι where
  feasible := fun v => B.feasible (fun i => (v i - β i) / α i)
  d := fun i => α i * B.d i + β i
  d_feasible := by
    change B.feasible (fun i => (α i * B.d i + β i - β i) / α i)
    have h : (fun i => (α i * B.d i + β i - β i) / α i) = B.d := by
      funext i
      rw [add_sub_cancel_right, mul_div_cancel_left₀ (B.d i) (hα i).ne']
    rw [h]; exact B.d_feasible

/-- Feasibility transports along `posAffineMap`: the affine image of `u` is feasible
in the image problem iff `u` is feasible in the original. -/
theorem posAffineMap_feasible_image {α : ι → ℝ} (hα : ∀ i, 0 < α i) {β : ι → ℝ}
    (u : ι → ℝ) :
    (B.posAffineMap α hα β).feasible (fun i => α i * u i + β i) ↔ B.feasible u := by
  have h : (fun i => (α i * u i + β i - β i) / α i) = u := by
    funext i
    rw [add_sub_cancel_right, mul_div_cancel_left₀ (u i) (hα i).ne']
  simp only [posAffineMap, h]

/-- Individual rationality transports along `posAffineMap`. -/
theorem posAffineMap_isIR_image {α : ι → ℝ} (hα : ∀ i, 0 < α i) {β : ι → ℝ}
    (u : ι → ℝ) :
    (B.posAffineMap α hα β).IsIR (fun i => α i * u i + β i) ↔ B.IsIR u := by
  simp only [posAffineMap, IsIR]
  constructor
  · intro h i
    exact le_of_mul_le_mul_left (by linarith [h i]) (hα i)
  · intro h i
    nlinarith [mul_le_mul_of_nonneg_left (h i) (hα i).le]

/-- Scale invariance: positive-affine transformations preserve the Nash solution. -/
theorem nashSolution_affine_invariant [Fintype ι]
    (α : ι → ℝ) (hα : ∀ i, 0 < α i) (β : ι → ℝ)
    (u : ι → ℝ) (hns : B.IsNashSolution u) :
    (B.posAffineMap α hα β).IsNashSolution (fun i => α i * u i + β i) := by
  refine ⟨(B.posAffineMap_feasible_image hα u).mpr hns.1,
    (B.posAffineMap_isIR_image hα u).mpr hns.2.1, ?_⟩
  intro v hfv hirv
  simp only [posAffineMap] at hfv hirv ⊢
  -- preimage of `v`
  have hirw : B.IsIR (fun i => (v i - β i) / α i) := by
    intro i
    rw [ge_iff_le, le_div_iff₀ (hα i)]
    nlinarith [hirv i]
  have hmax := hns.2.2 (fun i => (v i - β i) / α i) hfv hirw
  -- both Nash products scale by the positive factor `∏ i, α i`
  have hL : ∏ i, (α i * u i + β i - (α i * B.d i + β i)) =
      (∏ i, α i) * ∏ i, (u i - B.d i) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _ => by ring)
  have hR : ∏ i, (v i - (α i * B.d i + β i)) =
      (∏ i, α i) * ∏ i, ((v i - β i) / α i - B.d i) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [mul_sub, mul_div_cancel₀ _ (hα i).ne']
    ring
  rw [hL, hR]
  exact mul_le_mul_of_nonneg_left hmax (Finset.prod_nonneg (fun i _ => (hα i).le))

/-! ### Egalitarian bargaining solution

The egalitarian solution (Kalai 1977) selects the feasible
individually-rational profile on which all players gain *equally* over the
disagreement point, taking the *largest* common gain that remains feasible.
This is a non-utility-comparable alternative to Nash bargaining; the chief
difference is that the egalitarian solution is **not** scale invariant — it
depends on the cardinal utility scale. -/

/-- An outcome is the *egalitarian* (Kalai) solution of `B` if it is feasible,
individually rational, gives all players equal gain over the disagreement point,
and dominates (coordinatewise) every feasible equal-gain profile — equivalently,
it has the *largest* common gain. -/
def IsEgalitarian (u : ι → ℝ) : Prop :=
  B.feasible u ∧ B.IsIR u ∧ (∀ i j, u i - B.d i = u j - B.d j) ∧
    ∀ v, B.feasible v → (∀ i j, v i - B.d i = v j - B.d j) → ∀ i, v i ≤ u i

/-- The egalitarian solution is individually rational by definition. -/
theorem egalitarian_IR (u : ι → ℝ) (h : B.IsEgalitarian u) : B.IsIR u :=
  h.2.1

/-- The egalitarian solution gives equal gain to all players. -/
theorem egalitarian_equal_gain (u : ι → ℝ) (h : B.IsEgalitarian u) :
    ∀ i j, u i - B.d i = u j - B.d j :=
  h.2.2.1

/-- The egalitarian solution dominates every feasible equal-gain outcome,
i.e. it has the largest common gain. -/
theorem egalitarian_maximal (u : ι → ℝ) (h : B.IsEgalitarian u)
    {v : ι → ℝ} (hfv : B.feasible v) (hv : ∀ i j, v i - B.d i = v j - B.d j) :
    ∀ i, v i ≤ u i :=
  h.2.2.2 v hfv hv

/-- In a symmetric problem the egalitarian solution dominates the (unique)
symmetric Nash solution coordinatewise: the latter also lies on the
equal-gains diagonal, where the egalitarian solution maximizes the common gain. -/
theorem nashSolution_le_egalitarian [Fintype ι]
    (u v : ι → ℝ) (hsym : B.IsSymmetric)
    (heg : B.IsEgalitarian u) (hns : B.IsNashSolution v)
    (huniq : ∀ x w, B.IsNashSolution x → B.IsNashSolution w → x = w) :
    ∀ i, v i ≤ u i :=
  heg.2.2.2 v hns.1 (B.nashSolution_symmetric v hsym hns huniq)

/-! ### Kalai–Smorodinsky bargaining solution

The Kalai–Smorodinsky solution (1975) replaces Nash's *independence of
irrelevant alternatives* with a *monotonicity* axiom. It selects the
Pareto-optimal outcome at which all players' gains are **proportional to
their maximal feasible gains** — the gains at the *ideal* (utopia) point
`a`, where `a i` is the most player `i` could obtain among
individually-rational feasible outcomes. Unlike the egalitarian solution it
**is** scale invariant; unlike the Nash solution it is monotone. -/

/-- `a` is an *ideal* (utopia) point of `B`: each coordinate is the least
upper bound of that player's payoff over individually-rational feasible
outcomes. The Kalai–Smorodinsky solution is defined relative to such a point. -/
def IsIdealPoint (a : ι → ℝ) : Prop :=
  ∀ i, IsLUB {x | ∃ u, B.feasible u ∧ B.IsIR u ∧ u i = x} (a i)

/-- The Kalai–Smorodinsky outcome *relative to* a point `a`: a Pareto-optimal,
individually-rational, feasible outcome whose gains over the disagreement point
are proportional to the `a`-gains, i.e. `(u i - d i) / (a i - d i)` is common to
all players, written in the division-free form
`(u i - d i)(a j - d j) = (u j - d j)(a i - d i)`. The properties below hold for
any `a`; the Kalai–Smorodinsky *solution* additionally fixes `a` to be the ideal
point. -/
def IsKalaiSmorodinskyRelativeTo (a u : ι → ℝ) : Prop :=
  B.feasible u ∧ B.IsIR u ∧ B.IsPareto u ∧
    ∀ i j, (u i - B.d i) * (a j - B.d j) = (u j - B.d j) * (a i - B.d i)

/-- The **Kalai–Smorodinsky solution**: the Kalai–Smorodinsky outcome relative to
the *ideal* (utopia) point `a`, so proportionality is measured against each
player's maximal feasible gain. -/
def IsKalaiSmorodinsky (a u : ι → ℝ) : Prop :=
  B.IsIdealPoint a ∧ B.IsKalaiSmorodinskyRelativeTo a u

/-- The Kalai–Smorodinsky outcome is individually rational by definition. -/
theorem kalaiSmorodinskyRelativeTo_IR (a u : ι → ℝ)
    (h : B.IsKalaiSmorodinskyRelativeTo a u) : B.IsIR u :=
  h.2.1

/-- The Kalai–Smorodinsky outcome is Pareto optimal by definition. -/
theorem kalaiSmorodinskyRelativeTo_pareto (a u : ι → ℝ)
    (h : B.IsKalaiSmorodinskyRelativeTo a u) : B.IsPareto u :=
  h.2.2.1

/-- The Kalai–Smorodinsky outcome equalizes the ratio of each player's gain
to their `a`-gain. -/
theorem kalaiSmorodinskyRelativeTo_proportional (a u : ι → ℝ)
    (h : B.IsKalaiSmorodinskyRelativeTo a u) :
    ∀ i j, (u i - B.d i) * (a j - B.d j) = (u j - B.d j) * (a i - B.d i) :=
  h.2.2.2

/-- With a symmetric reference point (`a` constant), the Kalai–Smorodinsky outcome
gives equal gains to all players, provided the problem is nondegenerate
(`a i ≠ d i`). -/
theorem kalaiSmorodinskyRelativeTo_symmetric (a u : ι → ℝ)
    (hsym : B.IsSymmetric) (ha : ∀ i j, a i = a j) (hnd : ∀ i, a i - B.d i ≠ 0)
    (h : B.IsKalaiSmorodinskyRelativeTo a u) :
    ∀ i j, u i - B.d i = u j - B.d j := by
  intro i j
  have hprop := h.2.2.2 i j
  have haj : a j - B.d j = a i - B.d i := by rw [ha j i, hsym.1 j i]
  rw [haj] at hprop
  exact mul_right_cancel₀ (hnd i) hprop

/-- **Scale invariance.** The Kalai–Smorodinsky outcome is preserved under
independent positive-affine rescaling of the players' utilities, with the
reference point rescaled along with the problem. This is the axiom distinguishing
KS from the (scale-dependent) egalitarian solution. -/
theorem kalaiSmorodinskyRelativeTo_affine_invariant
    (α : ι → ℝ) (hα : ∀ i, 0 < α i) (β : ι → ℝ)
    (a u : ι → ℝ) (h : B.IsKalaiSmorodinskyRelativeTo a u) :
    (B.posAffineMap α hα β).IsKalaiSmorodinskyRelativeTo
      (fun i => α i * a i + β i) (fun i => α i * u i + β i) := by
  obtain ⟨hfu, hiru, hpu, hprop⟩ := h
  refine ⟨(B.posAffineMap_feasible_image hα u).mpr hfu,
    (B.posAffineMap_isIR_image hα u).mpr hiru,
    ⟨(B.posAffineMap_feasible_image hα u).mpr hfu, ?_⟩, ?_⟩
  · -- strong Pareto: a weakly-dominating image gives a weakly-dominating preimage
    rintro ⟨w, hfw, hwge, ⟨i₀, hwlt⟩⟩
    simp only [posAffineMap] at hfw
    apply hpu.2
    refine ⟨fun i => (w i - β i) / α i, hfw, ?_, ⟨i₀, ?_⟩⟩
    · intro i
      rw [ge_iff_le, le_div_iff₀ (hα i)]
      nlinarith [hwge i]
    · rw [gt_iff_lt, lt_div_iff₀ (hα i₀)]
      nlinarith [hwlt]
  · -- proportionality is preserved: both sides scale by `α i * α j`
    intro i j
    simp only [posAffineMap]
    linear_combination (α i * α j) * hprop i j

/-- The Kalai–Smorodinsky solution is dominated by the ideal point: no player
can exceed its maximal feasible (utopia) payoff. Together with individual
rationality this places each player's gain in `[0, ideal gain]`. -/
theorem kalaiSmorodinsky_le_ideal (a u : ι → ℝ) (h : B.IsKalaiSmorodinsky a u) :
    ∀ i, u i ≤ a i := by
  obtain ⟨hideal, hfeas, hIR, _, _⟩ := h
  intro i
  exact (hideal i).1 ⟨u, hfeas, hIR, rfl⟩

end BargainingProblem

end GameTheory
