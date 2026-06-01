/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Sum
import Math.Probability
import GameTheory.Cooperative.CoalitionalGame.Banzhaf

open scoped BigOperators

namespace GameTheory

open Math.Probability

namespace CoalGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ### Convex (supermodular) coalitional games

A coalitional game is **convex** (Shapley 1971) if
`v(S ∪ T) + v(S ∩ T) ≥ v(S) + v(T)` for every pair of coalitions. The
equivalent characterization is that marginal contributions are *monotone*:
joining a larger coalition is at least as valuable. Convex games have
nonempty cores (and the Shapley value is in the core); we develop the
monotone-marginals characterization here. -/

-- The convexity / monotone-marginals theory is about finite coalitions only;
-- it needs no enumeration of the player universe, so `Fintype ι` is dropped here.
omit [Fintype ι]

/-- A coalitional game is *convex* (supermodular) when value enjoys the
inclusion-exclusion inequality. -/
def IsConvex (G : CoalGame ι) : Prop :=
  ∀ S T : Finset ι, G.v (S ∪ T) + G.v (S ∩ T) ≥ G.v S + G.v T

/-- A game has *monotone marginals* if joining a larger coalition yields a
weakly larger marginal contribution: `S ⊆ T, i ∉ T ⇒ MC(i, S) ≤ MC(i, T)`. -/
def HasMonotoneMarginals (G : CoalGame ι) : Prop :=
  ∀ {i : ι} {S T : Finset ι}, S ⊆ T → i ∉ T →
    G.marginalContribution i S ≤ G.marginalContribution i T

/-- **Convexity → monotone marginals**: in a convex game, the marginal
contribution of a player to a coalition is weakly increasing as the
coalition grows. -/
theorem IsConvex.hasMonotoneMarginals (G : CoalGame ι) (h : G.IsConvex) :
    G.HasMonotoneMarginals := by
  intro i S T hST hiT
  simp only [marginalContribution]
  -- Apply convexity to the pair A = insert i S, B = T.
  -- Then A ∪ B = insert i T and A ∩ B = S (since S ⊆ T and i ∉ T).
  have hiS : i ∉ S := fun hi => hiT (hST hi)
  have hunion : (insert i S) ∪ T = insert i T := by
    ext x
    simp only [Finset.mem_union, Finset.mem_insert]
    refine ⟨fun h => h.elim (fun h => h.elim Or.inl (fun a => Or.inr (hST a))) Or.inr,
      fun h => h.elim (fun h => Or.inl (Or.inl h)) Or.inr⟩
  have hinter : (insert i S) ∩ T = S := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_insert]
    refine ⟨fun ⟨hx, hxT⟩ => hx.elim (fun hxi => absurd (hxi ▸ hxT) hiT) id,
      fun hxS => ⟨Or.inr hxS, hST hxS⟩⟩
  have hconvex := h (insert i S) T
  rw [hunion, hinter] at hconvex
  linarith

/-- Helper: in a game with monotone marginals, augmenting any coalition `B`
with a disjoint set `A` is more valuable when starting from a larger
coalition. Telescoping along `A` gives the inequality used to deduce
convexity. -/
private theorem augment_monotone (G : CoalGame ι) (h : G.HasMonotoneMarginals)
    (T₁ T₂ : Finset ι) (hT : T₁ ⊆ T₂) (A : Finset ι) (hdisj : Disjoint A T₂) :
    G.v (T₂ ∪ A) - G.v T₂ ≥ G.v (T₁ ∪ A) - G.v T₁ := by
  induction A using Finset.induction with
  | empty => simp
  | insert a A' haA' ih =>
    have ha_not_T₂ : a ∉ T₂ := by
      have := Finset.disjoint_left.mp hdisj (Finset.mem_insert_self a A')
      exact this
    have ha_not_T₁ : a ∉ T₁ := fun h' => ha_not_T₂ (hT h')
    have hdisj' : Disjoint A' T₂ :=
      Finset.disjoint_of_subset_left (Finset.subset_insert a A') hdisj
    have ha_not_T₂A' : a ∉ T₂ ∪ A' := by
      simp [ha_not_T₂, haA']
    have ha_not_T₁A' : a ∉ T₁ ∪ A' := by
      simp [ha_not_T₁, haA']
    have hT_ext : T₁ ∪ A' ⊆ T₂ ∪ A' := Finset.union_subset_union_left hT
    have hMC := h (i := a) hT_ext ha_not_T₂A'
    simp only [marginalContribution] at hMC
    have hU₂ : T₂ ∪ insert a A' = insert a (T₂ ∪ A') := by
      ext x; simp
    have hU₁ : T₁ ∪ insert a A' = insert a (T₁ ∪ A') := by
      ext x; simp
    rw [hU₂, hU₁]
    have ihA := ih hdisj'
    linarith

/-- **Monotone marginals → convexity**: the reverse implication, completing
the equivalence. The proof telescopes marginal contributions along the
elements of `S \ T`. -/
theorem HasMonotoneMarginals.isConvex (G : CoalGame ι) (h : G.HasMonotoneMarginals) :
    G.IsConvex := by
  intro S T
  -- Decompose S = (S ∩ T) ∪ (S \ T) and apply augment_monotone with A = S \ T.
  have hdecomp : (S ∩ T) ∪ (S \ T) = S := by
    ext x; simp [Finset.mem_inter, Finset.mem_sdiff]; tauto
  have hsuT : T ∪ (S \ T) = S ∪ T := by
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  have hsub : S ∩ T ⊆ T := Finset.inter_subset_right
  have hdisj : Disjoint (S \ T) T := Finset.sdiff_disjoint
  have key := G.augment_monotone h (S ∩ T) T hsub (S \ T) hdisj
  rw [hsuT, hdecomp] at key
  linarith

/-- **Convexity ↔ monotone marginals** (Shapley 1971). -/
theorem isConvex_iff_hasMonotoneMarginals (G : CoalGame ι) :
    G.IsConvex ↔ G.HasMonotoneMarginals :=
  ⟨IsConvex.hasMonotoneMarginals G, HasMonotoneMarginals.isConvex G⟩

/-- The sum of two convex games is convex. -/
theorem IsConvex.gameAdd {G₁ G₂ : CoalGame ι}
    (h₁ : G₁.IsConvex) (h₂ : G₂.IsConvex) :
    (gameAdd G₁ G₂).IsConvex := by
  intro S T
  change G₁.v (S ∪ T) + G₂.v (S ∪ T) + (G₁.v (S ∩ T) + G₂.v (S ∩ T)) ≥
    G₁.v S + G₂.v S + (G₁.v T + G₂.v T)
  have := h₁ S T
  have := h₂ S T
  linarith

/-- A nonnegative scalar multiple of a convex game is convex. -/
theorem IsConvex.gameScalar {G : CoalGame ι} (h : G.IsConvex)
    {c : ℝ} (hc : 0 ≤ c) :
    (gameScalar c G).IsConvex := by
  intro S T
  change c * G.v (S ∪ T) + c * G.v (S ∩ T) ≥ c * G.v S + c * G.v T
  have h_ineq := h S T
  nlinarith

variable [Fintype ι]

/-- **Shapley value of a unanimity game**: the unit value is split equally
among the members of `S`, and non-members get zero. Immediate corollary
of `allocation_on_unanimityGame` applied to `shapleyValue` itself (which
satisfies the three required axioms via `shapleyValue_efficient/symmetric/null`). -/
theorem unanimityGame_shapleyValue (S : Finset ι) (hS : S.Nonempty) (i : ι) :
    (unanimityGame S hS).shapleyValue i = if i ∈ S then (1 : ℝ) / S.card else 0 :=
  allocation_on_unanimityGame shapleyValue
    shapleyValue_efficient shapleyValue_symmetric shapleyValue_null S hS i

/-- The Shapley value of a unanimity game is in its core. -/
theorem unanimityGame_shapleyValue_isCore (S : Finset ι) (hS : S.Nonempty) :
    (unanimityGame S hS).IsCore (fun i => (unanimityGame S hS).shapleyValue i) := by
  classical
  refine ⟨shapleyValue_efficient _, ?_⟩
  intro T
  by_cases hST : S ⊆ T
  · have hsum :
        (∑ i ∈ T, (unanimityGame S hS).shapleyValue i) = 1 := by
      have hfilter : T.filter (fun i => i ∈ S) = S := by
        ext i
        simp [hST]
      calc
        ∑ i ∈ T, (unanimityGame S hS).shapleyValue i
            = ∑ i ∈ T, if i ∈ S then (1 : ℝ) / S.card else 0 := by
              refine Finset.sum_congr rfl ?_
              intro i _
              rw [unanimityGame_shapleyValue]
        _ = ∑ i ∈ T.filter (fun i => i ∈ S), (1 : ℝ) / S.card := by
              rw [← Finset.sum_filter]
        _ = ∑ i ∈ S, (1 : ℝ) / S.card := by rw [hfilter]
        _ = 1 := by
              rw [Finset.sum_const, nsmul_eq_mul]
              have hcard_ne : (S.card : ℝ) ≠ 0 := by
                exact_mod_cast (Finset.card_ne_zero.mpr hS)
              field_simp [hcard_ne]
    rw [hsum]
    simp [unanimityGame, hST]
  · have hnonneg :
        0 ≤ ∑ i ∈ T, (unanimityGame S hS).shapleyValue i := by
      apply Finset.sum_nonneg
      intro i _
      rw [unanimityGame_shapleyValue]
      split_ifs
      · exact div_nonneg zero_le_one (by exact_mod_cast Nat.zero_le S.card)
      · exact le_refl 0
    simpa [unanimityGame, hST] using hnonneg

/-- A scalar multiple of a game whose Shapley value is in the core still has
its Shapley value in the core, provided the scalar is nonnegative. -/
theorem gameScalar_shapleyValue_isCore {G : CoalGame ι} {c : ℝ} (hc : 0 ≤ c)
    (hcore : G.IsCore (fun i => G.shapleyValue i)) :
    (gameScalar c G).IsCore (fun i => (gameScalar c G).shapleyValue i) := by
  convert hcore.gameScalar hc using 1
  ext i
  rw [shapleyValue_scalar]

/-- If every unanimity-basis coefficient is nonnegative, then each term in the
unanimity decomposition has its Shapley value in the core. -/
theorem decompTerm_shapleyValue_isCore_of_nonneg_unanimityCoeff
    (G : CoalGame ι) (hcoeff : ∀ S : Finset ι, 0 ≤ G.unanimityCoeff S)
    (S : Finset ι) :
    (G.decompTerm S).IsCore (fun i => (G.decompTerm S).shapleyValue i) := by
  classical
  simp only [decompTerm]
  by_cases hS : S.Nonempty
  · simp only [hS, dif_pos]
    exact gameScalar_shapleyValue_isCore (hcoeff S)
      (unanimityGame_shapleyValue_isCore S hS)
  · simp only [hS, dif_neg, not_false_iff]
    exact zeroGame_shapleyValue_isCore

/-- Games with nonnegative unanimity-basis coefficients have the Shapley value
in the core. This covers the positive cone generated by unanimity games. -/
theorem shapleyValue_isCore_of_nonneg_unanimityCoeff
    (G : CoalGame ι) (hcoeff : ∀ S : Finset ι, 0 ≤ G.unanimityCoeff S) :
    G.IsCore (fun i => G.shapleyValue i) := by
  classical
  let terms := (Finset.univ : Finset (Finset ι))
  let alloc : Finset ι → ι → ℝ := fun S i => (G.decompTerm S).shapleyValue i
  have hterm : ∀ S ∈ terms, (G.decompTerm S).IsCore (alloc S) := by
    intro S _
    exact G.decompTerm_shapleyValue_isCore_of_nonneg_unanimityCoeff hcoeff S
  have hsum_core :
      (gameSum terms G.decompTerm).IsCore (fun i => ∑ S ∈ terms, alloc S i) :=
    gameSum_isCore terms G.decompTerm alloc hterm
  have halloc_sum : ∀ i,
      (gameSum terms G.decompTerm).shapleyValue i = ∑ S ∈ terms, alloc S i := by
    intro i
    exact gameSum_allocation_eq shapleyValue
      (fun G₁ G₂ j => shapleyValue_additive G₁ G₂ j) terms G.decompTerm i
  rw [G.eq_gameSum_decompTerm]
  convert hsum_core using 1
  ext i
  exact halloc_sum i

omit [Fintype ι]

/-- **Unanimity games are convex**. The value function jumps from `0` to
`1` exactly when `S` becomes a subset, and `S ⊆ A ∩ B ↔ S ⊆ A ∧ S ⊆ B`,
which is exactly the supermodular inequality on `{0,1}`-valued games. -/
theorem unanimityGame_isConvex (S : Finset ι) (hS : S.Nonempty) :
    (unanimityGame S hS).IsConvex := by
  intro T₁ T₂
  simp only [unanimityGame]
  by_cases h1 : S ⊆ T₁
  · by_cases h2 : S ⊆ T₂
    · have hu : S ⊆ T₁ ∪ T₂ := h1.trans Finset.subset_union_left
      have hi : S ⊆ T₁ ∩ T₂ := Finset.subset_inter h1 h2
      simp [h1, h2, hu, hi]
    · have hu : S ⊆ T₁ ∪ T₂ := h1.trans Finset.subset_union_left
      have hni : ¬ S ⊆ T₁ ∩ T₂ := fun h => h2 (h.trans Finset.inter_subset_right)
      simp [h1, h2, hu, hni]
  · by_cases h2 : S ⊆ T₂
    · have hu : S ⊆ T₁ ∪ T₂ := h2.trans Finset.subset_union_right
      have hni : ¬ S ⊆ T₁ ∩ T₂ := fun h => h1 (h.trans Finset.inter_subset_left)
      simp [h1, h2, hu, hni]
    · have hni : ¬ S ⊆ T₁ ∩ T₂ := fun h => h1 (h.trans Finset.inter_subset_left)
      by_cases hu : S ⊆ T₁ ∪ T₂
      · simp [h1, h2, hu, hni]
      · simp [h1, h2, hu, hni]


end CoalGame

end GameTheory
