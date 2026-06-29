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

-- `Fintype ι` is introduced only later (before the Shapley-value results that
-- enumerate the player universe); the convexity / monotone-marginals theory
-- needs only finite coalitions, so it is developed without it.
variable {ι : Type} [DecidableEq ι]

/-! ### Convex (supermodular) coalitional games

A coalitional game is **convex** (Shapley 1971) if
`v(S ∪ T) + v(S ∩ T) ≥ v(S) + v(T)` for every pair of coalitions. The
equivalent characterization is that marginal contributions are *monotone*:
joining a larger coalition is at least as valuable. Convex games have
nonempty cores (and the Shapley value is in the core); we develop the
monotone-marginals characterization here. -/

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

omit [Fintype ι] in
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


/-! ### Marginal vectors and the Shapley value of a convex game

For an *arrival order* `e : Fin n ≃ ι` (player `e k` arrives at step `k`),
the **marginal vector** assigns each player the marginal contribution they
make on joining the coalition of their predecessors. The Shapley value is the
average of these marginal vectors over all `n!` arrival orders. For a convex
game every marginal vector lies in the core, and the core is convex, so the
Shapley value lies in the core. -/

section MarginalVector

/-- Players arriving strictly before `i` under the arrival order `e`. -/
def predOrder (e : Fin (Fintype.card ι) ≃ ι) (i : ι) : Finset ι :=
  Finset.univ.filter (fun x => e.symm x < e.symm i)

/-- The marginal vector of the arrival order `e`: player `i` receives the
marginal contribution made on joining the coalition of their predecessors. -/
def margVec (G : CoalGame ι) (e : Fin (Fintype.card ι) ≃ ι) (i : ι) : ℝ :=
  G.marginalContribution i (predOrder e i)

omit [DecidableEq ι] in
/-- A player is never among their own predecessors. -/
theorem notMem_predOrder (e : Fin (Fintype.card ι) ≃ ι) (i : ι) :
    i ∉ predOrder e i := by
  simp [predOrder]

/-- **Telescoping identity.** Summing, over the players of a coalition `W`,
the marginal contribution each makes on joining their `W`-predecessors
(in the arrival order `e`) recovers `v W`. The proof removes the
`e`-last player of `W` and inducts. -/
theorem telescope (G : CoalGame ι) (e : Fin (Fintype.card ι) ≃ ι)
    (W : Finset ι) :
    ∑ i ∈ W, G.marginalContribution i (W.filter (fun x => e.symm x < e.symm i))
      = G.v W := by
  induction W using Finset.strongInductionOn with
  | _ W ih =>
    rcases W.eq_empty_or_nonempty with rfl | hW
    · simp [G.v_empty]
    · -- Extract the `e`-maximal player `m` of `W`.
      have hne : (W.image e.symm).Nonempty := hW.image _
      set M := (W.image e.symm).max' hne with hM_def
      have hM_mem : M ∈ W.image e.symm := (W.image e.symm).max'_mem hne
      obtain ⟨m, hmW, hmM⟩ := Finset.mem_image.mp hM_mem
      have hmax : ∀ x ∈ W, x ≠ m → e.symm x < e.symm m := by
        intro x hxW hxm
        have hle : e.symm x ≤ M :=
          Finset.le_max' _ _ (Finset.mem_image.mpr ⟨x, hxW, rfl⟩)
        rw [← hmM] at hle
        refine lt_of_le_of_ne hle ?_
        intro hcontra
        exact hxm (e.symm.injective hcontra)
      -- Fact 1: predecessors of `m` in `W` are everyone else.
      have hpredm : W.filter (fun x => e.symm x < e.symm m) = W.erase m := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_erase]
        constructor
        · rintro ⟨hxW, hlt⟩
          exact ⟨fun h => by rw [h] at hlt; exact absurd hlt (lt_irrefl _), hxW⟩
        · rintro ⟨hxm, hxW⟩
          exact ⟨hxW, hmax x hxW hxm⟩
      -- Fact 2: for `i ∈ W.erase m`, predecessors in `W` and in `W.erase m` agree.
      have hpred_erase : ∀ i ∈ W.erase m,
          W.filter (fun x => e.symm x < e.symm i)
            = (W.erase m).filter (fun x => e.symm x < e.symm i) := by
        intro i hi
        obtain ⟨him, hiW⟩ := Finset.mem_erase.mp hi
        have hilt : e.symm i < e.symm m := hmax i hiW him
        ext x
        simp only [Finset.mem_filter, Finset.mem_erase]
        constructor
        · rintro ⟨hxW, hlt⟩
          exact ⟨⟨fun h => by rw [h] at hlt; exact absurd (hlt.trans hilt) (lt_irrefl _),
            hxW⟩, hlt⟩
        · rintro ⟨⟨_, hxW⟩, hlt⟩
          exact ⟨hxW, hlt⟩
      -- Split the sum at `m` and apply the induction hypothesis to `W.erase m`.
      rw [← Finset.add_sum_erase W _ hmW]
      have hterm_m :
          G.marginalContribution m (W.filter (fun x => e.symm x < e.symm m))
            = G.v W - G.v (W.erase m) := by
        rw [hpredm, marginalContribution, Finset.insert_erase hmW]
      rw [hterm_m]
      rw [Finset.sum_congr rfl (fun i hi => by rw [hpred_erase i hi])]
      rw [ih (W.erase m) (Finset.erase_ssubset hmW)]
      ring

/-- **Efficiency of a marginal vector**: the components of the marginal
vector of any arrival order sum to `v(N)`. This is the telescoping identity
applied to the grand coalition. -/
theorem margVec_sum (G : CoalGame ι) (e : Fin (Fintype.card ι) ≃ ι) :
    ∑ i, G.margVec e i = G.v Finset.univ := by
  have h := G.telescope e Finset.univ
  simpa only [margVec, predOrder] using h

/-- There is at least one arrival order, so the number of arrival orders is
positive. -/
theorem card_orderings_pos :
    0 < Fintype.card (Fin (Fintype.card ι) ≃ ι) := by
  have hne : Nonempty (Fin (Fintype.card ι) ≃ ι) :=
    Fintype.card_eq.mp (by simp)
  exact Fintype.card_pos_iff.mpr hne

/-- **The Shapley value as an average of marginal vectors.** `orderingAvg`
averages the marginal vector over all `n!` arrival orders; it will be shown
to coincide with `shapleyValue`. -/
noncomputable def orderingAvg (G : CoalGame ι) (i : ι) : ℝ :=
  (∑ e : Fin (Fintype.card ι) ≃ ι, G.margVec e i)
    / (Fintype.card (Fin (Fintype.card ι) ≃ ι) : ℝ)

/-- The average-of-marginal-vectors allocation is efficient. -/
theorem orderingAvg_efficient (G : CoalGame ι) :
    ∑ i, G.orderingAvg i = G.v Finset.univ := by
  have hC : (Fintype.card (Fin (Fintype.card ι) ≃ ι) : ℝ) ≠ 0 := by
    exact_mod_cast card_orderings_pos.ne'
  simp only [orderingAvg]
  rw [← Finset.sum_div, Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun e _ => G.margVec_sum e)]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm, mul_div_assoc,
    div_self hC, mul_one]

/-- The average-of-marginal-vectors allocation gives null players `0`. -/
theorem orderingAvg_null (G : CoalGame ι) {i : ι} (h : G.IsNull i) :
    G.orderingAvg i = 0 := by
  simp only [orderingAvg]
  rw [show (∑ e : Fin (Fintype.card ι) ≃ ι, G.margVec e i) = 0 from ?_, zero_div]
  apply Finset.sum_eq_zero
  intro e _
  simp only [margVec]
  exact h (predOrder e i) (notMem_predOrder e i)

/-- The average-of-marginal-vectors allocation is additive across games. -/
theorem orderingAvg_additive (G₁ G₂ : CoalGame ι) (i : ι) :
    (gameAdd G₁ G₂).orderingAvg i = G₁.orderingAvg i + G₂.orderingAvg i := by
  simp only [orderingAvg]
  rw [← add_div]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  simp only [margVec, marginalContribution, gameAdd]
  ring

omit [Fintype ι] in
/-- **Swap-invariance of value under symmetry.** If players `i` and `j` are
symmetric, then transposing them leaves the value of every coalition
unchanged. (The pairwise-symmetry axiom upgrades to full invariance under
the transposition `swap i j`.) -/
theorem v_image_swap (G : CoalGame ι) {i j : ι} (hsym : G.AreSymmetric i j)
    (T : Finset ι) : G.v (T.image (Equiv.swap i j)) = G.v T := by
  classical
  -- A coalition avoiding both `i` and `j` is fixed pointwise by the swap.
  have himg_fix : ∀ U : Finset ι, i ∉ U → j ∉ U →
      U.image (Equiv.swap i j) = U := by
    intro U hiU hjU
    ext y
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rwa [Equiv.swap_apply_of_ne_of_ne (ne_of_mem_of_not_mem hx hiU)
        (ne_of_mem_of_not_mem hx hjU)]
    · intro hy
      exact ⟨y, hy, Equiv.swap_apply_of_ne_of_ne (ne_of_mem_of_not_mem hy hiU)
        (ne_of_mem_of_not_mem hy hjU)⟩
  by_cases hi : i ∈ T <;> by_cases hj : j ∈ T
  · -- both present: the swap permutes `T` onto itself.
    have hsub : T.image (Equiv.swap i j) ⊆ T := by
      rw [Finset.image_subset_iff]
      intro x hx
      rcases eq_or_ne x i with rfl | hxi
      · rw [Equiv.swap_apply_left]; exact hj
      rcases eq_or_ne x j with rfl | hxj
      · rw [Equiv.swap_apply_right]; exact hi
      · rw [Equiv.swap_apply_of_ne_of_ne hxi hxj]; exact hx
    have hcard : T.card ≤ (T.image (Equiv.swap i j)).card :=
      (Finset.card_image_of_injective T (Equiv.injective _)).ge
    rw [Finset.eq_of_subset_of_card_le hsub hcard]
  · -- `i ∈ T`, `j ∉ T`: the swap sends `i ↦ j`.
    have hiU : i ∉ T.erase i := Finset.notMem_erase i T
    have hjU : j ∉ T.erase i := fun h => hj (Finset.mem_of_mem_erase h)
    have himg : T.image (Equiv.swap i j) = insert j (T.erase i) := by
      conv_lhs => rw [← Finset.insert_erase hi]
      rw [Finset.image_insert, Equiv.swap_apply_left, himg_fix (T.erase i) hiU hjU]
    rw [himg, ← hsym (T.erase i) hiU hjU, Finset.insert_erase hi]
  · -- `i ∉ T`, `j ∈ T`: the swap sends `j ↦ i`.
    have hiU : i ∉ T.erase j := fun h => hi (Finset.mem_of_mem_erase h)
    have hjU : j ∉ T.erase j := Finset.notMem_erase j T
    have himg : T.image (Equiv.swap i j) = insert i (T.erase j) := by
      conv_lhs => rw [← Finset.insert_erase hj]
      rw [Finset.image_insert, Equiv.swap_apply_right, himg_fix (T.erase j) hiU hjU]
    rw [himg, hsym (T.erase j) hiU hjU, Finset.insert_erase hj]
  · -- neither present: the swap fixes `T`.
    rw [himg_fix T hi hj]

/-- **Relabelling marginal vectors under a symmetry.** When `i` and `j` are
symmetric, post-composing the arrival order with the transposition `swap i j`
turns `j`'s marginal-vector component into `i`'s. -/
theorem margVec_trans_swap (G : CoalGame ι) {i j : ι} (hsym : G.AreSymmetric i j)
    (e : Fin (Fintype.card ι) ≃ ι) :
    G.margVec (e.trans (Equiv.swap i j)) j = G.margVec e i := by
  have htrans_symm : ∀ x, (e.trans (Equiv.swap i j)).symm x
      = e.symm (Equiv.swap i j x) := by
    intro x
    simp only [Equiv.symm_trans_apply, Equiv.symm_swap]
  have hτj : (Equiv.swap i j) j = i := Equiv.swap_apply_right i j
  have hP : predOrder (e.trans (Equiv.swap i j)) j
      = (predOrder e i).image (Equiv.swap i j) := by
    ext x
    simp only [predOrder, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image, htrans_symm, hτj]
    constructor
    · intro hx
      exact ⟨Equiv.swap i j x, hx, Equiv.swap_apply_self i j x⟩
    · rintro ⟨y, hy, rfl⟩
      rwa [Equiv.swap_apply_self]
  rw [margVec, margVec, marginalContribution, marginalContribution, hP,
    G.v_image_swap hsym (predOrder e i),
    show insert j ((predOrder e i).image (Equiv.swap i j))
        = (insert i (predOrder e i)).image (Equiv.swap i j) from by
      rw [Finset.image_insert, Equiv.swap_apply_left],
    G.v_image_swap hsym (insert i (predOrder e i))]

/-- The average-of-marginal-vectors allocation treats symmetric players
identically. -/
theorem orderingAvg_symmetric (G : CoalGame ι) {i j : ι} (_hne : i ≠ j)
    (hsym : G.AreSymmetric i j) : G.orderingAvg i = G.orderingAvg j := by
  simp only [orderingAvg]
  congr 1
  have hττ : (Equiv.swap i j).trans (Equiv.swap i j) = Equiv.refl ι :=
    Equiv.ext (fun x => Equiv.swap_apply_self i j x)
  let Φ : (Fin (Fintype.card ι) ≃ ι) ≃ (Fin (Fintype.card ι) ≃ ι) :=
    { toFun := fun e => e.trans (Equiv.swap i j)
      invFun := fun e => e.trans (Equiv.swap i j)
      left_inv := fun e => by
        change (e.trans (Equiv.swap i j)).trans (Equiv.swap i j) = e
        rw [Equiv.trans_assoc, hττ, Equiv.trans_refl]
      right_inv := fun e => by
        change (e.trans (Equiv.swap i j)).trans (Equiv.swap i j) = e
        rw [Equiv.trans_assoc, hττ, Equiv.trans_refl] }
  rw [← Equiv.sum_comp Φ (fun e => G.margVec e j)]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  exact (margVec_trans_swap G hsym e).symm

/-- **The Shapley value is the average of marginal vectors.** Both satisfy
efficiency, symmetry, the null-player axiom, and additivity, so they coincide by
Shapley's uniqueness theorem. -/
theorem orderingAvg_eq_shapleyValue (G : CoalGame ι) (i : ι) :
    G.orderingAvg i = G.shapleyValue i :=
  shapleyValue_unique orderingAvg orderingAvg_efficient orderingAvg_symmetric
    orderingAvg_null orderingAvg_additive G i

/-- **Key lemma: marginal vectors of a convex game are coalition-rational.**
For a convex game, the marginal vector of any arrival order gives every
coalition at least its own value. The telescoping identity expresses `v S`
as a sum of marginal contributions to `S`-predecessor coalitions, each of
which is dominated by the corresponding full-predecessor marginal
contribution by monotonicity of marginals. -/
theorem margVec_coalition_ge (G : CoalGame ι) (h : G.IsConvex)
    (e : Fin (Fintype.card ι) ≃ ι) (S : Finset ι) :
    ∑ i ∈ S, G.margVec e i ≥ G.v S := by
  rw [ge_iff_le, ← G.telescope e S]
  apply Finset.sum_le_sum
  intro i _
  simp only [margVec, predOrder]
  apply IsConvex.hasMonotoneMarginals G h
  · exact Finset.filter_subset_filter _ (Finset.subset_univ S)
  · simp

/-- **Shapley (1971): the Shapley value of a convex game is in the core.**
Each marginal vector lies in the core (efficiency by telescoping, coalition
rationality by `margVec_coalition_ge`), the Shapley value is their average,
and the core is convex. -/
theorem shapleyValue_isCore_of_isConvex (G : CoalGame ι) (h : G.IsConvex) :
    G.IsCore (fun i => G.shapleyValue i) := by
  refine ⟨shapleyValue_efficient G, ?_⟩
  intro S
  have hCpos : (0 : ℝ) < (Fintype.card (Fin (Fintype.card ι) ≃ ι) : ℝ) := by
    exact_mod_cast card_orderings_pos
  have hrw : ∑ i ∈ S, G.shapleyValue i = ∑ i ∈ S, G.orderingAvg i :=
    Finset.sum_congr rfl (fun i _ => (orderingAvg_eq_shapleyValue G i).symm)
  rw [ge_iff_le, hrw]
  simp only [orderingAvg]
  rw [← Finset.sum_div, Finset.sum_comm, le_div_iff₀ hCpos]
  calc G.v S * (Fintype.card (Fin (Fintype.card ι) ≃ ι) : ℝ)
      = ∑ _e : Fin (Fintype.card ι) ≃ ι, G.v S := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ e : Fin (Fintype.card ι) ≃ ι, ∑ i ∈ S, G.margVec e i :=
        Finset.sum_le_sum (fun e _ => margVec_coalition_ge G h e S)

end MarginalVector

end CoalGame

end GameTheory
