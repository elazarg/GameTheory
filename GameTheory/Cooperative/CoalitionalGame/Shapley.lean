/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Sum
import Math.Probability
import GameTheory.Cooperative.CoalitionalGame.Core

open scoped BigOperators

namespace GameTheory

open Math.Probability

namespace CoalGame

variable {ι : Type} [DecidableEq ι]

/-! ### Unanimity games and Shapley uniqueness

The unanimity game on a nonempty coalition `S` pays `1` whenever the
present coalition contains all of `S`, and `0` otherwise. These games
are the building blocks: every coalitional game decomposes uniquely as
a linear combination of unanimity games (Shapley 1953). -/

/-- Unanimity game on coalition `S`: `v T = 1` if `S ⊆ T`, else `0`. -/
def unanimityGame (S : Finset ι) (hS : S.Nonempty) : CoalGame ι where
  v := fun T => if S ⊆ T then 1 else 0
  v_empty := by
    rw [if_neg]
    intro hsub
    obtain ⟨i, hi⟩ := hS
    exact Finset.notMem_empty i (hsub hi)

/-- A player outside `S` is null in the unanimity game on `S`:
adding them never crosses the `S ⊆ ·` threshold. -/
theorem unanimityGame_isNull_of_notMem (S : Finset ι) (hS : S.Nonempty)
    {i : ι} (hi : i ∉ S) :
    (unanimityGame S hS).IsNull i := by
  intro T _
  simp only [marginalContribution, unanimityGame]
  have hequiv : S ⊆ insert i T ↔ S ⊆ T := by
    refine ⟨fun h x hx => ?_, fun h => h.trans (Finset.subset_insert i T)⟩
    rcases Finset.mem_insert.mp (h hx) with rfl | hxT
    · exact absurd hx hi
    · exact hxT
  by_cases hST : S ⊆ T
  · simp [hST, hequiv.mpr hST]
  · have hnST' : ¬ S ⊆ insert i T := fun h => hST (hequiv.mp h)
    simp [hST, hnST']

/-- Two distinct members of `S` are symmetric in the unanimity game on `S`:
neither `insert i T` nor `insert j T` can contain `S` when the other
required member sits outside `T`, so both marginal coalitions miss `S`. -/
theorem unanimityGame_areSymmetric (S : Finset ι) (hS : S.Nonempty)
    {i j : ι} (hne : i ≠ j) (hi : i ∈ S) (hj : j ∈ S) :
    (unanimityGame S hS).AreSymmetric i j := by
  intro T hiT hjT
  simp only [unanimityGame]
  have hni : ¬ S ⊆ insert i T := fun h => hjT <| by
    rcases Finset.mem_insert.mp (h hj) with hji | hjT'
    · exact absurd hji.symm hne
    · exact hjT'
  have hnj : ¬ S ⊆ insert j T := fun h => hiT <| by
    rcases Finset.mem_insert.mp (h hi) with hij | hiT'
    · exact absurd hij hne
    · exact hiT'
  simp [hni, hnj]

section FinitePlayers

variable [Fintype ι]

/-- The grand coalition contains every nonempty `S`, so the unanimity
game on `S` has value `1` on `univ`. -/
theorem unanimityGame_v_univ (S : Finset ι) (hS : S.Nonempty) :
    (unanimityGame S hS).v Finset.univ = 1 := by
  have : S ⊆ Finset.univ := S.subset_univ
  simp [unanimityGame, this]

end FinitePlayers

/-- Möbius coefficient of `S` in the unanimity-basis decomposition of `G`:
`c_S = Σ_{R ⊆ S} (-1)^{|S| - |R|} · G.v R`. Together with the unanimity
games these recover `G` (see `unanimity_decomposition`). -/
def unanimityCoeff (G : CoalGame ι) (S : Finset ι) : ℝ :=
  ∑ R ∈ S.powerset, (-1 : ℝ) ^ (S.card - R.card) * G.v R

/-- **Unanimity basis decomposition** (Möbius inversion on subsets): for any
coalition `T`,
`G.v T = Σ_{S ⊆ T} unanimityCoeff G S`.
Combined with linearity of `φ`, this reduces uniqueness of `φ` on `G`
to its values on the unanimity games. -/
theorem unanimity_decomposition (G : CoalGame ι) (T : Finset ι) :
    G.v T = ∑ S ∈ T.powerset, G.unanimityCoeff S := by
  classical
  simp only [unanimityCoeff]
  -- Swap the double sum: outer becomes R ∈ T.powerset.
  rw [show
    (∑ S ∈ T.powerset, ∑ R ∈ S.powerset, (-1 : ℝ) ^ (S.card - R.card) * G.v R)
      = ∑ R ∈ T.powerset, ∑ S ∈ T.powerset.filter (R ⊆ ·),
          (-1 : ℝ) ^ (S.card - R.card) * G.v R from ?swap]
  rotate_left
  · apply Finset.sum_comm'
    intro S R
    simp only [Finset.mem_powerset, Finset.mem_filter]
    refine ⟨fun ⟨hST, hRS⟩ => ⟨⟨hST, hRS⟩, hRS.trans hST⟩, fun ⟨⟨hST, hRS⟩, _⟩ => ⟨hST, hRS⟩⟩
  -- For each R, factor out G.v R and reindex S = R ∪ X with X ⊆ T \ R.
  have hinner : ∀ R ∈ T.powerset,
      (∑ S ∈ T.powerset.filter (R ⊆ ·),
        (-1 : ℝ) ^ (S.card - R.card) * G.v R) =
      G.v R * (if R = T then 1 else 0) := by
    intro R hR
    rw [Finset.mem_powerset] at hR
    rw [show (∑ S ∈ T.powerset.filter (R ⊆ ·),
        (-1 : ℝ) ^ (S.card - R.card) * G.v R) =
        G.v R * ∑ S ∈ T.powerset.filter (R ⊆ ·),
          (-1 : ℝ) ^ (S.card - R.card) by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun S _ => ?_); ring]
    -- Reindex via X = S \ R; inverse via X ↦ R ∪ X. Convert filtered powerset
    -- on T to the powerset of T \ R, then evaluate via the alternating-sum identity.
    have hreindex :
        T.powerset.filter (R ⊆ ·) = (T \ R).powerset.image (fun X => R ∪ X) := by
      ext S
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
      refine ⟨fun ⟨hST, hRS⟩ => ⟨S \ R,
          Finset.subset_sdiff.mpr ⟨Finset.sdiff_subset.trans hST, Finset.sdiff_disjoint⟩,
          Finset.union_sdiff_of_subset hRS⟩, ?_⟩
      rintro ⟨X, hX, rfl⟩
      exact ⟨Finset.union_subset hR ((Finset.subset_sdiff.mp hX).1),
        Finset.subset_union_left⟩
    rw [hreindex]
    -- `X ⊆ T \ R` directly implies `Disjoint R X`.
    have hdisj : ∀ {X : Finset ι}, X ⊆ T \ R → Disjoint R X := fun hX =>
      ((Finset.subset_sdiff.mp hX).2).symm
    have hinj : Set.InjOn (fun X => R ∪ X) ((T \ R).powerset : Set (Finset ι)) := by
      intro X hX Y hY hXY
      simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff,
        Finset.coe_subset] at hX hY
      have := congrArg (· \ R) hXY
      simp only [Finset.union_sdiff_left,
        Finset.sdiff_eq_self_of_disjoint (hdisj hX).symm,
        Finset.sdiff_eq_self_of_disjoint (hdisj hY).symm] at this
      exact this
    rw [Finset.sum_image (fun X hX Y hY => hinj hX hY)]
    -- The exponent simplifies because R and X are disjoint.
    have hcard_eq : ∀ X ∈ (T \ R).powerset,
        (R ∪ X).card - R.card = X.card := by
      intro X hX
      rw [Finset.card_union_of_disjoint (hdisj (Finset.mem_powerset.mp hX)),
        Nat.add_sub_cancel_left]
    rw [Finset.sum_congr rfl (fun X hX => by rw [hcard_eq X hX])]
    -- Apply the alternating-sum identity (cast from the ℤ-valued lemma).
    have h_alt_int : (∑ X ∈ (T \ R).powerset, ((-1 : ℤ) ^ X.card)) =
        if T \ R = ∅ then 1 else 0 :=
      Finset.sum_powerset_neg_one_pow_card
    have h_alt_real : (∑ X ∈ (T \ R).powerset, ((-1 : ℝ) ^ X.card)) =
        if T \ R = ∅ then (1 : ℝ) else 0 := by
      have hcast : (∑ X ∈ (T \ R).powerset, ((-1 : ℝ) ^ X.card)) =
          (((∑ X ∈ (T \ R).powerset, ((-1 : ℤ) ^ X.card)) : ℤ) : ℝ) := by
        push_cast; rfl
      rw [hcast, h_alt_int]
      split_ifs <;> simp
    rw [h_alt_real]
    -- T \ R = ∅ ↔ R = T (since R ⊆ T).
    have hempty_iff : T \ R = ∅ ↔ R = T := by
      constructor
      · intro h
        exact Finset.Subset.antisymm hR (Finset.sdiff_eq_empty_iff_subset.mp h)
      · rintro rfl; exact Finset.sdiff_self _
    by_cases hRT : R = T
    · rw [if_pos hRT, if_pos (hempty_iff.mpr hRT)]
    · rw [if_neg hRT, if_neg (fun h => hRT (hempty_iff.mp h))]
  rw [Finset.sum_congr rfl hinner]
  -- Only R = T contributes; collapse via `Finset.sum_ite_eq'`.
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' T.powerset T G.v,
    if_pos (Finset.mem_powerset.mpr Finset.Subset.rfl)]

section FinitePlayers

variable [Fintype ι]

/-- **Value on unanimity games**: any allocation `φ` satisfying *efficiency*,
*symmetry*, and the *null-player* axioms must split the unit of value of
`unanimityGame S` equally among the members of `S`, and pay zero to
non-members. This is the inductive base case for Shapley uniqueness:
combined with additivity and the unanimity-basis decomposition, it pins
down `φ` on every coalitional game. -/
theorem allocation_on_unanimityGame
    (φ : CoalGame ι → ι → ℝ)
    (h_eff : ∀ G : CoalGame ι, ∑ i, φ G i = G.v Finset.univ)
    (h_sym : ∀ (G : CoalGame ι) {i j : ι},
        i ≠ j → G.AreSymmetric i j → φ G i = φ G j)
    (h_null : ∀ (G : CoalGame ι) {i : ι}, G.IsNull i → φ G i = 0)
    (S : Finset ι) (hS : S.Nonempty) (i : ι) :
    φ (unanimityGame S hS) i = if i ∈ S then (1 : ℝ) / S.card else 0 := by
  classical
  set G := unanimityGame S hS
  by_cases hiS : i ∈ S
  · -- Non-members get zero by the null axiom.
    have hnull_outside : ∀ k ∉ S, φ G k = 0 := fun k hk =>
      h_null G (unanimityGame_isNull_of_notMem S hS hk)
    -- Members of S are pairwise symmetric, hence get the same value c.
    obtain ⟨c, hc⟩ : ∃ c : ℝ, ∀ k ∈ S, φ G k = c := by
      refine ⟨φ G i, fun k hk => ?_⟩
      by_cases hki : k = i
      · subst hki; rfl
      · exact h_sym G hki (unanimityGame_areSymmetric S hS hki hk hiS)
    -- Sum-splitting and efficiency: |S| · c = 1.
    have hsum_split : ∑ k, φ G k = ∑ k ∈ S, φ G k := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ S) (φ G)]
      have h_in : Finset.univ.filter (· ∈ S) = S := by
        ext k; simp
      have h_out :
          ∑ k ∈ Finset.univ.filter (¬ · ∈ S), φ G k = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        exact hnull_outside k hk
      rw [h_in, h_out, add_zero]
    have hsum_const : ∑ k ∈ S, φ G k = S.card * c := by
      rw [Finset.sum_congr rfl (fun k hk => hc k hk),
        Finset.sum_const, nsmul_eq_mul]
    have heff := h_eff G
    rw [hsum_split, hsum_const, unanimityGame_v_univ] at heff
    -- |S| ≠ 0 since S is nonempty.
    have hSpos : 0 < (S.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hS
    have hc_val : c = 1 / S.card := by
      field_simp at heff ⊢
      linarith
    rw [if_pos hiS, hc i hiS, hc_val]
  · -- i ∉ S: null axiom gives φ = 0.
    rw [if_neg hiS]
    exact h_null G (unanimityGame_isNull_of_notMem S hS hiS)

end FinitePlayers

/-- Indexed sum of coalitional games: `(gameSum s f).v T = Σ_{a ∈ s} (f a).v T`. -/
noncomputable def gameSum {α : Type*} (s : Finset α) (f : α → CoalGame ι) :
    CoalGame ι where
  v := fun T => ∑ a ∈ s, (f a).v T
  v_empty := by
    apply Finset.sum_eq_zero
    intro a _
    exact (f a).v_empty

@[simp]
lemma gameSum_v {α : Type*} (s : Finset α) (f : α → CoalGame ι) (T : Finset ι) :
    (gameSum s f).v T = ∑ a ∈ s, (f a).v T := rfl

/-- An allocation `φ` that is additive and zero on the empty-index gameSum
factors over arbitrary `gameSum`s. The zero hypothesis is derivable from
additivity alone (`φ(0 + 0) = 2·φ(0)`), but it is kept as an explicit
hypothesis so the lemma is usable when the underlying type lacks
`Nonempty`. -/
theorem gameSum_allocation_eq
    (φ : CoalGame ι → ι → ℝ)
    (h_add : ∀ (G₁ G₂ : CoalGame ι) (i : ι),
        φ (gameAdd G₁ G₂) i = φ G₁ i + φ G₂ i)
    {α : Type*} (s : Finset α) (f : α → CoalGame ι) (i : ι) :
    φ (gameSum s f) i = ∑ a ∈ s, φ (f a) i := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [Finset.sum_empty]
    -- φ on the zero game: from additivity, 0 + 0 = 0 so φ(0) = 2·φ(0), i.e. φ(0) = 0.
    have hself : gameAdd (gameSum (∅ : Finset α) f) (gameSum (∅ : Finset α) f) =
        gameSum (∅ : Finset α) f := by
      ext T
      simp [gameAdd]
    have := h_add (gameSum (∅ : Finset α) f) (gameSum (∅ : Finset α) f) i
    rw [hself] at this
    linarith
  | insert a s ha ih =>
    have hext : gameSum (insert a s) f =
        gameAdd (f a) (gameSum s f) := by
      ext T
      simp [gameAdd, Finset.sum_insert ha]
    rw [hext, h_add, ih, Finset.sum_insert ha]

section FinitePlayers

variable [Fintype ι]

/-- A finite sum of games has a core allocation obtained by summing core
allocations termwise. -/
theorem gameSum_isCore
    {α : Type*} (s : Finset α) (f : α → CoalGame ι) (x : α → ι → ℝ)
    (hx : ∀ a ∈ s, (f a).IsCore (x a)) :
    (gameSum s f).IsCore (fun i => ∑ a ∈ s, x a i) := by
  classical
  refine ⟨?_, ?_⟩
  · calc
      ∑ i, (∑ a ∈ s, x a i)
          = ∑ a ∈ s, ∑ i, x a i := by
            rw [Finset.sum_comm]
      _ = ∑ a ∈ s, (f a).v Finset.univ := by
            refine Finset.sum_congr rfl ?_
            intro a ha
            exact (IsCore.efficient (f a) (hx a ha))
      _ = (gameSum s f).v Finset.univ := rfl
  · intro T
    calc
      ∑ i ∈ T, (∑ a ∈ s, x a i)
          = ∑ a ∈ s, ∑ i ∈ T, x a i := by
            rw [Finset.sum_comm]
      _ ≥ ∑ a ∈ s, (f a).v T := by
            exact Finset.sum_le_sum (fun a ha =>
              IsCore.coalition_rational (f a) (hx a ha) T)
      _ = (gameSum s f).v T := rfl

end FinitePlayers

/-- The constant-zero coalitional game. -/
noncomputable def zeroGame : CoalGame ι where
  v := fun _ => 0
  v_empty := rfl

section FinitePlayers

variable [Fintype ι]

/-- The Shapley value of the zero game is in its core. -/
theorem zeroGame_shapleyValue_isCore :
    (zeroGame (ι := ι)).IsCore (fun i => (zeroGame (ι := ι)).shapleyValue i) := by
  constructor
  · exact shapleyValue_efficient (zeroGame (ι := ι))
  · intro S
    apply Finset.sum_nonneg
    intro i _
    have hnull : (zeroGame (ι := ι)).IsNull i := by
      intro T _
      simp [marginalContribution, zeroGame]
    rw [shapleyValue_null _ hnull]

end FinitePlayers

/-- The S-th term in the unanimity-basis decomposition of `G`:
`c_S · u_S` for nonempty S, and the zero game when `S = ∅`. -/
noncomputable def decompTerm (G : CoalGame ι) (S : Finset ι) : CoalGame ι :=
  if hS : S.Nonempty then gameScalar (G.unanimityCoeff S) (unanimityGame S hS)
  else zeroGame

section FinitePlayers

variable [Fintype ι]

/-- **Sum-game form of the unanimity decomposition**: every coalitional
game `G` equals the `gameSum` over all subsets of `univ` of its
unanimity-decomposition terms. -/
theorem eq_gameSum_decompTerm (G : CoalGame ι) :
    G = gameSum (Finset.univ : Finset (Finset ι)) G.decompTerm := by
  ext T
  simp only [gameSum_v]
  -- Pair each S with its v-contribution.
  have hterm : ∀ S : Finset ι,
      (G.decompTerm S).v T =
        G.unanimityCoeff S * (if S ⊆ T then 1 else 0) := by
    intro S
    simp only [decompTerm]
    by_cases hS : S.Nonempty
    · simp only [hS, dif_pos, gameScalar, unanimityGame]
    · simp only [hS, dif_neg, zeroGame, not_false_iff]
      have hSe : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      have h_coeff : G.unanimityCoeff S = 0 := by
        subst hSe
        simp [unanimityCoeff, G.v_empty]
      rw [h_coeff, zero_mul]
  rw [Finset.sum_congr rfl (fun S _ => hterm S)]
  -- Convert `c * (if ... then 1 else 0)` to `if ... then c else 0`, then filter.
  have hmul : ∀ S : Finset ι, G.unanimityCoeff S * (if S ⊆ T then (1 : ℝ) else 0) =
      if S ⊆ T then G.unanimityCoeff S else 0 := by
    intro S; split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun S _ => hmul S)]
  rw [← Finset.sum_filter]
  rw [show (Finset.univ.filter (fun S : Finset ι => S ⊆ T)) = T.powerset by
    ext S; simp [Finset.mem_powerset]]
  exact G.unanimity_decomposition T

/-- **Shapley uniqueness** (Shapley 1953): any allocation `φ` satisfying
*efficiency*, *symmetry*, the *null-player* axiom, *additivity*, and
*scalar-homogeneity* (jointly, linearity) coincides with the Shapley value
on every coalitional game.

Note: the classical statement uses only additivity (not full scalar
homogeneity), and recovers scalar homogeneity for rationals via additivity.
Extending to ℝ requires either continuity or full linearity; we adopt the
modern formulation with linearity as a primitive axiom. -/
theorem shapleyValue_unique
    (φ : CoalGame ι → ι → ℝ)
    (h_eff : ∀ G : CoalGame ι, ∑ i, φ G i = G.v Finset.univ)
    (h_sym : ∀ (G : CoalGame ι) {i j : ι},
        i ≠ j → G.AreSymmetric i j → φ G i = φ G j)
    (h_null : ∀ (G : CoalGame ι) {i : ι}, G.IsNull i → φ G i = 0)
    (h_add : ∀ (G₁ G₂ : CoalGame ι) (i : ι),
        φ (gameAdd G₁ G₂) i = φ G₁ i + φ G₂ i)
    (h_scalar : ∀ (c : ℝ) (G : CoalGame ι) (i : ι),
        φ (gameScalar c G) i = c * φ G i)
    (G : CoalGame ι) (i : ι) :
    φ G i = G.shapleyValue i := by
  classical
  -- Both φ and shapleyValue factor over the gameSum decomposition into a
  -- combination of values on unanimity games. Pin both to the same formula.
  have hφ_sum : φ G i = ∑ S : Finset ι, φ (G.decompTerm S) i := by
    nth_rewrite 1 [G.eq_gameSum_decompTerm]
    exact gameSum_allocation_eq φ h_add _ _ i
  have hs_sum : G.shapleyValue i =
      ∑ S : Finset ι, (G.decompTerm S).shapleyValue i := by
    nth_rewrite 1 [G.eq_gameSum_decompTerm]
    exact gameSum_allocation_eq shapleyValue
      (fun G₁ G₂ j => shapleyValue_additive G₁ G₂ j) _ _ i
  rw [hφ_sum, hs_sum]
  -- Show termwise equality.
  refine Finset.sum_congr rfl (fun S _ => ?_)
  simp only [decompTerm]
  by_cases hS : S.Nonempty
  · -- Nonempty S: both sides equal c_S · (1/|S| if i ∈ S else 0).
    simp only [hS, dif_pos]
    rw [h_scalar,
      allocation_on_unanimityGame φ h_eff h_sym h_null S hS i,
      shapleyValue_scalar,
      allocation_on_unanimityGame shapleyValue
        shapleyValue_efficient shapleyValue_symmetric shapleyValue_null S hS i]
  · -- Empty S: both sides are zero (zero game).
    simp only [hS, dif_neg, not_false_iff]
    have hnull_all : (zeroGame (ι := ι)).IsNull i := by
      intro T _
      simp [marginalContribution, zeroGame]
    rw [h_null zeroGame hnull_all,
      shapleyValue_null zeroGame hnull_all]

end FinitePlayers

end CoalGame

end GameTheory
