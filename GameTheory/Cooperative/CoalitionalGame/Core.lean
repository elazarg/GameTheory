/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Sum
import Math.Probability

open scoped BigOperators

namespace GameTheory

open Math.Probability

/-- A transferable-utility coalitional game: `v S` is the value of coalition `S`. -/
structure CoalGame (ι : Type) [DecidableEq ι] where
  /-- Characteristic function: value of each coalition. -/
  v : Finset ι → ℝ
  /-- Empty coalition has zero value. -/
  v_empty : v ∅ = 0

namespace CoalGame

variable {ι : Type} [DecidableEq ι]

@[ext]
theorem ext {G₁ G₂ : CoalGame ι} (h : ∀ S, G₁.v S = G₂.v S) : G₁ = G₂ := by
  cases G₁; cases G₂; congr; funext S; exact h S

/-- Marginal contribution of player `i` to coalition `S`. -/
def marginalContribution (G : CoalGame ι) (i : ι) (S : Finset ι) : ℝ :=
  G.v (insert i S) - G.v S

/-- Player `i` is a null player if their marginal contribution to
    every coalition is zero. -/
def IsNull (G : CoalGame ι) (i : ι) : Prop :=
  ∀ S : Finset ι, i ∉ S → G.marginalContribution i S = 0

section FinitePlayers

variable [Fintype ι]

/-- The Shapley value: player `i`'s share. -/
noncomputable def shapleyValue (G : CoalGame ι) (i : ι) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset (Finset ι)).filter (fun S => i ∉ S),
    ((S.card.factorial * (Fintype.card ι - S.card - 1).factorial : ℕ) : ℝ) /
      ((Fintype.card ι).factorial : ℝ) * G.marginalContribution i S

/-- An allocation is in the core if it is efficient and no coalition blocks. -/
def IsCore (G : CoalGame ι) (x : ι → ℝ) : Prop :=
  (∑ i, x i = G.v Finset.univ) ∧
  ∀ S : Finset ι, ∑ i ∈ S, x i ≥ G.v S

/-- Core allocations are efficient: their components sum to `v(N)`. -/
theorem IsCore.efficient (G : CoalGame ι) {x : ι → ℝ} (h : G.IsCore x) :
    ∑ i, x i = G.v Finset.univ := h.1

/-- Core allocations satisfy *coalition rationality*: every coalition gets
at least its own value. -/
theorem IsCore.coalition_rational (G : CoalGame ι) {x : ι → ℝ}
    (h : G.IsCore x) (S : Finset ι) : ∑ i ∈ S, x i ≥ G.v S := h.2 S

/-- **The core is convex (as a set)**: a convex combination of two core
allocations is still in the core. -/
theorem IsCore.convex_combination (G : CoalGame ι) {x y : ι → ℝ}
    (hx : G.IsCore x) (hy : G.IsCore y)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    G.IsCore (fun i => a * x i + b * y i) := by
  refine ⟨?_, ?_⟩
  · -- Efficiency: a · v(univ) + b · v(univ) = (a+b) · v(univ) = v(univ).
    have heq : (∑ i, (a * x i + b * y i)) =
        a * (∑ i, x i) + b * (∑ i, y i) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [heq, IsCore.efficient G hx, IsCore.efficient G hy,
      ← add_mul, hab, one_mul]
  · -- Coalition rationality: weighted sum dominates v(S).
    intro S
    have heq : (∑ i ∈ S, (a * x i + b * y i)) =
        a * (∑ i ∈ S, x i) + b * (∑ i ∈ S, y i) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hxS := IsCore.coalition_rational G hx S
    have hyS := IsCore.coalition_rational G hy S
    have hsplit : G.v S = a * G.v S + b * G.v S := by
      rw [← add_mul, hab, one_mul]
    rw [heq, hsplit]
    exact add_le_add (mul_le_mul_of_nonneg_left hxS ha)
      (mul_le_mul_of_nonneg_left hyS hb)

/-- **Core dominates singleton values**: if `x` is in the core, every
player gets at least their stand-alone value. -/
theorem IsCore.individually_rational (G : CoalGame ι) {x : ι → ℝ}
    (h : G.IsCore x) (i : ι) : x i ≥ G.v ({i} : Finset ι) := by
  have := IsCore.coalition_rational G h {i}
  simpa using this

/-- A null player gets Shapley value 0. -/
theorem shapleyValue_null (G : CoalGame ι) {i : ι} (h : G.IsNull i) :
    G.shapleyValue i = 0 := by
  simp only [shapleyValue]
  apply Finset.sum_eq_zero
  intro S hS
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
  rw [h S hS, mul_zero]

end FinitePlayers

/-- Sum of two coalitional games. -/
def gameAdd (G₁ G₂ : CoalGame ι) : CoalGame ι where
  v := fun S => G₁.v S + G₂.v S
  v_empty := by simp [G₁.v_empty, G₂.v_empty]

section FinitePlayers

variable [Fintype ι]

/-- Shapley value is additive across games. -/
theorem shapleyValue_additive (G₁ G₂ : CoalGame ι) (i : ι) :
    (gameAdd G₁ G₂).shapleyValue i = G₁.shapleyValue i + G₂.shapleyValue i := by
  simp only [shapleyValue, gameAdd, marginalContribution]
  rw [← Finset.sum_add_distrib]
  congr 1
  ext S
  ring

end FinitePlayers

/-- Two players are symmetric if swapping them in any coalition
    preserves the value. -/
def AreSymmetric (G : CoalGame ι) (i j : ι) : Prop :=
  ∀ S : Finset ι, i ∉ S → j ∉ S → G.v (insert i S) = G.v (insert j S)

/-- Symmetric players have the same marginal contribution to coalitions
    containing neither of them. -/
theorem marginalContribution_eq_of_symmetric (G : CoalGame ι) {i j : ι}
    (hsym : G.AreSymmetric i j) {S : Finset ι}
    (hi : i ∉ S) (hj : j ∉ S) :
    G.marginalContribution i S = G.marginalContribution j S := by
  simp only [marginalContribution]
  rw [hsym S hi hj]

/-- Scalar multiplication of coalitional games. -/
def gameScalar (c : ℝ) (G : CoalGame ι) : CoalGame ι where
  v := fun S => c * G.v S
  v_empty := by simp [G.v_empty]

/-- `gameScalar` preserves null players. -/
theorem gameScalar_isNull {c : ℝ} {G : CoalGame ι} {i : ι} (h : G.IsNull i) :
    (gameScalar c G).IsNull i := by
  intro S hS
  have hmc := h S hS
  simp only [marginalContribution, gameScalar] at hmc ⊢
  have hv : G.v (insert i S) = G.v S := by linarith
  rw [hv]; ring

/-- `gameScalar` preserves symmetry of players. -/
theorem gameScalar_areSymmetric {c : ℝ} {G : CoalGame ι} {i j : ι}
    (h : G.AreSymmetric i j) : (gameScalar c G).AreSymmetric i j := by
  intro S hi hj
  simp only [gameScalar]
  rw [h S hi hj]

section FinitePlayers

variable [Fintype ι]

/-- Shapley value is linear: scales with scalar multiplication. -/
theorem shapleyValue_scalar (c : ℝ) (G : CoalGame ι) (i : ι) :
    (gameScalar c G).shapleyValue i = c * G.shapleyValue i := by
  simp only [shapleyValue, gameScalar, marginalContribution]
  rw [Finset.mul_sum]
  congr 1; ext S; ring

/-! ### Core closure under linear game operations -/

/-- The sum of two core allocations is a core allocation of the sum game. -/
theorem IsCore.gameAdd {G₁ G₂ : CoalGame ι} {x y : ι → ℝ}
    (hx : G₁.IsCore x) (hy : G₂.IsCore y) :
    (gameAdd G₁ G₂).IsCore (fun i => x i + y i) := by
  refine ⟨?_, ?_⟩
  · rw [Finset.sum_add_distrib, IsCore.efficient G₁ hx, IsCore.efficient G₂ hy]
    rfl
  · intro S
    rw [Finset.sum_add_distrib]
    exact add_le_add (IsCore.coalition_rational G₁ hx S)
      (IsCore.coalition_rational G₂ hy S)

/-- A nonnegative scalar multiple of a core allocation is a core allocation
of the scaled game. -/
theorem IsCore.gameScalar {G : CoalGame ι} {x : ι → ℝ}
    (hx : G.IsCore x) {c : ℝ} (hc : 0 ≤ c) :
    (gameScalar c G).IsCore (fun i => c * x i) := by
  refine ⟨?_, ?_⟩
  · rw [← Finset.mul_sum, IsCore.efficient G hx]
    rfl
  · intro S
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (IsCore.coalition_rational G hx S) hc

open Classical in
/-- Symmetric players have the same Shapley value. -/
theorem shapleyValue_symmetric (G : CoalGame ι) {i j : ι} (hne : i ≠ j)
    (hsym : G.AreSymmetric i j) :
    G.shapleyValue i = G.shapleyValue j := by
  simp only [shapleyValue]
  set Si := (Finset.univ : Finset (Finset ι)).filter (fun S => i ∉ S)
  set Sj := (Finset.univ : Finset (Finset ι)).filter (fun S => j ∉ S)
  let swap (a b : ι) (S : Finset ι) : Finset ι :=
    if b ∈ S then insert a (S.erase b) else S
  have swap_mem (a b : ι) (hab : a ≠ b) (S : Finset ι) (ha : a ∉ S) :
      b ∉ swap a b S := by
    simp only [swap]
    split_ifs with hb
    · intro hmem
      rcases Finset.mem_insert.mp hmem with rfl | hbe
      · exact hab rfl
      · exact (Finset.notMem_erase b S) hbe
    · exact hb
  have swap_inv (a b : ι) (hab : a ≠ b) (S : Finset ι) (ha : a ∉ S) :
      swap b a (swap a b S) = S := by
    change (if a ∈ (if b ∈ S then insert a (S.erase b) else S)
      then insert b ((if b ∈ S then insert a (S.erase b) else S).erase a)
      else (if b ∈ S then insert a (S.erase b) else S)) = S
    by_cases hb : b ∈ S
    · simp only [hb, ↓reduceIte, Finset.mem_insert_self]
      have ha_ne : a ∉ S.erase b := by
        intro hmem; exact ha (Finset.mem_of_mem_erase hmem)
      rw [Finset.erase_insert ha_ne, Finset.insert_erase hb]
    · simp only [hb, ↓reduceIte, show a ∉ S from ha]
  have swap_card (a b : ι) (S : Finset ι) (ha : a ∉ S) (hb : b ∈ S) :
      (swap a b S).card = S.card := by
    simp only [swap, hb, ↓reduceIte]
    have : a ∉ S.erase b := by
      simp only [Finset.mem_erase]; exact fun ⟨_, h⟩ => ha h
    rw [Finset.card_insert_of_notMem this, Finset.card_erase_of_mem hb]
    have : 0 < S.card := Finset.card_pos.mpr ⟨b, hb⟩
    omega
  apply Finset.sum_nbij' (swap i j) (swap j i)
  · intro S hS
    simp only [Si, Finset.mem_filter, Finset.mem_univ, true_and] at hS
    simp only [Sj, Finset.mem_filter, Finset.mem_univ, true_and]
    exact swap_mem i j hne S hS
  · intro T hT
    simp only [Sj, Finset.mem_filter, Finset.mem_univ, true_and] at hT
    simp only [Si, Finset.mem_filter, Finset.mem_univ, true_and]
    exact swap_mem j i hne.symm T hT
  · intro S hS
    simp only [Si, Finset.mem_filter, Finset.mem_univ, true_and] at hS
    exact swap_inv i j hne S hS
  · intro T hT
    simp only [Sj, Finset.mem_filter, Finset.mem_univ, true_and] at hT
    exact swap_inv j i hne.symm T hT
  · intro S hS
    simp only [Si, Finset.mem_filter, Finset.mem_univ, true_and] at hS
    simp only [swap]
    split_ifs with hj
    · have hcard := swap_card i j S hS hj
      simp only [swap, hj, ↓reduceIte] at hcard
      set U := S.erase j with hU_def
      have hiU : i ∉ U := by
        simp only [Finset.mem_erase, hU_def]; exact fun ⟨_, h⟩ => hS h
      have hjU : j ∉ U := Finset.notMem_erase j S
      have hv_sym : G.v (insert i U) = G.v (insert j U) := hsym U hiU hjU
      have hv_S : insert j U = S := Finset.insert_erase hj
      have hv_jT : insert j (insert i U) = insert i S := by
        rw [Finset.insert_comm, hv_S]
      simp only [marginalContribution, hcard, hv_jT, ← hv_S, hv_sym]
    · congr 1
      exact G.marginalContribution_eq_of_symmetric hsym hS hj

/-- **Efficiency of the Shapley value**: the Shapley payouts of all players
sum to the value of the grand coalition. This is one of Shapley's four
axioms and is the property that makes the Shapley value an *allocation*
of `v(N)` among the players. -/
theorem shapleyValue_efficient (G : CoalGame ι) :
    ∑ i, G.shapleyValue i = G.v Finset.univ := by
  classical
  -- Handle the degenerate empty-type case first.
  rcases isEmpty_or_nonempty ι with hempty | hnonempty
  · haveI := hempty
    simp only [Finset.univ_eq_empty, Finset.sum_empty, G.v_empty]
  set n := Fintype.card ι with hn_def
  have hn_pos : 0 < n := by rw [hn_def]; exact Fintype.card_pos
  -- Coefficient appearing inside the Shapley sum.
  let w : ℕ → ℝ := fun s =>
    ((s.factorial * (n - s - 1).factorial : ℕ) : ℝ) / (n.factorial : ℝ)
  -- Step 1: rewrite Σ_i ϕ_i with the filter pushed inside as an indicator,
  -- so we can swap Σ_i and Σ_S freely.
  have hindic : ∀ i : ι, G.shapleyValue i =
      ∑ S : Finset ι, (if i ∉ S then w S.card * (G.v (insert i S) - G.v S) else 0) := by
    intro i
    rw [shapleyValue]
    simp only [marginalContribution, w]
    rw [← Finset.sum_filter]
  rw [Finset.sum_congr rfl (fun i _ => hindic i)]
  -- Step 2: swap Σ_i and Σ_S.
  rw [Finset.sum_comm]
  -- Step 3: split each inner sum into a positive (v(S∪{i})) and negative (v(S)) half.
  have hinner : ∀ S : Finset ι,
      (∑ i, if i ∉ S then w S.card * (G.v (insert i S) - G.v S) else 0) =
        (∑ i ∈ Sᶜ, w S.card * G.v (insert i S))
        - w S.card * G.v S * (Sᶜ.card : ℝ) := by
    intro S
    have hfilter : (Finset.univ.filter (fun i : ι => i ∉ S)) = Sᶜ := by
      ext i; simp [Finset.mem_compl]
    rw [← Finset.sum_filter, hfilter]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [Finset.sum_congr rfl (fun S _ => hinner S)]
  rw [Finset.sum_sub_distrib]
  -- Step 4: reindex the positive part using (S, i ∉ S) ↔ (T = S∪{i}, i ∈ T).
  have hpos : (∑ S : Finset ι, ∑ i ∈ Sᶜ, w S.card * G.v (insert i S)) =
      ∑ T : Finset ι, (T.card : ℝ) * w (T.card - 1) * G.v T := by
    let σ : Finset ι → Type := fun _ => ι
    let fL : Sigma σ → ℝ := fun p => w p.1.card * G.v (insert p.2 p.1)
    let fR : Sigma σ → ℝ := fun p => w (p.1.card - 1) * G.v p.1
    -- LHS as a sigma sum.
    have hLHS : (∑ S : Finset ι, ∑ i ∈ Sᶜ, w S.card * G.v (insert i S)) =
        ∑ p ∈ (Finset.univ : Finset (Finset ι)).sigma
            (fun S : Finset ι => (Sᶜ : Finset ι)), fL p :=
      (Finset.sum_sigma (σ := σ) _ _ fL).symm
    -- RHS as a sigma sum: first expand T.card as a sum-of-1s, then apply sum_sigma.
    have hRHS_nest : (∑ T : Finset ι, (T.card : ℝ) * w (T.card - 1) * G.v T) =
        ∑ T : Finset ι, ∑ _ ∈ T, w (T.card - 1) * G.v T := by
      refine Finset.sum_congr rfl (fun T _ => ?_)
      rw [Finset.sum_const, nsmul_eq_mul]; ring
    have hRHS_sigma : (∑ T : Finset ι, ∑ _ ∈ T, w (T.card - 1) * G.v T) =
        ∑ p ∈ (Finset.univ : Finset (Finset ι)).sigma (fun T : Finset ι => T), fR p :=
      (Finset.sum_sigma (σ := σ) _ _ fR).symm
    rw [hLHS, hRHS_nest, hRHS_sigma]
    refine Finset.sum_nbij'
      (i := fun p : Sigma σ => ⟨insert p.2 p.1, p.2⟩)
      (j := fun p : Sigma σ => ⟨p.1.erase p.2, p.2⟩)
      ?_ ?_ ?_ ?_ ?_
    · rintro ⟨S, i⟩ hp
      simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_compl, true_and] at hp
      simp only [Finset.mem_sigma, Finset.mem_univ, true_and]
      exact Finset.mem_insert_self i S
    · rintro ⟨T, i⟩ hp
      simp only [Finset.mem_sigma, Finset.mem_univ, true_and] at hp
      simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_compl, true_and]
      exact Finset.notMem_erase i T
    · rintro ⟨S, i⟩ hp
      simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_compl, true_and] at hp
      simp [Finset.erase_insert hp]
    · rintro ⟨T, i⟩ hp
      simp only [Finset.mem_sigma, Finset.mem_univ, true_and] at hp
      simp [Finset.insert_erase hp]
    · rintro ⟨S, i⟩ hp
      simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_compl, true_and] at hp
      simp only [fL, fR, Finset.card_insert_of_notMem hp, Nat.add_sub_cancel]
  -- Step 5: combine the two sums into a single Σ_T coeff(T) · v(T).
  rw [hpos]
  rw [show (∑ T : Finset ι, (T.card : ℝ) * w (T.card - 1) * G.v T) -
      (∑ T : Finset ι, w T.card * G.v T * (Tᶜ.card : ℝ)) =
      ∑ T : Finset ι, ((T.card : ℝ) * w (T.card - 1) - w T.card * (Tᶜ.card : ℝ)) * G.v T from by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun T _ => ?_)
    ring]
  -- Step 6: only T = Finset.univ contributes; everything else is 0.
  rw [Finset.sum_eq_single Finset.univ]
  · -- Value at T = univ: coefficient is 1.
    have h_univ_card : (Finset.univ : Finset ι).card = n := Finset.card_univ.trans hn_def.symm
    have h_complc : (Finset.univᶜ : Finset ι).card = 0 := by
      simp [Finset.compl_univ]
    rw [h_univ_card, h_complc]
    simp only [Nat.cast_zero, mul_zero, sub_zero, w]
    obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := Nat.exists_eq_succ_of_ne_zero hn_pos.ne'
    have h_sub : n - 1 = m := by omega
    have h_sub2 : n - (n - 1) - 1 = 0 := by omega
    rw [h_sub2, Nat.factorial_zero, mul_one]
    rw [h_sub, hm, Nat.factorial_succ]
    field_simp
    push_cast
    ring
  · -- For T ≠ univ: term is 0, by cases on T = ∅ or 0 < |T| < n.
    intro T _ hT_ne
    rcases Finset.eq_empty_or_nonempty T with hempty | hT_nonempty
    · subst hempty
      simp [G.v_empty]
    · -- T ≠ ∅, T ≠ univ ⇒ 1 ≤ |T| < n. The coefficient is 0.
      have hcard_pos : 0 < T.card := Finset.card_pos.mpr hT_nonempty
      have hcard_lt : T.card < n := by
        rw [hn_def]
        exact Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hT_ne)
      suffices hcoeff_eq : (T.card : ℝ) * w (T.card - 1) = w T.card * (Tᶜ.card : ℝ) by
        rw [hcoeff_eq, sub_self, zero_mul]
      -- Numerator identity in ℕ.
      have hsub_eq : n - (T.card - 1) - 1 = n - T.card := by omega
      have hfact_self : ∀ k, 0 < k → k * (k - 1).factorial = k.factorial := by
        intro k hk
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := Nat.exists_eq_succ_of_ne_zero hk.ne'
        rw [Nat.add_sub_cancel, Nat.factorial_succ]
      have hfact1 := hfact_self T.card hcard_pos
      have hfact2 := hfact_self (n - T.card) (by omega)
      have hkey : T.card * ((T.card - 1).factorial * (n - T.card).factorial) =
          T.card.factorial * (n - T.card - 1).factorial * (n - T.card) := by
        rw [show T.card * ((T.card - 1).factorial * (n - T.card).factorial) =
            (T.card * (T.card - 1).factorial) * (n - T.card).factorial from by ring,
          hfact1, show T.card.factorial * (n - T.card - 1).factorial * (n - T.card) =
            T.card.factorial * ((n - T.card) * (n - T.card - 1).factorial) from by ring,
          hfact2]
      -- Lift to ℝ.
      simp only [w]
      rw [Finset.card_compl, ← hn_def, hsub_eq]
      rw [mul_div_assoc', div_mul_eq_mul_div]
      congr 1
      exact_mod_cast hkey
  · intro h
    exact absurd (Finset.mem_univ _) h

end FinitePlayers

end CoalGame

end GameTheory
