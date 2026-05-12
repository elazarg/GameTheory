import GameTheory.Core.KernelGame
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Sum
import Math.Probability

/-!
# Coalitional Games and the Shapley Value

A coalitional (transferable utility) game assigns a value to each
coalition of players. The Shapley value (1953) is the unique allocation
satisfying efficiency, symmetry, dummy, and additivity axioms.

## Main definitions

* `CoalGame` — TU coalitional game
* `CoalGame.shapleyValue` — the Shapley value
* `CoalGame.marginalContribution` — player's marginal contribution to a coalition
* `CoalGame.IsCore` — the core of a coalitional game

## Main results

* `shapleyValue_null` — null players get Shapley value 0
* `shapleyValue_additive` — Shapley value is additive across games
* `shapleyValue_symmetric` — symmetric players have the same Shapley value
-/

open scoped BigOperators

namespace GameTheory

open Math.Probability

/-- A transferable-utility coalitional game: `v S` is the value of coalition `S`. -/
structure CoalGame (ι : Type) [Fintype ι] [DecidableEq ι] where
  /-- Characteristic function: value of each coalition. -/
  v : Finset ι → ℝ
  /-- Empty coalition has zero value. -/
  v_empty : v ∅ = 0

namespace CoalGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

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

/-- The Shapley value: player `i`'s share. -/
noncomputable def shapleyValue (G : CoalGame ι) (i : ι) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset (Finset ι)).filter (fun S => i ∉ S),
    ((S.card.factorial * (Fintype.card ι - S.card - 1).factorial : ℕ) : ℝ) /
      ((Fintype.card ι).factorial : ℝ) * G.marginalContribution i S

/-- An allocation is in the core if it is efficient and no coalition blocks. -/
def IsCore (G : CoalGame ι) (x : ι → ℝ) : Prop :=
  (∑ i, x i = G.v Finset.univ) ∧
  ∀ S : Finset ι, ∑ i ∈ S, x i ≥ G.v S

/-- A null player gets Shapley value 0. -/
theorem shapleyValue_null (G : CoalGame ι) {i : ι} (h : G.IsNull i) :
    G.shapleyValue i = 0 := by
  simp only [shapleyValue]
  apply Finset.sum_eq_zero
  intro S hS
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
  rw [h S hS, mul_zero]

/-- Sum of two coalitional games. -/
def gameAdd (G₁ G₂ : CoalGame ι) : CoalGame ι where
  v := fun S => G₁.v S + G₂.v S
  v_empty := by simp [G₁.v_empty, G₂.v_empty]

/-- Shapley value is additive across games. -/
theorem shapleyValue_additive (G₁ G₂ : CoalGame ι) (i : ι) :
    (gameAdd G₁ G₂).shapleyValue i = G₁.shapleyValue i + G₂.shapleyValue i := by
  simp only [shapleyValue, gameAdd, marginalContribution]
  rw [← Finset.sum_add_distrib]
  congr 1
  ext S
  ring

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

/-- Shapley value is linear: scales with scalar multiplication. -/
theorem shapleyValue_scalar (c : ℝ) (G : CoalGame ι) (i : ι) :
    (gameScalar c G).shapleyValue i = c * G.shapleyValue i := by
  simp only [shapleyValue, gameScalar, marginalContribution]
  rw [Finset.mul_sum]
  congr 1; ext S; ring

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

/-- The grand coalition contains every nonempty `S`, so the unanimity
game on `S` has value `1` on `univ`. -/
theorem unanimityGame_v_univ (S : Finset ι) (hS : S.Nonempty) :
    (unanimityGame S hS).v Finset.univ = 1 := by
  have : S ⊆ Finset.univ := S.subset_univ
  simp [unanimityGame, this]

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
      refine ⟨fun ⟨hST, hRS⟩ => ⟨S \ R, ?_, ?_⟩, ?_⟩
      · intro x hx
        simp only [Finset.mem_sdiff] at hx
        exact Finset.mem_sdiff.mpr ⟨hST hx.1, hx.2⟩
      · ext x
        simp only [Finset.mem_union, Finset.mem_sdiff]
        refine ⟨fun h => h.elim (fun a => hRS a) (fun ⟨a, _⟩ => a), fun hxS => ?_⟩
        by_cases hxR : x ∈ R
        · exact Or.inl hxR
        · exact Or.inr ⟨hxS, hxR⟩
      · rintro ⟨X, hX, rfl⟩
        refine ⟨?_, Finset.subset_union_left⟩
        intro x hx
        rcases Finset.mem_union.mp hx with hxR | hxX
        · exact hR hxR
        · exact (Finset.mem_sdiff.mp (hX hxX)).1
    rw [hreindex]
    have hinj : Set.InjOn (fun X => R ∪ X) ((T \ R).powerset : Set (Finset ι)) := by
      intro X hX Y hY hXY
      simp only [Finset.coe_powerset] at hX hY
      have hXdisj : Disjoint R X := Finset.disjoint_left.mpr fun x hxR hxX => by
        have : x ∈ T \ R := hX hxX
        exact (Finset.mem_sdiff.mp this).2 hxR
      have hYdisj : Disjoint R Y := Finset.disjoint_left.mpr fun x hxR hxY => by
        have : x ∈ T \ R := hY hxY
        exact (Finset.mem_sdiff.mp this).2 hxR
      have := congrArg (· \ R) hXY
      simp only [Finset.union_sdiff_left,
        Finset.sdiff_eq_self_of_disjoint hXdisj.symm,
        Finset.sdiff_eq_self_of_disjoint hYdisj.symm] at this
      exact this
    rw [Finset.sum_image (fun X hX Y hY => hinj hX hY)]
    -- The exponent simplifies because R and X are disjoint.
    have hcard_eq : ∀ X ∈ (T \ R).powerset,
        (R ∪ X).card - R.card = X.card := by
      intro X hX
      simp only [Finset.mem_powerset] at hX
      have hdisj : Disjoint R X := Finset.disjoint_left.mpr fun x hxR hxX => by
        exact (Finset.mem_sdiff.mp (hX hxX)).2 hxR
      rw [Finset.card_union_of_disjoint hdisj, Nat.add_sub_cancel_left]
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
  -- Only R = T contributes.
  rw [Finset.sum_eq_single T]
  · simp
  · intro R hR hRne
    simp [hRne]
  · intro hT
    exact absurd (Finset.mem_powerset.mpr (Finset.Subset.refl T)) hT

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

/-- The constant-zero coalitional game. -/
noncomputable def zeroGame : CoalGame ι where
  v := fun _ => 0
  v_empty := rfl

/-- The S-th term in the unanimity-basis decomposition of `G`:
`c_S · u_S` for nonempty S, and the zero game when `S = ∅`. -/
noncomputable def decompTerm (G : CoalGame ι) (S : Finset ι) : CoalGame ι :=
  if hS : S.Nonempty then gameScalar (G.unanimityCoeff S) (unanimityGame S hS)
  else zeroGame

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

end CoalGame

end GameTheory
