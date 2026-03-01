import Mathlib
import Fixpoint.SpernerParity

set_option autoImplicit false

namespace Fixpoint

namespace SpernerParity

/-!
# Per-cell Sperner parity

A facet index `i` of cell `c` is **rainbow** under labeling `L` if removing
vertex `i` leaves all "initial" labels `{0, …, n−1}` (= `Fin.castSucc` image)
represented.  The number of rainbow facets is:
- `1` for fully-labeled cells,
- `0` when some initial label is missing,
- `2` when all initial labels are present but `Fin.last n` is absent.

Hence `rainbowFacetCount L c ≡ cellFullyLabeledIndicatorZ2 L c (mod 2)`.
-/

section RainbowFacets

variable {n m : ℕ}

/-- Face index `i` of cell `c` is "rainbow": after removing vertex `i`,
    every label `k.castSucc` for `k : Fin n` is still present. -/
def IsRainbowFacetIdx (L : Labeling n m) (c : Cell n m) (i : Idx n) : Prop :=
  ∀ k : Fin n, ∃ j : Idx n, j ≠ i ∧ L (c j) = k.castSucc

/-- The finset of rainbow facet indices of a cell. -/
noncomputable def rainbowFacetIndices (L : Labeling n m) (c : Cell n m) :
    Finset (Idx n) := by
  classical
  exact Finset.univ.filter (fun i => IsRainbowFacetIdx L c i)

/-- Number of rainbow facets of a cell. -/
noncomputable def rainbowFacetCount (L : Labeling n m) (c : Cell n m) : ℕ :=
  (rainbowFacetIndices L c).card

-- ────────────────────────────────────────────────────────────
-- Helpers
-- ────────────────────────────────────────────────────────────

private theorem castSucc_ne_last (k : Fin n) : k.castSucc ≠ Fin.last n :=
  ne_of_lt (Fin.castSucc_lt_last k)

private theorem idx_eq_castSucc_or_last (i : Idx n) :
    (∃ k : Fin n, i = k.castSucc) ∨ i = Fin.last n := by
  by_cases h : i.val < n
  · exact Or.inl ⟨⟨i.val, h⟩, by ext; simp [Fin.castSucc]⟩
  · right; ext; simp [Fin.last]; omega

-- ────────────────────────────────────────────────────────────
-- Case 1: Fully labeled ⟹ count = 1
-- ────────────────────────────────────────────────────────────

/-- A fully-labeled cell has exactly one rainbow facet. -/
theorem rainbowFacetCount_eq_one_of_fullyLabeled
    (L : Labeling n m) (c : Cell n m) (hfull : CellFullyLabeled L c) :
    rainbowFacetCount L c = 1 := by
  classical
  let e := labelEquivOfFullyLabeled L c hfull
  let j₀ := e.symm (Fin.last n)
  -- j₀ is rainbow
  have hj₀_rainbow : IsRainbowFacetIdx L c j₀ := by
    intro k
    refine ⟨e.symm k.castSucc, ?_, ?_⟩
    · intro heq
      have h1 := e.apply_symm_apply (k.castSucc)
      have h2 := e.apply_symm_apply (Fin.last n)
      rw [show e.symm (Fin.last n) = j₀ from rfl] at h2
      rw [← heq] at h2
      rw [h1] at h2
      exact absurd h2 (castSucc_ne_last k)
    · show L (c (e.symm k.castSucc)) = k.castSucc
      change e (e.symm k.castSucc) = k.castSucc
      exact e.apply_symm_apply k.castSucc
  -- No other index is rainbow
  have hother : ∀ i : Idx n, i ≠ j₀ → ¬ IsRainbowFacetIdx L c i := by
    intro i hne hi
    have hinj := (fullyLabeled_bijective_labelMap L c hfull).1
    -- L(c i) ≠ Fin.last n
    have hli_ne : L (c i) ≠ Fin.last n := by
      intro heq
      apply hne
      have hei : e i = Fin.last n := by
        simp [e, labelEquivOfFullyLabeled, heq]
      exact e.injective (by rw [hei]; exact (e.apply_symm_apply (Fin.last n)).symm)
    -- So L(c i) = k₀.castSucc for some k₀
    rcases idx_eq_castSucc_or_last (L (c i)) with ⟨k₀, hk₀⟩ | habs
    · -- Rainbow gives j ≠ i with L(c j) = k₀.castSucc = L(c i)
      rcases hi k₀ with ⟨j, hjne, hjlab⟩
      have : L (c j) = L (c i) := by rw [hjlab, hk₀]
      exact hjne (hinj this)
    · exact hli_ne habs
  -- The filter is {j₀}
  have hset : rainbowFacetIndices L c = {j₀} := by
    ext i
    simp only [rainbowFacetIndices, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_singleton]
    exact ⟨fun hi => by_contra (fun hne => hother i hne hi),
           fun hi => hi ▸ hj₀_rainbow⟩
  simp [rainbowFacetCount, hset]

-- ────────────────────────────────────────────────────────────
-- Case 2: Missing initial label ⟹ count = 0
-- ────────────────────────────────────────────────────────────

/-- When an initial label is missing from the cell, no facet is rainbow. -/
theorem rainbowFacetCount_eq_zero_of_missing_label
    (L : Labeling n m) (c : Cell n m)
    (k₀ : Fin n) (hmiss : ∀ j : Idx n, L (c j) ≠ k₀.castSucc) :
    rainbowFacetCount L c = 0 := by
  classical
  have hempty : rainbowFacetIndices L c = ∅ := by
    ext i
    constructor
    · intro hi
      simp only [rainbowFacetIndices, Finset.mem_filter, Finset.mem_univ,
        true_and] at hi
      rcases hi k₀ with ⟨j, _, hjlab⟩
      exact absurd hjlab (hmiss j)
    · intro hi; simp at hi
  simp [rainbowFacetCount, hempty]

-- ────────────────────────────────────────────────────────────
-- Case 3: All initial labels present but not fully labeled ⟹ count = 2
-- ────────────────────────────────────────────────────────────

/-- When all initial labels {0,…,n−1} are present but the cell is not
    fully labeled (so `Fin.last n` is absent), there are exactly 2 rainbow
    facets: the two positions carrying the unique repeated label. -/
theorem rainbowFacetCount_eq_two_of_almostLabeled
    (L : Labeling n m) (c : Cell n m)
    (hall : ∀ k : Fin n, ∃ j : Idx n, L (c j) = k.castSucc)
    (hnotfull : ¬ CellFullyLabeled L c) :
    rainbowFacetCount L c = 2 := by
  classical
  -- Fin.last n is not in the range (otherwise cell would be fully labeled)
  have hlast_miss : ∀ j : Idx n, L (c j) ≠ Fin.last n := by
    intro j heq
    apply hnotfull
    intro i
    rcases idx_eq_castSucc_or_last i with ⟨k, hk⟩ | hlast
    · rw [hk]; exact hall k
    · rw [hlast]; exact ⟨j, heq⟩
  -- Every label is some k.castSucc
  have hcast : ∀ j : Idx n, ∃ k : Fin n, L (c j) = k.castSucc := by
    intro j
    rcases idx_eq_castSucc_or_last (L (c j)) with ⟨k, hk⟩ | hlast
    · exact ⟨k, hk⟩
    · exact absurd hlast (hlast_miss j)
  -- L ∘ c is not injective (n+1 elements → n+1 elements, not surjective)
  have hnotinj : ¬ Function.Injective (fun j : Idx n => L (c j)) := by
    intro hinj
    exact hnotfull (Finite.injective_iff_surjective.mp hinj)
  -- Pick two colliding indices
  rw [Function.Injective] at hnotinj
  push_neg at hnotinj
  rcases hnotinj with ⟨j₁, j₂, hlab_eq, hne⟩
  -- Define g : Idx n → Fin n by projecting labels
  have hval_lt : ∀ j : Idx n, (L (c j)).val < n := by
    intro j
    rcases hcast j with ⟨k, hk⟩
    simp [hk, Fin.castSucc]
  let g : Idx n → Fin n := fun j => ⟨(L (c j)).val, hval_lt j⟩
  have g_eq_iff : ∀ a b : Idx n, g a = g b ↔ L (c a) = L (c b) := by
    intro a b
    simp only [g, Fin.mk.injEq]
    exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
  -- g is surjective
  have g_surj : Function.Surjective g := by
    intro k
    rcases hall k with ⟨j, hj⟩
    exact ⟨j, Fin.ext (by simp [g, hj, Fin.castSucc])⟩
  -- g j₁ = g j₂
  have g_coll : g j₁ = g j₂ := (g_eq_iff j₁ j₂).mpr hlab_eq
  -- Restriction h := g ∘ (j₁.succAbove) : Fin n → Fin n
  let h : Fin n → Fin n := g ∘ j₁.succAbove
  -- h is surjective
  have h_surj : Function.Surjective h := by
    intro k
    by_cases hk : k = g j₁
    · -- Use j₂ (which ≠ j₁)
      rcases Fin.exists_succAbove_eq (show j₂ ≠ j₁ from hne.symm) with ⟨j₂', hj₂'⟩
      exact ⟨j₂', show g (j₁.succAbove j₂') = k by rw [hj₂', hk, ← g_coll]⟩
    · -- Use g's surjectivity: get a with g a = k, then a ≠ j₁
      rcases g_surj k with ⟨a, ha⟩
      have ha_ne : a ≠ j₁ := fun heq => hk (by rw [← ha, heq])
      rcases Fin.exists_succAbove_eq ha_ne with ⟨a', ha'⟩
      exact ⟨a', show g (j₁.succAbove a') = k by rw [ha', ha]⟩
  -- h is injective (surjection Fin n → Fin n is injective)
  have h_inj : Function.Injective h :=
    (Finite.injective_iff_surjective (f := h)).mpr h_surj
  -- Key lemma: fiber of g j₁ is exactly {j₁, j₂}
  have fiber_two : ∀ a : Idx n, L (c a) = L (c j₁) → a = j₁ ∨ a = j₂ := by
    intro a ha
    by_cases haj₁ : a = j₁
    · exact Or.inl haj₁
    · right
      rcases Fin.exists_succAbove_eq haj₁ with ⟨a', ha'⟩
      rcases Fin.exists_succAbove_eq (show j₂ ≠ j₁ from hne.symm) with ⟨j₂', hj₂'⟩
      have hhh : h a' = h j₂' := by
        change g (j₁.succAbove a') = g (j₁.succAbove j₂')
        rw [ha', hj₂']
        exact (g_eq_iff a j₂).mpr (by rw [ha, hlab_eq])
      exact by rw [← ha', ← hj₂', h_inj hhh]
  -- Characterize rainbow: face i is rainbow iff i has a twin with the same label
  have rainbow_iff : ∀ i : Idx n, IsRainbowFacetIdx L c i ↔
      (∃ j : Idx n, j ≠ i ∧ L (c j) = L (c i)) := by
    intro i
    constructor
    · intro hi
      rcases hcast i with ⟨ki, hki⟩
      rcases hi ki with ⟨j, hjne, hjlab⟩
      exact ⟨j, hjne, by rw [hjlab, hki]⟩
    · intro ⟨j, hjne, hjlab⟩ k
      by_cases hk : L (c i) = k.castSucc
      · exact ⟨j, hjne, by rw [hjlab, hk]⟩
      · rcases hall k with ⟨j', hj'⟩
        exact ⟨j', fun heq => hk (heq ▸ hj'), hj'⟩
  -- If i is rainbow and L(c i) ≠ L(c j₁), derive contradiction
  have rainbow_in_fiber : ∀ i : Idx n,
      (∃ j : Idx n, j ≠ i ∧ L (c j) = L (c i)) → i = j₁ ∨ i = j₂ := by
    intro i ⟨j, hjne, hjlab⟩
    -- If L(c i) = L(c j₁), use fiber_two
    by_cases hli : L (c i) = L (c j₁)
    · exact fiber_two i hli
    · -- L(c i) ≠ L(c j₁). Then i ≠ j₁ and j ≠ j₁.
      exfalso
      have hi_ne : i ≠ j₁ := fun h => hli (h ▸ rfl)
      have hj_ne : j ≠ j₁ := fun h => hli (hjlab ▸ h ▸ rfl)
      -- Map both through succAbove
      rcases Fin.exists_succAbove_eq hi_ne with ⟨i', hi'⟩
      rcases Fin.exists_succAbove_eq hj_ne with ⟨j', hj'⟩
      -- h i' = g i = g j = h j'
      have : h i' = h j' := by
        change g (j₁.succAbove i') = g (j₁.succAbove j')
        rw [hi', hj']
        exact (g_eq_iff i j).mpr hjlab.symm
      -- By injectivity: i' = j', hence i = j
      have : i = j := by rw [← hi', ← hj', h_inj this]
      exact hjne this.symm
  -- rainbowFacetIndices = {j₁, j₂}
  have hrainbow_eq : rainbowFacetIndices L c = {j₁, j₂} := by
    ext i
    simp only [rainbowFacetIndices, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hi
      exact rainbow_in_fiber i ((rainbow_iff i).mp hi)
    · intro hi
      rcases hi with h₁ | h₂
      · rw [h₁]; exact (rainbow_iff _).mpr ⟨j₂, hne.symm, hlab_eq.symm⟩
      · rw [h₂]; exact (rainbow_iff _).mpr ⟨j₁, hne, hlab_eq⟩
  rw [rainbowFacetCount, hrainbow_eq]
  simp [Finset.card_pair hne]

-- ────────────────────────────────────────────────────────────
-- Main parity theorem
-- ────────────────────────────────────────────────────────────

/-- **Per-cell Sperner parity**: the rainbow facet count of a cell has the same
    mod-2 value as its fully-labeled indicator. -/
theorem rainbowFacetCount_parity
    (L : Labeling n m) (c : Cell n m) :
    ((rainbowFacetCount L c : ZMod 2) = cellFullyLabeledIndicatorZ2 L c) := by
  classical
  by_cases hfull : CellFullyLabeled L c
  · -- Fully labeled: count = 1
    rw [rainbowFacetCount_eq_one_of_fullyLabeled L c hfull]
    simp [cellFullyLabeledIndicatorZ2, hfull]
  · -- Not fully labeled: count is even (0 or 2)
    simp only [cellFullyLabeledIndicatorZ2, hfull, ite_false]
    by_cases hall : ∀ k : Fin n, ∃ j : Idx n, L (c j) = k.castSucc
    · -- All initial labels present: count = 2
      rw [rainbowFacetCount_eq_two_of_almostLabeled L c hall hfull]
      decide
    · -- Some initial label missing: count = 0
      push_neg at hall
      rcases hall with ⟨k₀, hk₀⟩
      rw [rainbowFacetCount_eq_zero_of_missing_label L c k₀ (by
        intro j; exact hk₀ j)]
      simp

end RainbowFacets

end SpernerParity

end Fixpoint
