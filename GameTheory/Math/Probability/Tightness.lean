/-
# Uniform tightness of discrete probability-law families

Finite sets capture nearly all mass uniformly across a sequence of ordinary
PMFs. The family index and ambient outcome type need not be countable.
-/

import GameTheory.Math.Probability.Expectation

noncomputable section

namespace GameTheory.Math.Probability

/-- Every law in the sequence assigns at least `1 - ε` mass to one common
finite set, for each positive `ε`. -/
def UniformlyTight {κ α : Type*} (family : κ → PMF α) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ s : Finset α,
    ∀ k, 1 - ε ≤ ∑ a ∈ s, (family k a).toReal

/-- Reindexing a uniformly tight family preserves its finite mass bounds. -/
theorem UniformlyTight.comp {κ ξ α : Type*} {family : κ → PMF α}
    (h : UniformlyTight family) (index : ξ → κ) :
    UniformlyTight (family ∘ index) := by
  intro ε hε
  obtain ⟨s, hs⟩ := h ε hε
  exact ⟨s, fun k => hs (index k)⟩

/-- A fixed ordinary PMF is tight on any ambient carrier. -/
theorem uniformlyTight_const {κ α : Type*} (law : PMF α) :
    UniformlyTight (fun _ : κ => law) := by
  intro ε hε
  have hsum : HasSum (fun a : α => (law a).toReal) 1 := by
    simpa only [pmf_weight_tsum_one law] using (pmf_weight_summable law).hasSum
  have hnear : Set.Ioi (1 - ε) ∈ nhds (1 : ℝ) :=
    Ioi_mem_nhds (by linarith)
  obtain ⟨s, hs⟩ := (hsum.eventually hnear).exists
  exact ⟨s, fun _ => le_of_lt hs⟩

/-- Choosing at each time between two uniformly tight sequences remains
uniformly tight. The union of their finite witnesses captures either law. -/
theorem UniformlyTight.ite {κ α : Type*} {first second : κ → PMF α}
    (hfirst : UniformlyTight first) (hsecond : UniformlyTight second)
    (choose : κ → Prop) [DecidablePred choose] :
    UniformlyTight (fun k => if choose k then first k else second k) := by
  classical
  intro ε hε
  obtain ⟨s, hs⟩ := hfirst ε hε
  obtain ⟨t, ht⟩ := hsecond ε hε
  refine ⟨s ∪ t, fun k => ?_⟩
  by_cases hk : choose k
  · simpa only [hk, ↓reduceIte] using
      (hs k).trans (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_union_left) (fun a _ _ => ENNReal.toReal_nonneg))
  · simpa only [hk, ↓reduceIte] using
      (ht k).trans (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_union_right) (fun a _ _ => ENNReal.toReal_nonneg))

/-- Every family on a finite carrier is uniformly tight. -/
theorem uniformlyTight_of_finite {κ α : Type*} [Finite α]
    (family : κ → PMF α) : UniformlyTight family := by
  intro ε hε
  let s : Finset α := Set.finite_univ.toFinset
  refine ⟨s, fun k => ?_⟩
  have hmass : (∑ a ∈ s, (family k a).toReal) = 1 := by
    calc
      (∑ a ∈ s, (family k a).toReal) =
          ∑' a, (family k a).toReal := by
        symm
        apply tsum_eq_sum
        intro a ha
        exact False.elim (ha (by simp [s]))
      _ = 1 := pmf_weight_tsum_one (family k)
  rw [hmass]
  linarith

end GameTheory.Math.Probability
