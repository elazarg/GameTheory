/-
# Tight discrete PMF families and countable-coordinate compactness

Uniform finite-set tightness prevents mass escaping from any discrete PMF
coordinate. Countability of the coordinate family and of the union of its
supports lets Mathlib's compact-product theorem extract one subsequence.
No topology is imposed on the semantic PMF type.
-/

import GameTheory.Math.Probability.Convergence
import GameTheory.Math.Probability.Tightness
import Mathlib.Topology.Sequences

noncomputable section

namespace GameTheory.Math.Probability

/-- Countably many uniformly tight sequences of discrete laws on arbitrary
carriers have one subsequence along which all atom masses converge to PMFs.
Only the union of the laws' countable supports enters the compact product. -/
theorem exists_subseq_pmfConvergesPointwise_pi_of_uniformlyTight
    {ι : Type*} [Countable ι] {A : ι → Type*}
    (sequence : ℕ → ∀ i, PMF (A i))
    (htight : ∀ i, UniformlyTight (fun n => sequence n i)) :
    ∃ (target : ∀ i, PMF (A i)) (subseq : ℕ → ℕ),
      StrictMono subseq ∧
        ∀ i, PMFConvergesPointwise (fun n => sequence (subseq n) i) (target i) := by
  classical
  let supportIndex (n : ℕ) := (i : ι) × (sequence n i).support
  have hcount (n : ℕ) : Countable (supportIndex n) := by
    have (i : ι) : Countable (sequence n i).support :=
      (sequence n i).support_countable.to_subtype
    infer_instance
  let S : Set ((i : ι) × A i) := ⋃ n,
    Set.range (fun coordinate : supportIndex n =>
      (⟨coordinate.1, coordinate.2.1⟩ : (i : ι) × A i))
  have hS : S.Countable := by
    apply Set.countable_iUnion
    intro n
    have : Countable (supportIndex n) := hcount n
    exact Set.countable_range _
  have : Countable S := hS.to_subtype
  have hmember (n : ℕ) (i : ι) (a : A i)
      (ha : sequence n i a ≠ 0) : (⟨i, a⟩ : (i : ι) × A i) ∈ S := by
    apply Set.mem_iUnion.mpr
    exact ⟨n, ⟨⟨i, ⟨a, ha⟩⟩, rfl⟩⟩
  let weights (n : ℕ) (coordinate : S) : ℝ :=
    (sequence n coordinate.1.1 coordinate.1.2).toReal
  have hcompact : IsCompact {w : S → ℝ | ∀ coordinate, w coordinate ∈ Set.Icc 0 1} :=
    isCompact_pi_infinite fun _ => isCompact_Icc
  have hweights (n : ℕ) :
      weights n ∈ {w : S → ℝ | ∀ coordinate, w coordinate ∈ Set.Icc 0 1} := by
    intro coordinate
    refine ⟨ENNReal.toReal_nonneg, ?_⟩
    have hmass := (pmf_weight_summable
      (sequence n coordinate.1.1)).sum_le_tsum
        {coordinate.1.2} (fun _ _ => ENNReal.toReal_nonneg)
    simpa [pmf_weight_tsum_one] using hmass
  obtain ⟨limit, _, subseq, hsubseq, hlimit⟩ :=
    hcompact.tendsto_subseq (x := weights) hweights
  let mass (i : ι) (a : A i) : ℝ :=
    if h : (⟨i, a⟩ : (i : ι) × A i) ∈ S then limit ⟨⟨i, a⟩, h⟩ else 0
  have hmass_tendsto (i : ι) (a : A i) :
      Filter.Tendsto (fun n => (sequence (subseq n) i a).toReal)
        Filter.atTop (nhds (mass i a)) := by
    by_cases ha : (⟨i, a⟩ : (i : ι) × A i) ∈ S
    · simpa only [mass, dite_eq_left ha, weights, Function.comp_def] using
        ((continuous_apply (⟨⟨i, a⟩, ha⟩ : S)).tendsto limit).comp hlimit
    · have hzero (n : ℕ) : sequence n i a = 0 := by
        by_contra hne
        exact ha (hmember n i a hne)
      simpa only [mass, dite_eq_right ha, hzero, ENNReal.toReal_zero] using
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0 : ℝ))
          Filter.atTop (nhds 0))
  have hmass_nonneg (i : ι) (a : A i) : 0 ≤ mass i a :=
    ge_of_tendsto (hmass_tendsto i a)
      (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
  have hfin_le (i : ι) (s : Finset (A i)) : ∑ a ∈ s, mass i a ≤ 1 := by
    have hsum : Filter.Tendsto
        (fun n => ∑ a ∈ s, (sequence (subseq n) i a).toReal)
        Filter.atTop (nhds (∑ a ∈ s, mass i a)) :=
      tendsto_finsetSum s (fun a _ => hmass_tendsto i a)
    apply le_of_tendsto hsum
    apply Filter.Eventually.of_forall
    intro n
    exact (pmf_weight_summable (sequence (subseq n) i)).sum_le_tsum s
      (fun _ _ => ENNReal.toReal_nonneg) |>.trans_eq
        (pmf_weight_tsum_one (sequence (subseq n) i))
  have hsummable (i : ι) : Summable (mass i) :=
    summable_of_sum_le (hmass_nonneg i) (hfin_le i)
  have htotal (i : ι) : (∑' a, mass i a) = 1 := by
    apply le_antisymm
    · exact (hsummable i).tsum_le_of_sum_le (hfin_le i)
    · apply le_of_forall_pos_le_add
      intro ε hε
      obtain ⟨s, hs⟩ := htight i ε hε
      have hsum : Filter.Tendsto
          (fun n => ∑ a ∈ s, (sequence (subseq n) i a).toReal)
          Filter.atTop (nhds (∑ a ∈ s, mass i a)) :=
        tendsto_finsetSum s (fun a _ => hmass_tendsto i a)
      have hlow : 1 - ε ≤ ∑ a ∈ s, mass i a :=
        ge_of_tendsto hsum (Filter.Eventually.of_forall fun n => hs (subseq n))
      have hle := (hsummable i).sum_le_tsum s
        (fun _ _ => hmass_nonneg i _)
      linarith
  let target (i : ι) : PMF (A i) :=
    ⟨fun a => ENNReal.ofReal (mass i a), ENNReal.summable.hasSum_iff.2 (by
      rw [← ENNReal.ofReal_tsum_of_nonneg (hmass_nonneg i) (hsummable i), htotal i]
      norm_num)⟩
  refine ⟨target, subseq, hsubseq, ?_⟩
  intro i
  apply pmfConvergesPointwise_iff_toReal.mpr
  intro a
  have htarget : target i a = ENNReal.ofReal (mass i a) := rfl
  rw [htarget, ENNReal.toReal_ofReal (hmass_nonneg i a)]
  exact hmass_tendsto i a

/-- Uniform tightness extracts a probability-law limit without assuming a
countable ambient outcome type. -/
theorem exists_subseq_pmfConvergesPointwise_of_uniformlyTight
    {α : Type*} (sequence : ℕ → PMF α) (htight : UniformlyTight sequence) :
    ∃ (target : PMF α) (subseq : ℕ → ℕ),
      StrictMono subseq ∧ PMFConvergesPointwise (fun n => sequence (subseq n)) target := by
  obtain ⟨target, subseq, hsubseq, hlimit⟩ :=
    exists_subseq_pmfConvergesPointwise_pi_of_uniformlyTight
      (ι := Unit) (fun n _ => sequence n) (fun _ => htight)
  exact ⟨target (), subseq, hsubseq, hlimit ()⟩

/-- Countably many finite-carrier coordinates are automatically uniformly
tight, so they share one convergent subsequence. -/
theorem exists_subseq_pmfConvergesPointwise_pi
    {ι : Type*} [Countable ι] {A : ι → Type*} [∀ i, Finite (A i)]
    (sequence : ℕ → ∀ i, PMF (A i)) :
    ∃ (target : ∀ i, PMF (A i)) (subseq : ℕ → ℕ),
      StrictMono subseq ∧
        ∀ i, PMFConvergesPointwise (fun n => sequence (subseq n) i) (target i) := by
  exact exists_subseq_pmfConvergesPointwise_pi_of_uniformlyTight sequence
    (fun i => uniformlyTight_of_finite (fun n => sequence n i))

/-- A sequence of probability laws on a finite carrier has a pointwise
convergent subsequence whose limit is a probability law. -/
theorem exists_subseq_pmfConvergesPointwise
    {α : Type*} [Finite α] (sequence : ℕ → PMF α) :
    ∃ (target : PMF α) (subseq : ℕ → ℕ),
      StrictMono subseq ∧ PMFConvergesPointwise (fun n => sequence (subseq n)) target := by
  obtain ⟨target, subseq, hsubseq, hlimit⟩ :=
    exists_subseq_pmfConvergesPointwise_pi (ι := Unit) (fun n _ => sequence n)
  exact ⟨target (), subseq, hsubseq, hlimit ()⟩

end GameTheory.Math.Probability
