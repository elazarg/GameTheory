/-
# Comparing empirical means

Two real laws are compared by drawing equally many independent samples from
each and asking which sample sum — equivalently, which empirical mean — is
larger. `meanComparisonGap X Y m` is how much more often the `m`-sample mean of
`Y` reaches that of `X` than the reverse. A small gap says that `m` samples do
not make `Y` look better than `X`.

*Empirical mean dominance* bounds the gap at one sample size. *Computational
mean dominance* compares ensembles indexed by a size parameter `κ`: for every
inverse-polynomial tolerance there is a polynomial sample size at which the gap
eventually falls below it. Events of negligible probability are then invisible,
however large the values they carry.

Computational mean dominance cannot tell apart ensembles that the comparison of
empirical means itself cannot distinguish (`MeanTestIndistinguishable`), so
replacing either side by such an ensemble preserves it, and such ensembles
dominate each other. The indistinguishability hypothesis names exactly one
test, not a class of efficient algorithms: a computational model enters only in
showing that this test is admissible.

Primary reference: A. Psomas, A. Terzoglou, Y. Wei, and V. Zikas,
“Pseudo-Equilibria, or: How to Stop Worrying About Crypto and Just Analyze the
Game,” arXiv:2506.22089 (2025).
-/
import GameTheory.Math.Probability.SampleSumEvents
import GameTheory.Math.Negligible
import Mathlib.Basic.Real.Sign

noncomputable section

namespace GameTheory.Math.Probability

open Filter
open GameTheory.Math

/-- The joint law of the sums of `m` independent draws from each of two laws. -/
def sampleSumPair (X Y : PMF ℝ) (m : ℕ) : PMF (ℝ × ℝ) :=
  (sampleSum X m).bind fun s => (sampleSum Y m).map fun t => (s, t)

/-- `Pr[ΣY ≥ ΣX] - Pr[ΣX ≥ ΣY]` for `m` independent draws of each law: how much
more often the empirical mean of `Y` reaches that of `X` than the reverse. -/
def meanComparisonGap (X Y : PMF ℝ) (m : ℕ) : ℝ :=
  ((sampleSumPair X Y m).toOuterMeasure {p | p.1 ≤ p.2}).toReal -
    ((sampleSumPair X Y m).toOuterMeasure {p | p.2 ≤ p.1}).toReal

/-- `X` `(m, δ)`-empirically mean-dominates `Y`: with `m` samples of each, the
mean of `Y` reaches that of `X` at most `δ` more often than the reverse. -/
def EmpiricalMeanDominates (m : ℕ) (δ : ℝ) (X Y : PMF ℝ) : Prop :=
  meanComparisonGap X Y m ≤ δ

/-- The ensemble `X` computationally mean-dominates `Y`: for every exponent `c`
some polynomial sample size `κ ^ d` with `d > c` eventually brings the gap
below `κ ^ (-c)`. -/
def ComputationallyMeanDominates (X Y : ℕ → PMF ℝ) : Prop :=
  ∀ c : ℕ, 1 ≤ c → ∃ d : ℕ, c < d ∧
    ∀ᶠ κ : ℕ in atTop, meanComparisonGap (X κ) (Y κ) (κ ^ d) < ((κ : ℝ) ^ c)⁻¹

/-- The law of `X - Y` for independent `X ∼ μ` and `Y ∼ ν`. -/
def differenceLaw (μ ν : PMF ℝ) : PMF ℝ :=
  addLaw μ (ν.map Neg.neg)

/-- `Pr[ΣX > ΣY]` for `m` independent draws of each law: how often the mean
test declares `X` ahead of the reference `Y`. -/
def aheadProb (X Y : PMF ℝ) (m : ℕ) : ℝ :=
  ((sampleSumPair X Y m).toOuterMeasure {p | p.2 < p.1}).toReal

theorem sampleSumPair_map_sub (X Y : PMF ℝ) (m : ℕ) :
    (sampleSumPair X Y m).map (fun p => p.1 - p.2) =
      sampleSum (differenceLaw X Y) m := by
  rw [differenceLaw, sampleSum_addLaw, sampleSum_map_neg, sampleSumPair, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def, addLaw, sub_eq_add_neg]

theorem differenceLaw_swap (X Y : PMF ℝ) :
    differenceLaw Y X = (differenceLaw X Y).map Neg.neg := by
  rw [differenceLaw, differenceLaw, ← addLaw_map_neg, PMF.map_comp]
  simp only [Function.comp_def, neg_neg]
  rw [show (fun x : ℝ => x) = id from rfl, PMF.map_id]
  exact addLaw_comm _ _

open Classical in
private theorem pair_prob_eq (X Y : PMF ℝ) (m : ℕ) (event : Set ℝ) :
    ((sampleSumPair X Y m).toOuterMeasure ((fun p => p.1 - p.2) ⁻¹' event)).toReal =
      expect (sampleSum (differenceLaw X Y) m)
        (fun d => if d ∈ event then (1 : ℝ) else 0) := by
  classical
  rw [← PMF.toOuterMeasure_map_apply, sampleSumPair_map_sub, expect_indicator]

theorem aheadProb_eq (X Y : PMF ℝ) (m : ℕ) :
    aheadProb X Y m =
      expect (sampleSum (differenceLaw X Y) m) (fun d => if 0 < d then (1 : ℝ) else 0) := by
  have hset : {p : ℝ × ℝ | p.2 < p.1} = (fun p => p.1 - p.2) ⁻¹' {d | 0 < d} := by
    ext p
    simp [sub_pos]
  rw [aheadProb, hset, pair_prob_eq]
  rfl

/-- The gap is the expected sign of `ΣY - ΣX`. -/
theorem meanComparisonGap_eq_neg_expect_sign (X Y : PMF ℝ) (m : ℕ) :
    meanComparisonGap X Y m = -expect (sampleSum (differenceLaw X Y) m) Real.sign := by
  classical
  have hle : {p : ℝ × ℝ | p.1 ≤ p.2} = (fun p => p.1 - p.2) ⁻¹' {d | d ≤ 0} := by
    ext p
    simp
  have hge : {p : ℝ × ℝ | p.2 ≤ p.1} = (fun p => p.1 - p.2) ⁻¹' {d | 0 ≤ d} := by
    ext p
    simp [sub_nonneg]
  rw [meanComparisonGap, hle, hge, pair_prob_eq, pair_prob_eq,
    ← expect_sub (payoffIntegrable_of_bounded _ _ (C := 1) fun _ => abs_indicator_le _)
      (payoffIntegrable_of_bounded _ _ (C := 1) fun _ => abs_indicator_le _),
    ← expect_neg]
  apply expect_congr_on_support
  intro d _
  rcases lt_trichotomy d 0 with hd | hd | hd
  · simp [hd.le, not_le.mpr hd, Real.sign_of_neg hd]
  · simp [hd]
  · simp [hd.le, not_le.mpr hd, Real.sign_of_pos hd]

/-- The gap is the difference of the two ahead probabilities. -/
theorem meanComparisonGap_eq_aheadProb_sub (X Y : PMF ℝ) (m : ℕ) :
    meanComparisonGap X Y m = aheadProb Y X m - aheadProb X Y m := by
  set law := sampleSum (differenceLaw X Y) m
  have hbehind : PayoffIntegrable law
      ((fun d : ℝ => if 0 < d then (1 : ℝ) else 0) ∘ Neg.neg) :=
    payoffIntegrable_of_bounded _ _ (C := 1) fun _ => abs_indicator_le _
  have hahead : PayoffIntegrable law (fun d : ℝ => if 0 < d then (1 : ℝ) else 0) :=
    payoffIntegrable_of_bounded _ _ (C := 1) fun _ => abs_indicator_le _
  rw [meanComparisonGap_eq_neg_expect_sign, aheadProb_eq, aheadProb_eq, differenceLaw_swap X Y,
    sampleSum_map_neg, expect_map, ← expect_sub hbehind hahead, ← expect_neg]
  apply expect_congr_on_support
  intro d _
  rcases lt_trichotomy d 0 with hd | hd | hd
  · simp [hd, not_lt.mpr hd.le, Real.sign_of_neg hd]
  · simp [hd]
  · simp [hd, not_lt.mpr hd.le, Real.sign_of_pos hd]

@[simp]
theorem meanComparisonGap_self (X : PMF ℝ) (m : ℕ) : meanComparisonGap X X m = 0 := by
  rw [meanComparisonGap_eq_aheadProb_sub, sub_self]

/-! ## Invariance under mean-test indistinguishability -/

/-- `X` and `X'` cannot be told apart by comparing their empirical mean with
that of the reference `Y`: at every polynomial sample size `κ ^ d`, both the
probability of beating the reference and the probability of being beaten by it
change negligibly. This is the advantage of the one test the dominance
comparison performs. -/
def MeanTestIndistinguishable (Y X X' : ℕ → PMF ℝ) : Prop :=
  ∀ d : ℕ,
    Negligible (fun κ => aheadProb (X κ) (Y κ) (κ ^ d) - aheadProb (X' κ) (Y κ) (κ ^ d)) ∧
      Negligible (fun κ => aheadProb (Y κ) (X κ) (κ ^ d) - aheadProb (Y κ) (X' κ) (κ ^ d))

theorem MeanTestIndistinguishable.symm {Y X X' : ℕ → PMF ℝ}
    (h : MeanTestIndistinguishable Y X X') : MeanTestIndistinguishable Y X' X := by
  intro d
  obtain ⟨h₁, h₂⟩ := h d
  exact ⟨by simpa using h₁.neg, by simpa using h₂.neg⟩

theorem meanTestIndistinguishable_refl (Y X : ℕ → PMF ℝ) :
    MeanTestIndistinguishable Y X X := by
  intro d
  exact ⟨by simpa using negligible_zero, by simpa using negligible_zero⟩

/-- Dominance transfers between gap functions that differ negligibly at every
polynomial sample size. -/
private theorem computationallyMeanDominates_of_gap_close {X Y X' Y' : ℕ → PMF ℝ}
    (hclose : ∀ d : ℕ, Negligible (fun κ =>
      meanComparisonGap (X' κ) (Y' κ) (κ ^ d) - meanComparisonGap (X κ) (Y κ) (κ ^ d)))
    (h : ComputationallyMeanDominates X Y) : ComputationallyMeanDominates X' Y' := by
  intro c hc
  obtain ⟨d, hcd, hev⟩ := h (c + 1) (by omega)
  refine ⟨d, by omega, ?_⟩
  filter_upwards [hev, (hclose d).eventually_abs_lt (c + 1), eventually_ge_atTop 2]
    with κ hgap hdiff hκ
  have hκpos : (0 : ℝ) < κ := by exact_mod_cast (show 0 < κ by omega)
  have h2 : 2 * (κ : ℝ)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hκpos]
    exact_mod_cast hκ
  have hbound : 2 * ((κ : ℝ) ^ (c + 1))⁻¹ ≤ ((κ : ℝ) ^ c)⁻¹ :=
    calc
      2 * ((κ : ℝ) ^ (c + 1))⁻¹ = (2 * (κ : ℝ)⁻¹) * ((κ : ℝ) ^ c)⁻¹ := by
        rw [pow_succ, mul_inv]
        ring
      _ ≤ 1 * ((κ : ℝ) ^ c)⁻¹ := mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = ((κ : ℝ) ^ c)⁻¹ := one_mul _
  have := (abs_lt.mp hdiff).2
  linarith

/-- Replacing the dominating ensemble by one the mean test against `Y` cannot
distinguish preserves dominance of `Y`. -/
theorem ComputationallyMeanDominates.congr_left {X X' Y : ℕ → PMF ℝ}
    (hX : MeanTestIndistinguishable Y X X') :
    ComputationallyMeanDominates X Y ↔ ComputationallyMeanDominates X' Y := by
  have transfer : ∀ {A A' : ℕ → PMF ℝ}, MeanTestIndistinguishable Y A A' →
      ComputationallyMeanDominates A Y → ComputationallyMeanDominates A' Y := by
    intro A A' hA hdom
    refine computationallyMeanDominates_of_gap_close (fun d => ?_) hdom
    obtain ⟨hbeat, hbeaten⟩ := hA d
    refine (hbeat.sub hbeaten).congr fun κ => ?_
    simp only [meanComparisonGap_eq_aheadProb_sub]
    ring
  exact ⟨transfer hX, transfer hX.symm⟩

/-- Replacing the dominated ensemble by one the mean test against `X` cannot
distinguish preserves dominance by `X`. -/
theorem ComputationallyMeanDominates.congr_right {X Y Y' : ℕ → PMF ℝ}
    (hY : MeanTestIndistinguishable X Y Y') :
    ComputationallyMeanDominates X Y ↔ ComputationallyMeanDominates X Y' := by
  have transfer : ∀ {B B' : ℕ → PMF ℝ}, MeanTestIndistinguishable X B B' →
      ComputationallyMeanDominates X B → ComputationallyMeanDominates X B' := by
    intro B B' hB hdom
    refine computationallyMeanDominates_of_gap_close (fun d => ?_) hdom
    obtain ⟨hbeat, hbeaten⟩ := hB d
    refine (hbeaten.sub hbeat).congr fun κ => ?_
    simp only [meanComparisonGap_eq_aheadProb_sub]
    ring
  exact ⟨transfer hY, transfer hY.symm⟩

theorem computationallyMeanDominates_refl (X : ℕ → PMF ℝ) :
    ComputationallyMeanDominates X X := by
  intro c _
  refine ⟨c + 1, by omega, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with κ hκ
  rw [meanComparisonGap_self]
  have : (0 : ℝ) < κ := by exact_mod_cast hκ
  positivity

/-- Ensembles that the mean test against `X` cannot distinguish dominate each
other. -/
theorem computationallyMeanDominates_of_meanTestIndistinguishable {X Y : ℕ → PMF ℝ}
    (h : MeanTestIndistinguishable X X Y) :
    ComputationallyMeanDominates X Y ∧ ComputationallyMeanDominates Y X :=
  ⟨(ComputationallyMeanDominates.congr_right h).mp (computationallyMeanDominates_refl X),
    (ComputationallyMeanDominates.congr_left h).mp (computationallyMeanDominates_refl X)⟩

end GameTheory.Math.Probability
