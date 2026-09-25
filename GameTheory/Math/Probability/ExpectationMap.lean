import GameTheory.Math.Probability.Expectation

noncomputable section

open scoped BigOperators

namespace GameTheory.Math.Probability

/-- The ENNReal weighted mass sum commutes with PMF pushforward. -/
theorem tsum_map_mul {α β : Type*} (f : α → β) (p : PMF α)
    (v : β → ENNReal) :
    ∑' b, (PMF.map f p) b * v b = ∑' a, p a * v (f a) := by
  simp_rw [PMF.map_apply, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun a => ?_
  rw [tsum_eq_single (f a) (fun b hb => by simp [hb])]
  simp

private theorem summable_toReal_iff {α : Type*} (H : α → ENNReal)
    (hH : ∀ a, H a ≠ ⊤) : Summable (fun a => (H a).toReal) ↔
      (∑' a, H a) ≠ ⊤ := by
  constructor
  · intro hs
    rw [show (∑' a, H a) = ∑' a, ENNReal.ofReal ((H a).toReal) from
      tsum_congr fun a => (ENNReal.ofReal_toReal (hH a)).symm]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => ENNReal.toReal_nonneg) hs]
    exact ENNReal.ofReal_ne_top
  · exact fun hne => ENNReal.summable_toReal hne

/-- Nonnegative real summability transfers exactly across a PMF map. -/
theorem summable_map_mul_iff_of_nonneg {α β : Type*}
    (f : α → β) (p : PMF α) (g : β → ℝ) (hg : ∀ b, 0 ≤ g b) :
    Summable (fun b => (PMF.map f p b).toReal * g b) ↔
      Summable (fun a => (p a).toReal * g (f a)) := by
  have hmap : (fun b => (PMF.map f p b).toReal * g b) =
      (fun b => (PMF.map f p b * ENNReal.ofReal (g b)).toReal) := by
    funext b
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hg b)]
  have hp : (fun a => (p a).toReal * g (f a)) =
      (fun a => (p a * ENNReal.ofReal (g (f a))).toReal) := by
    funext a
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hg (f a))]
  rw [hmap, hp,
    summable_toReal_iff (fun b => PMF.map f p b * ENNReal.ofReal (g b))
      (fun b => ENNReal.mul_ne_top (PMF.apply_ne_top _ b) ENNReal.ofReal_ne_top),
    summable_toReal_iff (fun a => p a * ENNReal.ofReal (g (f a)))
      (fun a => ENNReal.mul_ne_top (PMF.apply_ne_top _ a) ENNReal.ofReal_ne_top),
    tsum_map_mul f p (fun b => ENNReal.ofReal (g b))]

/-- Absolute weighted summability is invariant under PMF pushforward. -/
theorem payoffIntegrable_map_iff {α β : Type*} (f : α → β)
    (p : PMF α) (u : β → ℝ) :
    PayoffIntegrable (PMF.map f p) u ↔ PayoffIntegrable p (u ∘ f) := by
  simpa only [PayoffIntegrable, Function.comp_apply] using
    (summable_map_mul_iff_of_nonneg f p (fun b => |u b|)
      (fun _ => abs_nonneg _))

private theorem abs_max_pos (x : ℝ) : |max x 0| = max x 0 :=
  abs_of_nonneg (le_max_right x 0)

private theorem abs_max_neg (x : ℝ) : |max (-x) 0| = max (-x) 0 :=
  abs_of_nonneg (le_max_right (-x) 0)

private theorem payoffIntegrable_positive {α : Type*} {μ : PMF α}
    {u : α → ℝ} (h : PayoffIntegrable μ u) :
    PayoffIntegrable μ (fun a => max (u a) 0) := by
  have habs : Summable (fun a => (μ a).toReal * |u a|) := by
    simpa only [PayoffIntegrable] using h
  have hsum := Summable.of_nonneg_of_le
    (fun a => mul_nonneg ENNReal.toReal_nonneg (le_max_right _ _))
    (fun a => mul_le_mul_of_nonneg_left
      (max_le (le_abs_self _) (abs_nonneg _)) ENNReal.toReal_nonneg)
    habs
  simpa only [PayoffIntegrable, abs_max_pos] using hsum

private theorem payoffIntegrable_negative {α : Type*} {μ : PMF α}
    {u : α → ℝ} (h : PayoffIntegrable μ u) :
    PayoffIntegrable μ (fun a => max (-(u a)) 0) := by
  have habs : Summable (fun a => (μ a).toReal * |u a|) := by
    simpa only [PayoffIntegrable] using h
  have hsum := Summable.of_nonneg_of_le
    (fun a => mul_nonneg ENNReal.toReal_nonneg (le_max_right _ _))
    (fun a => mul_le_mul_of_nonneg_left
      (max_le (neg_le_abs _) (abs_nonneg _)) ENNReal.toReal_nonneg)
    habs
  simpa only [PayoffIntegrable, abs_max_neg] using hsum

private theorem expect_split {α : Type*} (μ : PMF α) (u : α → ℝ)
    (h : PayoffIntegrable μ u) :
    expect μ u h =
      expect μ (fun a => max (u a) 0) (payoffIntegrable_positive h) -
      expect μ (fun a => max (-(u a)) 0) (payoffIntegrable_negative h) := by
  have hpos := payoffIntegrable_positive h
  have hneg := payoffIntegrable_negative h
  have hposSum : Summable (fun a =>
      (μ a).toReal * max (u a) 0) := by
    simpa only [PayoffIntegrable, abs_max_pos] using hpos
  have hnegSum : Summable (fun a =>
      (μ a).toReal * max (-(u a)) 0) := by
    simpa only [PayoffIntegrable, abs_max_neg] using hneg
  simp only [expect]
  rw [← Summable.tsum_sub hposSum hnegSum]
  refine tsum_congr fun a => ?_
  rw [← mul_sub]
  congr 1
  rcases le_total 0 (u a) with hnonneg | hnonpos
  · rw [max_eq_left hnonneg, max_eq_right (by linarith), sub_zero]
  · rw [max_eq_right hnonpos, max_eq_left (by linarith),
      sub_neg_eq_add, zero_add]

private theorem expect_eq_toReal_of_nonneg {α : Type*} (μ : PMF α)
    (g : α → ℝ) (h : PayoffIntegrable μ g) (hg : ∀ a, 0 ≤ g a) :
    expect μ g h = (∑' a, μ a * ENNReal.ofReal (g a)).toReal := by
  rw [expect, ENNReal.tsum_toReal_eq
    (fun a => ENNReal.mul_ne_top (PMF.apply_ne_top μ a) ENNReal.ofReal_ne_top)]
  refine tsum_congr fun a => ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hg a)]

/-- Change variables for a nonnegative integrand under PMF pushforward. -/
theorem expect_map_of_nonneg {α β : Type*} (f : α → β)
    (p : PMF α) (u : β → ℝ) (hp : PayoffIntegrable p (u ∘ f))
    (hmap : PayoffIntegrable (PMF.map f p) u) (hu : ∀ b, 0 ≤ u b) :
    expect (PMF.map f p) u hmap = expect p (u ∘ f) hp := by
  rw [expect_eq_toReal_of_nonneg _ _ hmap hu,
    expect_eq_toReal_of_nonneg _ _ hp (fun a => hu (f a))]
  congr 1
  exact tsum_map_mul f p (fun b => ENNReal.ofReal (u b))

/-- Change variables for a guarded real expectation under a PMF map. -/
theorem expect_map {α β : Type*} (f : α → β) (p : PMF α)
    (u : β → ℝ) (hp : PayoffIntegrable p (u ∘ f))
    (hmap : PayoffIntegrable (PMF.map f p) u) :
    expect (PMF.map f p) u hmap = expect p (u ∘ f) hp := by
  calc
    expect (PMF.map f p) u hmap =
        expect (PMF.map f p) (fun b => max (u b) 0)
            (payoffIntegrable_positive hmap) -
          expect (PMF.map f p) (fun b => max (-(u b)) 0)
            (payoffIntegrable_negative hmap) :=
      expect_split (PMF.map f p) u hmap
    _ = expect p (fun a => max (u (f a)) 0)
            (payoffIntegrable_positive hp) -
          expect p (fun a => max (-(u (f a))) 0)
            (payoffIntegrable_negative hp) := by
      congr 1
      · exact expect_map_of_nonneg f p (fun b => max (u b) 0)
          (payoffIntegrable_positive hp) (payoffIntegrable_positive hmap)
          (fun _ => le_max_right _ _)
      · exact expect_map_of_nonneg f p (fun b => max (-(u b)) 0)
          (payoffIntegrable_negative hp) (payoffIntegrable_negative hmap)
          (fun _ => le_max_right _ _)
    _ = expect p (u ∘ f) hp := (expect_split p (u ∘ f) hp).symm

/-- Equal observed laws transport payoff integrability between distinct
underlying PMFs. -/
theorem payoffIntegrable_observed_law_iff {α β Observation : Type*}
    (μ : PMF α) (ν : PMF β) (f : α → Observation) (g : β → Observation)
    (value : Observation → ℝ) (hlaw : μ.map f = ν.map g) :
    PayoffIntegrable μ (value ∘ f) ↔ PayoffIntegrable ν (value ∘ g) := by
  calc
    PayoffIntegrable μ (value ∘ f) ↔ PayoffIntegrable (μ.map f) value :=
      (payoffIntegrable_map_iff f μ value).symm
    _ ↔ PayoffIntegrable (ν.map g) value := by rw [hlaw]
    _ ↔ PayoffIntegrable ν (value ∘ g) :=
      payoffIntegrable_map_iff g ν value

/-- Equal observed laws have equal guarded expectations. -/
theorem expect_observed_law_eq {α β Observation : Type*}
    (μ : PMF α) (ν : PMF β) (f : α → Observation) (g : β → Observation)
    (value : Observation → ℝ) (hlaw : μ.map f = ν.map g)
    (hμ : PayoffIntegrable μ (value ∘ f))
    (hν : PayoffIntegrable ν (value ∘ g)) :
    expect μ (value ∘ f) hμ = expect ν (value ∘ g) hν := by
  have hm : PayoffIntegrable (μ.map f) value :=
    (payoffIntegrable_map_iff f μ value).mpr hμ
  have hn : PayoffIntegrable (ν.map g) value :=
    (payoffIntegrable_map_iff g ν value).mpr hν
  calc
    expect μ (value ∘ f) hμ = expect (μ.map f) value hm :=
      (expect_map f μ value hμ hm).symm
    _ = expect (ν.map g) value hn := expect_congr_law hlaw value hm hn
    _ = expect ν (value ∘ g) hν := expect_map g ν value hν hn

end GameTheory.Math.Probability
