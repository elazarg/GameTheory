/-
# Statistical distance of discrete probability laws

Half the total absolute mass difference equals the largest event probability
gap. Deterministic and stochastic observations contract this distance; changing
a transition kernel costs its expected distance under the input law. Bounded
payoffs change by at most the distance times their range, and only the values
on the two laws' supports need bounds. No carrier is assumed finite.
-/

import GameTheory.Math.Probability.Bounds
import GameTheory.Math.Probability.Support

noncomputable section

namespace GameTheory.Math.Probability

universe u
variable {α : Type u}

/-- The statistical distance between two laws: half their total absolute mass
difference. -/
def statisticalDistance (μ ν : PMF α) : ℝ :=
  (∑' a, |(μ a).toReal - (ν a).toReal|) / 2

theorem summable_abs_sub_mass (μ ν : PMF α) :
    Summable fun a => |(μ a).toReal - (ν a).toReal| := by
  refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun a => ?_)
    ((pmf_weight_summable μ).add (pmf_weight_summable ν))
  refine (abs_sub _ _).trans ?_
  rw [abs_of_nonneg ENNReal.toReal_nonneg, abs_of_nonneg ENNReal.toReal_nonneg]

theorem statisticalDistance_nonneg (μ ν : PMF α) : 0 ≤ statisticalDistance μ ν :=
  div_nonneg (tsum_nonneg fun _ => abs_nonneg _) zero_le_two

/-- A test with values in `[-1, 1]` separates two laws by at most twice their
statistical distance. -/
theorem abs_expect_sub_le_statisticalDistance {μ ν : PMF α} {f : α → ℝ}
    (hf : ∀ a, |f a| ≤ 1) :
    |expect μ f - expect ν f| ≤ 2 * statisticalDistance μ ν := by
  have hμ := (payoffIntegrable_of_bounded μ f hf).summable
  have hν := (payoffIntegrable_of_bounded ν f hf).summable
  have hterm : ∀ a, ‖(μ a).toReal * f a - (ν a).toReal * f a‖ ≤
      |(μ a).toReal - (ν a).toReal| := by
    intro a
    rw [Real.norm_eq_abs, ← sub_mul, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (hf a)
  have hnorm : Summable fun a => ‖(μ a).toReal * f a - (ν a).toReal * f a‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm (summable_abs_sub_mass μ ν)
  rw [statisticalDistance, mul_div_cancel₀ _ two_ne_zero, expect, expect, ← hμ.tsum_sub hν,
    ← Real.norm_eq_abs]
  exact (norm_tsum_le_tsum_norm hnorm).trans
    (hnorm.tsum_le_tsum hterm (summable_abs_sub_mass μ ν))

/-- Statistical distance is symmetric. -/
theorem statisticalDistance_comm {α : Type u} (μ ν : PMF α) :
    statisticalDistance μ ν = statisticalDistance ν μ := by
  unfold statisticalDistance
  congr 1
  exact tsum_congr fun a => abs_sub_comm _ _

/-- The event where the first law has greater mass realizes statistical distance. -/
theorem statisticalDistance_eq_positive_event {α : Type*} (μ ν : PMF α) :
    statisticalDistance μ ν =
      (μ.toOuterMeasure {a | (ν a).toReal < (μ a).toReal}).toReal -
        (ν.toOuterMeasure {a | (ν a).toReal < (μ a).toReal}).toReal := by
  classical
  let event : Set α := {a | (ν a).toReal < (μ a).toReal}
  let difference : α → ℝ := fun a => (μ a).toReal - (ν a).toReal
  have summable := (pmf_weight_summable μ).sub (pmf_weight_summable ν)
  have left := summable.indicator event
  have right := summable.indicator eventᶜ
  have zero : ∑' a, difference a = 0 := by
    rw [(pmf_weight_summable μ).tsum_sub (pmf_weight_summable ν),
      pmf_weight_tsum_one, pmf_weight_tsum_one, sub_self]
  have split : (∑' a, event.indicator difference a) +
      (∑' a, eventᶜ.indicator difference a) = 0 := by
    rw [← left.tsum_add right]
    convert zero using 1
    apply tsum_congr
    intro a
    by_cases member : a ∈ event <;> simp [Set.indicator, member, difference]
  have absolute : (∑' a, |difference a|) =
      (∑' a, event.indicator difference a) -
        (∑' a, eventᶜ.indicator difference a) := by
    rw [← left.tsum_sub right]
    apply tsum_congr
    intro a
    by_cases member : a ∈ event
    · have positive : 0 < difference a := sub_pos.mpr member
      simp only [Set.indicator, member, Set.mem_compl_iff, not_true_eq_false, ↓reduceIte, sub_zero, abs_of_pos positive]
      rfl
    · have negative : difference a ≤ 0 := sub_nonpos.mpr (le_of_not_gt member)
      simp only [Set.indicator, member, Set.mem_compl_iff, not_false_eq_true, ↓reduceIte, zero_sub, abs_of_nonpos negative]
      rfl
  have massDifference : (∑' a, event.indicator difference a) =
      (μ.toOuterMeasure event).toReal - (ν.toOuterMeasure event).toReal := by
    rw [← expect_indicator μ event, ← expect_indicator ν event, expect, expect,
      ← (payoffIntegrable_of_bounded μ (fun a => if a ∈ event then (1 : ℝ) else 0)
        (C := 1) (fun a => by split <;> norm_num)).summable.tsum_sub
        (payoffIntegrable_of_bounded ν (fun a => if a ∈ event then (1 : ℝ) else 0)
          (C := 1) (fun a => by split <;> norm_num)).summable]
    apply tsum_congr
    intro a
    by_cases member : a ∈ event <;> simp [Set.indicator, difference, member]
  change (∑' a, |difference a|) / 2 = _
  rw [absolute, ← massDifference]
  linarith

/-- Every event gap is at most statistical distance, with the sharp coefficient one. -/
theorem abs_event_mass_sub_le_statisticalDistance {α : Type*} (μ ν : PMF α) (event : Set α) :
    |(μ.toOuterMeasure event).toReal - (ν.toOuterMeasure event).toReal| ≤
      statisticalDistance μ ν := by
  classical
  let indicator : α → ℝ := fun a => if a ∈ event then 1 else 0
  let signed : α → ℝ := fun a => if a ∈ event then 1 else -1
  have integrable (law : PMF α) : PayoffIntegrable law indicator :=
    payoffIntegrable_of_bounded law indicator (C := 1) fun a => by
      by_cases member : a ∈ event <;> simp [indicator, member]
  have value (law : PMF α) : expect law signed =
      2 * (law.toOuterMeasure event).toReal - 1 := by
    have same : signed = fun a => 2 * indicator a - 1 := by
      funext a
      by_cases member : a ∈ event <;> norm_num [signed, indicator, member]
    rw [same, expect_sub (payoffIntegrable_const_mul (integrable law))
      (payoffIntegrable_constant law 1), expect_const_mul, expect_constant]
    rw [show expect law indicator = (law.toOuterMeasure event).toReal from
      expect_indicator law event]
  have bound := abs_expect_sub_le_statisticalDistance (μ := μ) (ν := ν)
    (f := signed) (fun a => by by_cases member : a ∈ event <;> simp [signed, member])
  rw [value μ, value ν] at bound
  have same : 2 * (μ.toOuterMeasure event).toReal - 1 -
      (2 * (ν.toOuterMeasure event).toReal - 1) =
        2 * ((μ.toOuterMeasure event).toReal - (ν.toOuterMeasure event).toReal) := by ring
  rw [same, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at bound
  linarith


/-- The existing half-L1 distance is precisely the uniform event-gap bound. -/
theorem statisticalDistance_le_iff {α : Type*} (μ ν : PMF α) (error : ℝ) :
    statisticalDistance μ ν ≤ error ↔
      ∀ event : Set α,
        |(μ.toOuterMeasure event).toReal - (ν.toOuterMeasure event).toReal| ≤ error := by
  constructor
  · intro bound event
    exact (abs_event_mass_sub_le_statisticalDistance μ ν event).trans bound
  · intro bound
    rw [statisticalDistance_eq_positive_event]
    exact (le_abs_self _).trans (bound _)


/-- An atom's probability changes by at most statistical distance. -/
theorem abs_mass_sub_le_statisticalDistance {α : Type*} (μ ν : PMF α) (a : α) :
    |(μ a).toReal - (ν a).toReal| ≤ statisticalDistance μ ν := by
  simpa only [PMF.toOuterMeasure_apply_singleton] using
    abs_event_mass_sub_le_statisticalDistance μ ν {a}

/-- Statistical distance vanishes precisely for equal laws. -/
theorem statisticalDistance_eq_zero_iff {α : Type*} (μ ν : PMF α) :
    statisticalDistance μ ν = 0 ↔ μ = ν := by
  constructor
  · intro zero
    ext a
    have bound := abs_mass_sub_le_statisticalDistance μ ν a
    rw [zero] at bound
    have equal := abs_nonpos_iff.mp bound
    exact (ENNReal.toReal_eq_toReal_iff' (μ.apply_ne_top a) (ν.apply_ne_top a)).mp
      (sub_eq_zero.mp equal)
  · rintro rfl
    simp [statisticalDistance]

/-- Deterministic observations cannot increase statistical distance. -/
theorem statisticalDistance_map_le {α β : Type*} (μ ν : PMF α) (f : α → β) :
    statisticalDistance (μ.map f) (ν.map f) ≤ statisticalDistance μ ν := by
  apply (statisticalDistance_le_iff _ _ _).mpr
  intro event
  simpa only [PMF.toOuterMeasure_map_apply] using
    abs_event_mass_sub_le_statisticalDistance μ ν (f ⁻¹' event)


/-- Tests valued in the unit interval have the sharp statistical-distance bound. -/
theorem abs_expect_sub_le_statisticalDistance_of_mem_Icc {α : Type*}
    (μ ν : PMF α) (f : α → ℝ) (bounded : ∀ a, 0 ≤ f a ∧ f a ≤ 1) :
    |expect μ f - expect ν f| ≤ statisticalDistance μ ν := by
  have integrable (law : PMF α) : PayoffIntegrable law f :=
    payoffIntegrable_of_bounded law f (C := 1) fun a => by
      rw [abs_of_nonneg (bounded a).1]
      exact (bounded a).2
  have value (law : PMF α) : expect law (fun a => 2 * f a - 1) =
      2 * expect law f - 1 := by
    rw [expect_sub (payoffIntegrable_const_mul (integrable law))
      (payoffIntegrable_constant law 1), expect_const_mul, expect_constant]
  have bound := abs_expect_sub_le_statisticalDistance (μ := μ) (ν := ν)
    (f := fun a => 2 * f a - 1) (fun a => by rw [abs_le]; constructor <;> linarith [(bounded a).1, (bounded a).2])
  rw [value μ, value ν] at bound
  have same : 2 * expect μ f - 1 - (2 * expect ν f - 1) =
      2 * (expect μ f - expect ν f) := by ring
  rw [same, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at bound
  linarith


/-- Payoff differences are bounded by statistical distance times payoff range. -/
theorem abs_expect_sub_le_statisticalDistance_mul_range {α : Type*}
    (μ ν : PMF α) (f : α → ℝ) (low range : ℝ)
    (bounded : ∀ a, a ∈ μ.support ∨ a ∈ ν.support → low ≤ f a ∧ f a ≤ low + range) :
    |expect μ f - expect ν f| ≤ statisticalDistance μ ν * range := by
  obtain ⟨a, used⟩ := μ.support_nonempty
  have nonnegative : 0 ≤ range := by linarith [(bounded a (Or.inl used)).1, (bounded a (Or.inl used)).2]
  by_cases zero : range = 0
  · have value (law : PMF α) (within : ∀ a ∈ law.support, a ∈ μ.support ∨ a ∈ ν.support) :
        expect law f = low := by
      calc
        expect law f = expect law (fun _ => low) := expect_congr_on_support fun a used => by
          have interval := bounded a (within a used)
          rw [zero, add_zero] at interval
          exact le_antisymm interval.2 interval.1
        _ = low := expect_constant _ _
    rw [value μ (fun _ used => Or.inl used), value ν (fun _ used => Or.inr used),
      sub_self, abs_zero, zero, mul_zero]
  · have positive : 0 < range := lt_of_le_of_ne nonnegative (Ne.symm zero)
    let clipped : α → ℝ := fun a => max 0 (min 1 ((f a - low) / range))
    have clipBounds (a : α) : 0 ≤ clipped a ∧ clipped a ≤ 1 :=
      ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
    have clipIntegrable (law : PMF α) : PayoffIntegrable law clipped :=
      payoffIntegrable_of_bounded law clipped (C := 1) fun a => by
        rw [abs_of_nonneg (clipBounds a).1]
        exact (clipBounds a).2
    have value (law : PMF α) (within : ∀ a ∈ law.support, a ∈ μ.support ∨ a ∈ ν.support) :
        expect law f = low + range * expect law clipped := by
      calc
        expect law f = expect law (fun a => low + range * clipped a) :=
          expect_congr_on_support fun a used => by
            obtain ⟨lower, upper⟩ := bounded a (within a used)
            have nonnegative : 0 ≤ (f a - low) / range := div_nonneg (sub_nonneg.mpr lower) positive.le
            have atMostOne : (f a - low) / range ≤ 1 := (div_le_one positive).mpr (by linarith)
            rw [show clipped a = (f a - low) / range from by
              simp only [clipped, min_eq_right atMostOne, max_eq_right nonnegative],
              mul_div_cancel₀ _ zero]
            ring
        _ = low + range * expect law clipped := by
          rw [expect_add (payoffIntegrable_constant law low)
            (payoffIntegrable_const_mul (clipIntegrable law)), expect_constant, expect_const_mul]
    rw [value μ (fun _ used => Or.inl used), value ν (fun _ used => Or.inr used)]
    have same : low + range * expect μ clipped - (low + range * expect ν clipped) =
        range * (expect μ clipped - expect ν clipped) := by ring
    rw [same, abs_mul, abs_of_pos positive]
    exact (mul_le_mul_of_nonneg_left
      (abs_expect_sub_le_statisticalDistance_of_mem_Icc μ ν clipped clipBounds) positive.le).trans_eq (mul_comm ..)


/-- A common stochastic observation cannot increase statistical distance. -/
theorem statisticalDistance_bind_left_le {α β : Type*}
    (μ ν : PMF α) (kernel : α → PMF β) :
    statisticalDistance (μ.bind kernel) (ν.bind kernel) ≤ statisticalDistance μ ν := by
  apply (statisticalDistance_le_iff _ _ _).mpr
  intro event
  rw [toReal_toOuterMeasure_bind, toReal_toOuterMeasure_bind]
  apply abs_expect_sub_le_statisticalDistance_of_mem_Icc
  intro a
  exact ⟨ENNReal.toReal_nonneg, ENNReal.toReal_le_of_le_ofReal zero_le_one
    (by simpa using outerMeasure_le_one (kernel a) event)⟩


/-- Probability laws have statistical distance at most one. -/
theorem statisticalDistance_le_one {α : Type*} (μ ν : PMF α) :
    statisticalDistance μ ν ≤ 1 := by
  apply (statisticalDistance_le_iff _ _ _).mpr
  intro event
  have upper (law : PMF α) : (law.toOuterMeasure event).toReal ≤ 1 :=
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using outerMeasure_le_one law event)
  rw [abs_le]
  constructor <;> linarith [upper μ, upper ν, ENNReal.toReal_nonneg (a := μ.toOuterMeasure event),
    ENNReal.toReal_nonneg (a := ν.toOuterMeasure event)]

/-- Statistical distance is the normalization mass missing from the overlap. -/
theorem statisticalDistance_eq_one_sub_overlap {α : Type*} (μ ν : PMF α) :
    statisticalDistance μ ν = 1 - ∑' a, min ((μ a).toReal) ((ν a).toReal) := by
  have overlap : Summable fun a => min ((μ a).toReal) ((ν a).toReal) :=
    Summable.of_nonneg_of_le (fun a => le_min ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
      (fun a => min_le_left _ _) (pmf_weight_summable μ)
  have sum : (∑' a, |(μ a).toReal - (ν a).toReal|) =
      2 - 2 * ∑' a, min ((μ a).toReal) ((ν a).toReal) := by
    calc
      _ = (∑' a, ((μ a).toReal + (ν a).toReal -
          2 * min ((μ a).toReal) ((ν a).toReal))) := by
        apply tsum_congr
        intro a
        rcases le_total ((μ a).toReal) ((ν a).toReal) with ordered | ordered
        · rw [min_eq_left ordered, abs_of_nonpos (sub_nonpos.mpr ordered)]
          ring
        · rw [min_eq_right ordered, abs_of_nonneg (sub_nonneg.mpr ordered)]
          ring
      _ = _ := by
        rw [((pmf_weight_summable μ).add (pmf_weight_summable ν)).tsum_sub
          (overlap.mul_left 2), (pmf_weight_summable μ).tsum_add (pmf_weight_summable ν),
          pmf_weight_tsum_one, pmf_weight_tsum_one, tsum_mul_left]
        norm_num
  rw [statisticalDistance, sum]
  ring

/-- Statistical distance satisfies the triangle inequality. -/
theorem statisticalDistance_triangle {α : Type*} (μ ν ρ : PMF α) :
    statisticalDistance μ ρ ≤ statisticalDistance μ ν + statisticalDistance ν ρ := by
  apply (statisticalDistance_le_iff _ _ _).mpr
  intro event
  exact (abs_sub_le _ _ _).trans (add_le_add
    (abs_event_mass_sub_le_statisticalDistance μ ν event)
    (abs_event_mass_sub_le_statisticalDistance ν ρ event))

/-- Changing a kernel costs its expected statistical distance under the input law. -/
theorem statisticalDistance_bind_right_le {α β : Type*}
    (μ : PMF α) (first second : α → PMF β) :
    statisticalDistance (μ.bind first) (μ.bind second) ≤
      expect μ (fun a => statisticalDistance (first a) (second a)) := by
  apply (statisticalDistance_le_iff _ _ _).mpr
  intro event
  let f : α → ℝ := fun a => (first a |>.toOuterMeasure event).toReal
  let g : α → ℝ := fun a => (second a |>.toOuterMeasure event).toReal
  let error : α → ℝ := fun a => statisticalDistance (first a) (second a)
  have bounded (law : PMF β) : |(law.toOuterMeasure event).toReal| ≤ 1 := by
    rw [abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using outerMeasure_le_one law event)
  have fi : PayoffIntegrable μ f := payoffIntegrable_of_bounded μ f fun a => bounded (first a)
  have gi : PayoffIntegrable μ g := payoffIntegrable_of_bounded μ g fun a => bounded (second a)
  have ei : PayoffIntegrable μ error := payoffIntegrable_of_bounded μ error fun a => by
    rw [abs_of_nonneg (statisticalDistance_nonneg ..)]
    exact statisticalDistance_le_one ..
  rw [toReal_toOuterMeasure_bind, toReal_toOuterMeasure_bind, abs_le]
  constructor
  · have bound := expect_mono (μ := μ) (f := fun a => -(f a - g a))
      (g := error) (fun a _ => by
        have bound := (abs_le.mp
          (abs_event_mass_sub_le_statisticalDistance (first a) (second a) event)).1
        change -error a ≤ f a - g a at bound
        linarith)
      (payoffIntegrable_neg (payoffIntegrable_sub fi gi)) ei
    rw [expect_neg, expect_sub fi gi] at bound
    change -expect μ error ≤ expect μ f - expect μ g
    linarith
  · have bound := expect_mono (μ := μ) (f := fun a => f a - g a)
      (g := error) (fun a _ => (le_abs_self _).trans
        (abs_event_mass_sub_le_statisticalDistance (first a) (second a) event))
      (payoffIntegrable_sub fi gi) ei
    rw [expect_sub fi gi] at bound
    exact bound

/-- Input-law error and expected kernel error add under sequential sampling. -/
theorem statisticalDistance_bind_le {α β : Type*}
    (μ ν : PMF α) (first second : α → PMF β) :
    statisticalDistance (μ.bind first) (ν.bind second) ≤ statisticalDistance μ ν +
      expect ν (fun a => statisticalDistance (first a) (second a)) :=
  (statisticalDistance_triangle _ _ _).trans (add_le_add
    (statisticalDistance_bind_left_le μ ν first)
    (statisticalDistance_bind_right_le ν first second))

/-- A uniform support-local kernel error gives a uniform output error. -/
theorem statisticalDistance_bind_right_le_of_bound {α β : Type*}
    (μ : PMF α) (first second : α → PMF β) (error : ℝ)
    (bounded : ∀ a ∈ μ.support, statisticalDistance (first a) (second a) ≤ error) :
    statisticalDistance (μ.bind first) (μ.bind second) ≤ error := by
  refine (statisticalDistance_bind_right_le μ first second).trans ?_
  calc
    expect μ (fun a => statisticalDistance (first a) (second a)) ≤
        expect μ (fun _ => error) := expect_mono bounded
          (payoffIntegrable_of_bounded μ _ fun a => by
            rw [abs_of_nonneg (statisticalDistance_nonneg ..)]
            exact statisticalDistance_le_one ..)
          (payoffIntegrable_constant μ error)
    _ = error := expect_constant _ _


/-- Distance from a point mass is precisely the probability assigned elsewhere. -/
theorem statisticalDistance_pure_eq_one_sub_mass {α : Type*} (law : PMF α) (a : α) :
    statisticalDistance law (PMF.pure a) = 1 - (law a).toReal := by
  classical
  rw [statisticalDistance_eq_one_sub_overlap]
  congr 1
  rw [tsum_eq_single a]
  · rw [PMF.pure_apply_self, ENNReal.toReal_one]
    exact min_eq_left (pmf_toReal_apply_le_one law a)
  · intro b different
    rw [PMF.pure_apply_of_ne _ _ different, ENNReal.toReal_zero]
    exact min_eq_right ENNReal.toReal_nonneg

open Classical in
/-- The statistical distance of a law from a point mass is the mass it puts elsewhere. -/
theorem statisticalDistance_pure (μ : PMF α) (a : α) :
    statisticalDistance μ (PMF.pure a) = expect μ fun x => if x = a then 0 else 1 := by
  classical
  have complement : (fun x => if x = a then (0 : ℝ) else 1) =
      (fun x => (1 : ℝ) - if a = x then 1 else 0) := by
    funext x
    by_cases same : x = a
    · subst x; simp
    · simp [same, Ne.symm same]
  have atom : expect μ (fun x => if a = x then (1 : ℝ) else 0) = (μ a).toReal := by
    simpa only [Set.mem_singleton_iff, eq_comm, PMF.toOuterMeasure_apply_singleton] using
      expect_indicator μ {a}
  rw [statisticalDistance_pure_eq_one_sub_mass, complement,
    expect_sub (payoffIntegrable_constant μ 1)
      (payoffIntegrable_of_bounded μ _ (C := 1) fun x => by split <;> norm_num),
    expect_constant, atom]

/-- A lottery is close to a branch whenever it chooses that branch with high probability. -/
theorem statisticalDistance_bind_point_le {α β : Type*} (mixing : PMF α) (a : α)
    (branch : α → PMF β) :
    statisticalDistance (mixing.bind branch) (branch a) ≤ 1 - (mixing a).toReal := by
  simpa only [PMF.pure_bind, statisticalDistance_pure_eq_one_sub_mass] using
    statisticalDistance_bind_left_le mixing (PMF.pure a) branch


end GameTheory.Math.Probability
