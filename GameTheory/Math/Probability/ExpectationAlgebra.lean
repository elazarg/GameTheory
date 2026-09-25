import GameTheory.Math.Probability.ExpectationComposition

noncomputable section

open scoped BigOperators

namespace GameTheory.Math.Probability

theorem payoffIntegrable_zero {α : Type*} (μ : PMF α) :
    PayoffIntegrable μ (fun _ => (0 : ℝ)) := by
  simp [PayoffIntegrable]

/-- Restricting an integrable payoff to an event preserves integrability. -/
theorem payoffIntegrable_indicator {α : Type*} {μ : PMF α}
    {f : α → ℝ} (event : Set α) (hf : PayoffIntegrable μ f) :
    PayoffIntegrable μ (event.indicator f) := by
  unfold PayoffIntegrable at hf ⊢
  apply Summable.of_nonneg_of_le
    (fun a => mul_nonneg ENNReal.toReal_nonneg (abs_nonneg _))
    (fun a => by
      by_cases ha : a ∈ event
      · simp [Set.indicator_of_mem ha]
      · simp [Set.indicator_of_notMem ha]
        exact mul_nonneg ENNReal.toReal_nonneg (abs_nonneg _))
    hf

theorem payoffIntegrable_neg {α : Type*} {μ : PMF α} {f : α → ℝ}
    (hf : PayoffIntegrable μ f) : PayoffIntegrable μ (fun a => -f a) := by
  simpa only [PayoffIntegrable, abs_neg] using hf

theorem payoffIntegrable_add {α : Type*} {μ : PMF α} {f g : α → ℝ}
    (hf : PayoffIntegrable μ f) (hg : PayoffIntegrable μ g) :
    PayoffIntegrable μ (fun a => f a + g a) := by
  have hsum : Summable (fun a =>
      (μ a).toReal * (|f a| + |g a|)) := by
    simpa only [PayoffIntegrable, mul_add] using hf.add hg
  have hresult : Summable (fun a =>
      (μ a).toReal * |f a + g a|) := Summable.of_nonneg_of_le
    (fun a => mul_nonneg ENNReal.toReal_nonneg (abs_nonneg _))
    (fun a => mul_le_mul_of_nonneg_left (abs_add_le _ _) ENNReal.toReal_nonneg)
    hsum
  simpa only [PayoffIntegrable] using hresult

theorem payoffIntegrable_sub {α : Type*} {μ : PMF α} {f g : α → ℝ}
    (hf : PayoffIntegrable μ f) (hg : PayoffIntegrable μ g) :
    PayoffIntegrable μ (fun a => f a - g a) := by
  simpa only [sub_eq_add_neg] using payoffIntegrable_add hf (payoffIntegrable_neg hg)

theorem payoffIntegrable_const_mul {α : Type*} {μ : PMF α}
    {c : ℝ} {f : α → ℝ} (hf : PayoffIntegrable μ f) :
    PayoffIntegrable μ (fun a => c * f a) := by
  have hsum := hf.mul_left |c|
  have hresult : Summable (fun a => (μ a).toReal * |c * f a|) := by
    apply hsum.congr
    intro a
    rw [abs_mul]
    ring
  simpa only [PayoffIntegrable] using hresult

theorem expect_zero {α : Type*} (μ : PMF α)
    (h : PayoffIntegrable μ (fun _ => (0 : ℝ))) :
    expect μ (fun _ => 0) h = 0 := by
  simp [expect]

theorem expect_neg {α : Type*} {μ : PMF α} {f : α → ℝ}
    (hf : PayoffIntegrable μ f) :
    expect μ (fun a => -f a) (payoffIntegrable_neg hf) = -expect μ f hf := by
  unfold expect
  rw [← tsum_neg]
  refine tsum_congr fun a => ?_
  ring

theorem expect_add {α : Type*} {μ : PMF α} {f g : α → ℝ}
    (hf : PayoffIntegrable μ f) (hg : PayoffIntegrable μ g) :
    expect μ (fun a => f a + g a) (payoffIntegrable_add hf hg) =
      expect μ f hf + expect μ g hg := by
  have hfs := hf.summable
  have hgs := hg.summable
  unfold expect
  rw [← Summable.tsum_add hfs hgs]
  refine tsum_congr fun a => ?_
  ring

theorem expect_sub {α : Type*} {μ : PMF α} {f g : α → ℝ}
    (hf : PayoffIntegrable μ f) (hg : PayoffIntegrable μ g) :
    expect μ (fun a => f a - g a) (payoffIntegrable_sub hf hg) =
      expect μ f hf - expect μ g hg := by
  calc
    expect μ (fun a => f a - g a) (payoffIntegrable_sub hf hg) =
        expect μ f hf + expect μ (fun a => -g a) (payoffIntegrable_neg hg) := by
          simpa only [sub_eq_add_neg] using
            expect_add hf (payoffIntegrable_neg hg)
    _ = expect μ f hf - expect μ g hg := by
      rw [expect_neg hg]
      ring

/-- If an integrable payoff is bounded above by a constant on the law's
support and its expectation reaches that constant, it equals the constant
throughout the support. -/
theorem expect_eq_const_of_le_on_support {α : Type*} (μ : PMF α) (f : α → ℝ)
    (c : ℝ) (hf : PayoffIntegrable μ f)
    (hle : ∀ a ∈ μ.support, f a ≤ c)
    (heq : expect μ f hf = c) :
    ∀ a ∈ μ.support, f a = c := by
  have hconst : PayoffIntegrable μ (fun _ => c) :=
    payoffIntegrable_of_bounded μ (fun _ => c) (C := |c|) (fun _ => le_rfl)
  have hgap : PayoffIntegrable μ (fun a => c - f a) := by
    simpa only [sub_eq_add_neg] using
      payoffIntegrable_add hconst (payoffIntegrable_neg hf)
  have hgapValue : expect μ (fun a => c - f a) hgap = 0 := by
    calc
      _ = expect μ (fun _ => c) hconst +
          expect μ (fun a => -f a) (payoffIntegrable_neg hf) := by
            simpa only [sub_eq_add_neg] using
              expect_add hconst (payoffIntegrable_neg hf)
      _ = c - expect μ f hf := by
            rw [expect_constant μ c hconst, expect_neg hf]
            ring
      _ = 0 := by rw [heq]; ring
  intro a ha
  apply le_antisymm (hle a ha)
  by_contra hnot
  have hstrict : f a < c := lt_of_not_ge hnot
  have habs : Summable (fun x => (μ x).toReal * |c - f x|) := by
    simpa only [PayoffIntegrable] using hgap
  have hnorm : Summable (fun x => ‖(μ x).toReal * (c - f x)‖) := by
    simpa [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg ENNReal.toReal_nonneg] using habs
  have hweighted := hnorm.of_norm
  have hnonneg (x : α) : 0 ≤ (μ x).toReal * (c - f x) := by
    by_cases hx : x ∈ μ.support
    · exact mul_nonneg ENNReal.toReal_nonneg (sub_nonneg.mpr (hle x hx))
    · have hzero : μ x = 0 := not_ne_iff.mp hx
      simp [hzero]
  have hmass := ENNReal.toReal_pos (μ.mem_support_iff a |>.mp ha) (μ.apply_ne_top a)
  have hterm : 0 < (μ a).toReal * (c - f a) :=
    mul_pos hmass (sub_pos.mpr hstrict)
  have hpositive := hweighted.tsum_pos hnonneg a hterm
  have hzero : ∑' x, (μ x).toReal * (c - f x) = 0 := by
    simpa only [expect] using hgapValue
  exact (ne_of_gt hpositive) hzero

/-- An integrable payoff attains an action whose value is at least its mean. -/
theorem exists_mem_support_expect_le {α : Type*} (μ : PMF α) (f : α → ℝ)
    (hf : PayoffIntegrable μ f) :
    ∃ a ∈ μ.support, expect μ f hf ≤ f a := by
  by_contra h
  push Not at h
  have hle : ∀ a ∈ μ.support, f a ≤ expect μ f hf := by
    intro a ha
    exact (h a ha).le
  have heq := expect_eq_const_of_le_on_support μ f (expect μ f hf) hf hle rfl
  obtain ⟨a, ha⟩ := PMF.support_nonempty μ
  have hlt := h a ha
  rw [heq a ha] at hlt
  exact (lt_irrefl _ hlt)

theorem expect_const_mul {α : Type*} {μ : PMF α} {c : ℝ} {f : α → ℝ}
    (hf : PayoffIntegrable μ f) :
    expect μ (fun a => c * f a) (payoffIntegrable_const_mul hf) =
      c * expect μ f hf := by
  unfold expect
  rw [← tsum_mul_left]
  refine tsum_congr fun a => ?_
  ring

private theorem payoffIntegrable_finset_sum_aux {α κ : Type*} (μ : PMF α)
    (s : Finset κ) (f : κ → α → ℝ) (h : ∀ k, PayoffIntegrable μ (f k)) :
    PayoffIntegrable μ (fun a => ∑ k ∈ s, f k a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using payoffIntegrable_zero μ
  | @insert k s hk ih =>
      have hsum := payoffIntegrable_add (h k) ih
      simpa [Finset.sum_insert, hk] using hsum

/-- A finite sum of absolutely integrable real payoffs remains integrable. -/
theorem payoffIntegrable_sum {α κ : Type*} [Fintype κ] (μ : PMF α)
    (f : κ → α → ℝ) (h : ∀ k, PayoffIntegrable μ (f k)) :
    PayoffIntegrable μ (fun a => ∑ k, f k a) := by
  simpa using payoffIntegrable_finset_sum_aux μ Finset.univ f h

private theorem expect_finset_sum_aux {α κ : Type*} (μ : PMF α)
    (s : Finset κ) (f : κ → α → ℝ) (h : ∀ k, PayoffIntegrable μ (f k)) :
    expect μ (fun a => ∑ k ∈ s, f k a)
      (payoffIntegrable_finset_sum_aux μ s f h) =
        ∑ k ∈ s, expect μ (f k) (h k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [expect]
  | @insert k s hk ih =>
      have hsum : PayoffIntegrable μ (fun a => ∑ j ∈ insert k s, f j a) :=
        payoffIntegrable_finset_sum_aux μ (insert k s) f h
      have hadd : PayoffIntegrable μ (fun a => f k a + ∑ j ∈ s, f j a) :=
        payoffIntegrable_add (h k) (payoffIntegrable_finset_sum_aux μ s f h)
      have hfun : (fun a => ∑ j ∈ insert k s, f j a) =
          (fun a => f k a + ∑ j ∈ s, f j a) := by
        funext a
        simp [Finset.sum_insert, hk]
      calc
        expect μ (fun a => ∑ j ∈ insert k s, f j a) hsum =
            expect μ (fun a => f k a + ∑ j ∈ s, f j a) hadd := by
          exact expect_congr_on_support
            (fun a _ => congrFun hfun a) hsum hadd
        _ = expect μ (f k) (h k) +
            expect μ (fun a => ∑ j ∈ s, f j a)
              (payoffIntegrable_finset_sum_aux μ s f h) := expect_add (h k)
                (payoffIntegrable_finset_sum_aux μ s f h)
        _ = expect μ (f k) (h k) + ∑ j ∈ s, expect μ (f j) (h j) := by
          rw [ih]
        _ = ∑ j ∈ insert k s, expect μ (f j) (h j) := by
          rw [Finset.sum_insert hk]

/-- Expected value commutes with a finite sum of absolutely integrable payoffs. -/
theorem expect_sum {α κ : Type*} [Fintype κ] (μ : PMF α)
    (f : κ → α → ℝ) (h : ∀ k, PayoffIntegrable μ (f k)) :
    expect μ (fun a => ∑ k, f k a) (payoffIntegrable_sum μ f h) =
      ∑ k, expect μ (f k) (h k) := by
  simpa using expect_finset_sum_aux μ Finset.univ f h

/-- A payoff equal on support to a finite sum inherits integrability and its
mean is the sum of the component means. -/
theorem expect_eq_sum_on_support {α κ : Type*} [Fintype κ]
    (μ : PMF α) (term : κ → α → ℝ) (value : α → ℝ)
    (hterm : ∀ k, PayoffIntegrable μ (term k))
    (hvalue : ∀ a ∈ μ.support, value a = ∑ k, term k a) :
    ∃ hvalueIntegrable : PayoffIntegrable μ value,
      expect μ value hvalueIntegrable =
        ∑ k, expect μ (term k) (hterm k) := by
  have hsum := payoffIntegrable_sum μ term hterm
  have hvalueIntegrable : PayoffIntegrable μ value :=
    payoffIntegrable_congr_on_support
      (fun a ha => (hvalue a ha).symm) hsum
  refine ⟨hvalueIntegrable, ?_⟩
  calc
    expect μ value hvalueIntegrable =
        expect μ (fun a => ∑ k, term k a) hsum :=
      expect_congr_on_support hvalue hvalueIntegrable hsum
    _ = ∑ k, expect μ (term k) (hterm k) := expect_sum μ term hterm

/-- Some supported point attains at least the mean of an integrable payoff,
even when the PMF has infinite support. -/
theorem exists_expect_le_support {α : Type*} (law : PMF α)
    (value : α → ℝ) (hvalue : PayoffIntegrable law value) :
    ∃ a ∈ law.support, expect law value hvalue ≤ value a := by
  by_contra hnone
  have hlt : ∀ a ∈ law.support, value a < expect law value hvalue := by
    intro a ha
    exact lt_of_not_ge (fun hge => hnone ⟨a, ha, hge⟩)
  have heq := expect_eq_const_of_le_on_support law value
    (expect law value hvalue) hvalue (fun a ha => (hlt a ha).le) rfl
  obtain ⟨a, ha⟩ := law.support_nonempty
  exact (ne_of_lt (hlt a ha)) (heq a ha)

end GameTheory.Math.Probability
