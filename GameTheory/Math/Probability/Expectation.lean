import Mathlib.Probability.ProbabilityMassFunction.Constructions

noncomputable section

open scoped BigOperators

namespace GameTheory.Math.Probability

/-- A real payoff has a finite weighted absolute sum under this law. -/
def PayoffIntegrable {α : Type*} (μ : PMF α) (f : α → ℝ) : Prop :=
  Summable (fun a => (μ a).toReal * |f a|)

/-- A positive pointwise lower bound on target weights transfers absolute
integrability to the source law. -/
theorem payoffIntegrable_of_scaled_weight_le {α : Type*}
    (source target : PMF α) (f : α → ℝ) (scale : ℝ)
    (hscale : 0 < scale)
    (hle : ∀ a, scale * (source a).toReal ≤ (target a).toReal)
    (htarget : PayoffIntegrable target f) :
    PayoffIntegrable source f := by
  have hs : Summable (fun a =>
      scale⁻¹ * ((target a).toReal * |f a|)) :=
    htarget.mul_left scale⁻¹
  apply Summable.of_nonneg_of_le
    (fun a => mul_nonneg ENNReal.toReal_nonneg (abs_nonneg _))
    (fun a => ?_) hs
  have hweight : (source a).toReal ≤ scale⁻¹ * (target a).toReal := by
    calc
      (source a).toReal ≤ (target a).toReal / scale :=
        (le_div_iff₀ hscale).2 (by simpa [mul_comm] using hle a)
      _ = scale⁻¹ * (target a).toReal := by rw [div_eq_mul_inv]; ring
  calc
    (source a).toReal * |f a| ≤
        (scale⁻¹ * (target a).toReal) * |f a| :=
      mul_le_mul_of_nonneg_right hweight (abs_nonneg _)
    _ = scale⁻¹ * ((target a).toReal * |f a|) := by ring

/-- Absolute integration also supplies summability of the signed weighted
payoff. -/
theorem PayoffIntegrable.summable {α : Type*} {μ : PMF α} {f : α → ℝ}
    (h : PayoffIntegrable μ f) :
    Summable (fun a => (μ a).toReal * f a) := by
  have habs : Summable (fun a => (μ a).toReal * |f a|) := by
    simpa only [PayoffIntegrable] using h
  have hnorm : Summable (fun a => ‖(μ a).toReal * f a‖) := by
    simpa [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg ENNReal.toReal_nonneg] using habs
  exact hnorm.of_norm

/-- Extend a real value defined on the support of a PMF by zero elsewhere.
The off-support choice is immaterial to expectations under that PMF. -/
noncomputable def extendFromSupport {α : Type*} (μ : PMF α)
    (value : ∀ a, a ∈ μ.support → ℝ) : α → ℝ := by
  classical
  exact fun a => if ha : a ∈ μ.support then value a ha else 0

/-- The expected payoff, defined only with an absolute-summability certificate. -/
noncomputable def expect {α : Type*} (μ : PMF α) (f : α → ℝ)
    (_h : PayoffIntegrable μ f) : ℝ :=
  ∑' a, (μ a).toReal * f a

theorem pmf_weight_summable {α : Type*} (μ : PMF α) :
    Summable (fun a => (μ a).toReal) := by
  apply ENNReal.summable_toReal
  rw [PMF.tsum_coe]
  exact ENNReal.one_ne_top

/-- The real atom weights of a PMF sum to one. -/
theorem pmf_weight_tsum_one {α : Type*} (μ : PMF α) :
    (∑' value, (μ value).toReal) = 1 := by
  rw [← ENNReal.tsum_toReal_eq (fun value => μ.apply_ne_top value), PMF.tsum_coe]
  rfl

theorem payoffIntegrable_of_bounded_on_support {α : Type*}
    (μ : PMF α) (f : α → ℝ) {C : ℝ}
    (hbound : ∀ a ∈ μ.support, |f a| ≤ C) :
    PayoffIntegrable μ f := by
  apply Summable.of_nonneg_of_le
    (fun a => mul_nonneg ENNReal.toReal_nonneg (abs_nonneg _))
    (fun a => ?_) ((pmf_weight_summable μ).mul_right C)
  by_cases ha : a ∈ μ.support
  · exact mul_le_mul_of_nonneg_left (hbound a ha) ENNReal.toReal_nonneg
  · have hzero : μ a = 0 := not_ne_iff.mp ha
    simp [hzero]

theorem payoffIntegrable_of_bounded {α : Type*}
    (μ : PMF α) (f : α → ℝ) {C : ℝ}
    (hbound : ∀ a, |f a| ≤ C) :
    PayoffIntegrable μ f :=
  payoffIntegrable_of_bounded_on_support μ f
    (fun a _ => hbound a)

theorem payoffIntegrable_of_finite_support {α : Type*}
    (μ : PMF α) (f : α → ℝ) (hfinite : μ.support.Finite) :
    PayoffIntegrable μ f := by
  let values := (fun a => |f a|) '' μ.support
  have hvalues : values.Finite := hfinite.image _
  obtain ⟨C, hC⟩ := hvalues.bddAbove
  apply payoffIntegrable_of_bounded_on_support μ f
  intro a ha
  exact hC ⟨a, ha, rfl⟩

theorem payoffIntegrable_of_finite {α : Type*} [Finite α]
    (μ : PMF α) (f : α → ℝ) : PayoffIntegrable μ f :=
  payoffIntegrable_of_finite_support μ f (Set.toFinite _)

theorem payoffIntegrable_constant {α : Type*} (μ : PMF α) (c : ℝ) :
    PayoffIntegrable μ (fun _ => c) :=
  payoffIntegrable_of_bounded μ (fun _ => c) (C := |c|) (fun _ => le_rfl)

theorem payoffIntegrable_pure {α : Type*} (a : α) (f : α → ℝ) :
    PayoffIntegrable (PMF.pure a) f := by
  apply payoffIntegrable_of_bounded_on_support
    (C := |f a|) (μ := PMF.pure a) (f := f)
  intro b hb
  rw [PMF.mem_support_pure_iff] at hb
  subst b
  rfl

theorem expect_pure {α : Type*} (a : α) (f : α → ℝ)
    (h : PayoffIntegrable (PMF.pure a) f) :
    expect (PMF.pure a) f h = f a := by
  classical
  unfold expect
  rw [tsum_eq_single a]
  · simp [PMF.pure_apply]
  · intro b hb
    have hzero : (PMF.pure a b).toReal = 0 := by
      simp [PMF.pure_apply, hb]
    rw [hzero]
    simp

theorem expect_eq_sum {α : Type*} [Fintype α] (μ : PMF α) (f : α → ℝ)
    (h : PayoffIntegrable μ f) :
    expect μ f h = ∑ a, (μ a).toReal * f a := by
  simp [expect, tsum_fintype]

/-- A constant payoff has its constant value under every probability mass
function. -/
theorem expect_constant {α : Type*} (μ : PMF α) (c : ℝ)
    (h : PayoffIntegrable μ (fun _ => c)) :
    expect μ (fun _ => c) h = c := by
  have hmass : (∑' a, (μ a).toReal) = 1 := by
    exact pmf_weight_tsum_one μ
  simp only [expect]
  rw [tsum_mul_right, hmass, one_mul]

theorem expect_congr_on_support {α : Type*} {μ : PMF α}
    {f g : α → ℝ} (hfg : ∀ a ∈ μ.support, f a = g a)
    (hf : PayoffIntegrable μ f) (hg : PayoffIntegrable μ g) :
    expect μ f hf = expect μ g hg := by
  apply tsum_congr
  intro a
  by_cases ha : a ∈ μ.support
  · rw [hfg a ha]
  · have hzero : μ a = 0 := not_ne_iff.mp ha
    simp [hzero]

theorem payoffIntegrable_congr_on_support {α : Type*} {μ : PMF α}
    {f g : α → ℝ} (hfg : ∀ a ∈ μ.support, f a = g a)
    (hf : PayoffIntegrable μ f) : PayoffIntegrable μ g := by
  unfold PayoffIntegrable at hf ⊢
  exact hf.congr fun a => by
    by_cases ha : a ∈ μ.support
    · rw [hfg a ha]
    · have hzero : μ a = 0 := not_ne_iff.mp ha
      simp [hzero]

theorem payoffIntegrable_congr_law {α : Type*} {μ ν : PMF α}
    (hlaw : μ = ν) {f : α → ℝ} (hf : PayoffIntegrable μ f) :
    PayoffIntegrable ν f := by
  unfold PayoffIntegrable at hf ⊢
  apply hf.congr
  intro a
  exact congrArg (fun mass : ENNReal => mass.toReal * |f a|)
    (congrArg (fun law : PMF α => law a) hlaw)

theorem expect_proof_irrel {α : Type*} (μ : PMF α) (f : α → ℝ)
    (h₁ h₂ : PayoffIntegrable μ f) :
    expect μ f h₁ = expect μ f h₂ := rfl

theorem expect_congr_law {α : Type*} {μ ν : PMF α} (hlaw : μ = ν)
    (f : α → ℝ) (hμ : PayoffIntegrable μ f) (hν : PayoffIntegrable ν f) :
    expect μ f hμ = expect ν f hν := by
  unfold expect
  apply tsum_congr
  intro a
  exact congrArg (fun (mass : ENNReal) => mass.toReal * f a)
    (congrArg (fun law : PMF α => law a) hlaw)

theorem expect_mono {α : Type*} {μ : PMF α} {f g : α → ℝ}
    (hfg : ∀ a ∈ μ.support, f a ≤ g a)
    (hf : PayoffIntegrable μ f) (hg : PayoffIntegrable μ g) :
    expect μ f hf ≤ expect μ g hg := by
  have hfs := hf.summable
  have hgs := hg.summable
  rw [expect, expect]
  apply hfs.tsum_le_tsum (fun a => ?_) hgs
  by_cases ha : a ∈ μ.support
  · exact mul_le_mul_of_nonneg_left (hfg a ha) ENNReal.toReal_nonneg
  · have hzero : μ a = 0 := not_ne_iff.mp ha
    simp [hzero]

/-- A strict payoff improvement at one positive-mass atom makes the
expectation strictly larger when the payoff comparison holds on the support. -/
theorem expect_lt_of_mem_support {α : Type*} {μ : PMF α} {f g : α → ℝ}
    (hf : PayoffIntegrable μ f) (hg : PayoffIntegrable μ g)
    (hle : ∀ a ∈ μ.support, f a ≤ g a)
    (a : α) (ha : a ∈ μ.support) (hlt : f a < g a) :
    expect μ f hf < expect μ g hg := by
  have hmass : 0 < (μ a).toReal :=
    ENNReal.toReal_pos ((μ.mem_support_iff a).mp ha) (μ.apply_ne_top a)
  unfold expect
  apply Summable.tsum_lt_tsum
  · intro b
    by_cases hb : b ∈ μ.support
    · exact mul_le_mul_of_nonneg_left (hle b hb) ENNReal.toReal_nonneg
    · have hzero : μ b = 0 := not_ne_iff.mp hb
      simp [hzero]
  · exact mul_lt_mul_of_pos_left hlt hmass
  · exact hf.summable
  · exact hg.summable

/-- The absolute value of an integrable expected payoff inherits a uniform bound. -/
theorem expect_abs_le_of_bounded {α : Type*} {μ : PMF α}
    {f : α → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ a, |f a| ≤ C) (hf : PayoffIntegrable μ f) :
    |expect μ f hf| ≤ C := by
  have hplus : PayoffIntegrable μ (fun _ => C) :=
    payoffIntegrable_of_bounded μ _ (C := C)
      (fun _ => by simp [abs_of_nonneg hC])
  have hminus : PayoffIntegrable μ (fun _ => -C) :=
    payoffIntegrable_of_bounded μ _ (C := C) (fun _ => by
      simp [abs_of_nonpos (neg_nonpos.mpr hC)])
  have hupper : expect μ f hf ≤ expect μ (fun _ => C) hplus :=
    expect_mono (fun a _ => (abs_le.mp (hbound a)).2) hf hplus
  have hlower : expect μ (fun _ => -C) hminus ≤ expect μ f hf :=
    expect_mono (fun a _ => (abs_le.mp (hbound a)).1) hminus hf
  have hvalplus := expect_constant μ C hplus
  have hvalminus := expect_constant μ (-C) hminus
  rw [hvalplus] at hupper
  rw [hvalminus] at hlower
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- An integrable payoff nonnegative on the support has nonnegative expectation. -/
theorem expect_nonneg {α : Type*} (μ : PMF α)
    (f : α → ℝ) (hf : PayoffIntegrable μ f)
    (h0 : ∀ a ∈ μ.support, 0 ≤ f a) : 0 ≤ expect μ f hf := by
  have hzero := payoffIntegrable_constant μ 0
  have h := expect_mono (μ := μ) (f := fun _ => 0) (g := f)
    h0 hzero hf
  simpa [expect_constant μ 0 hzero] using h

/-- An integrable payoff bounded above on the support has that expectation bound. -/
theorem expect_le_const {α : Type*} (μ : PMF α)
    (f : α → ℝ) (hf : PayoffIntegrable μ f) (c : ℝ)
    (hfc : ∀ a ∈ μ.support, f a ≤ c) : expect μ f hf ≤ c := by
  have hc := payoffIntegrable_constant μ c
  have h := expect_mono (μ := μ) (f := f) (g := fun _ => c)
    hfc hf hc
  simpa [expect_constant μ c hc] using h

end GameTheory.Math.Probability
