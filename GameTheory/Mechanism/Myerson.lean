/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Mechanism.Monotonicity
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Myerson payment identity for single-parameter mechanisms

This file gives a single-parameter specialization of `SCFWithPayments`.  A report
profile is a vector of real bids/types, an allocation rule returns each player's
served quantity, and player `i`'s value is `θᵢ * xᵢ`.

The algebraic part is independent of continuity: any DSIC single-parameter
mechanism has the usual payment-difference bounds, and therefore a monotone
allocation rule.  The constructive part uses the envelope formula

`pᵢ(θ) = θᵢ xᵢ(θ) - ∫ z in 0..θᵢ, xᵢ(z, θ₋ᵢ)`

and proves that a monotone, interval-integrable allocation rule with these
payments is DSIC.  For continuous one-dimensional allocation slices, DSIC also
implies the envelope derivative, so zero-normalized payments are uniquely pinned
down by the same formula.

## Main definitions

* `SingleParameterMechanism` — allocation and payment rules for real
  single-parameter reports.
* `SingleParameterMechanism.AllocationIsMonotone` — monotonicity of an allocation
  rule in each player's own report.
* `SingleParameterMechanism.IsMonotone` — monotonicity in each player's own
  report.
* `SingleParameterMechanism.IsImplementable` — existence of payments making an
  allocation rule DSIC.
* `SingleParameterMechanism.ZeroNormalized` — payments vanish at a zero own
  report.
* `SingleParameterMechanism.OwnAllocationContinuous` — continuity of every
  one-dimensional allocation slice.
* `SingleParameterMechanism.myersonPayment` — envelope/Myerson payment rule.
* `SingleParameterMechanism.withMyersonPayment` — mechanism using that payment.

## Main results

* `SingleParameterMechanism.payment_sandwich`
* `SingleParameterMechanism.isMonotone_of_isDSIC`
* `SingleParameterMechanism.myersonPayment_zeroNormalized`
* `SingleParameterMechanism.withMyersonPayment_isDSIC_of_isMonotone`
* `SingleParameterMechanism.isMonotone_of_isImplementable`
* `SingleParameterMechanism.isImplementable_of_isMonotone`
* `SingleParameterMechanism.payment_eq_myersonPayment_of_isDSIC_of_zeroNormalized`
* `SingleParameterMechanism.existsUnique_zeroNormalized_payment_of_isMonotone`
-/

open scoped BigOperators
open MeasureTheory

namespace GameTheory

/-- A single-parameter direct mechanism.  Reports are real numbers, the allocation
rule returns each player's assigned quantity, and the payment rule charges each
player as a function of the report profile. -/
structure SingleParameterMechanism (ι : Type) where
  /-- Allocation/quantity assigned to each player. -/
  allocation : (ι → ℝ) → ι → ℝ
  /-- Payment charged to each player. -/
  payment : (ι → ℝ) → ι → ℝ

namespace SingleParameterMechanism

variable {ι : Type} [DecidableEq ι]

/-- View a single-parameter mechanism as a quasilinear `SCFWithPayments`, where
the alternative is the vector of allocated quantities and values are linear in the
player's real type. -/
noncomputable def toSCFWithPayments (M : SingleParameterMechanism ι) :
    SCFWithPayments ι (ι → ℝ) where
  Θ := fun _ => ℝ
  value := fun i θ alloc => θ * alloc i
  choice := M.allocation
  payment := M.payment

/-- Quasilinear utility for true type `θᵢ` under a reported profile. -/
def utility (M : SingleParameterMechanism ι) (report : ι → ℝ) (i : ι) (θᵢ : ℝ) : ℝ :=
  θᵢ * M.allocation report i - M.payment report i

/-- Dominant-strategy incentive compatibility for truthful real reports. -/
def IsDSIC (M : SingleParameterMechanism ι) : Prop :=
  M.toSCFWithPayments.IsDSIC

omit [DecidableEq ι] in
@[simp] theorem toSCFWithPayments_utility (M : SingleParameterMechanism ι)
    (report : ι → ℝ) (i : ι) (θᵢ : ℝ) :
    M.toSCFWithPayments.utility report i θᵢ = M.utility report i θᵢ := rfl

/-- Direct real-report form of `IsDSIC`. -/
theorem isDSIC_iff (M : SingleParameterMechanism ι) :
    M.IsDSIC ↔ ∀ (i : ι) (θ : ι → ℝ) (b : ℝ),
      M.utility θ i (θ i) ≥ M.utility (Function.update θ i b) i (θ i) := by
  rfl

/-- Monotonicity of an allocation rule in each player's own report, holding all
other reports fixed. -/
def AllocationIsMonotone (allocation : (ι → ℝ) → ι → ℝ) : Prop :=
  ∀ (i : ι) (θ : ι → ℝ) (b : ℝ), θ i ≤ b →
    allocation θ i ≤ allocation (Function.update θ i b) i

/-- Monotonicity of a mechanism's allocation rule in each player's own report. -/
def IsMonotone (M : SingleParameterMechanism ι) : Prop :=
  AllocationIsMonotone M.allocation

/-- Allocation difference between truthful profile `θ` and replacing player `i`'s
report by `b`. -/
abbrev allocationDiff (M : SingleParameterMechanism ι) (θ : ι → ℝ) (i : ι) (b : ℝ) :
    ℝ :=
  M.allocation θ i - M.allocation (Function.update θ i b) i

/-- Payment difference between truthful profile `θ` and replacing player `i`'s
report by `b`. -/
abbrev paymentDiff (M : SingleParameterMechanism ι) (θ : ι → ℝ) (i : ι) (b : ℝ) :
    ℝ :=
  M.payment θ i - M.payment (Function.update θ i b) i

/-- One side of the DSIC payment-difference bound. -/
theorem payment_difference_le_of_isDSIC {M : SingleParameterMechanism ι}
    (h : M.IsDSIC) (i : ι) (θ : ι → ℝ) (b : ℝ) :
    M.paymentDiff θ i b ≤ θ i * M.allocationDiff θ i b := by
  have hic := h i θ b
  simp only [SCFWithPayments.utility, toSCFWithPayments] at hic
  dsimp [allocationDiff, paymentDiff]
  linarith

/-- The other side of the DSIC payment-difference bound. -/
theorem payment_difference_ge_of_isDSIC {M : SingleParameterMechanism ι}
    (h : M.IsDSIC) (i : ι) (θ : ι → ℝ) (b : ℝ) :
    b * M.allocationDiff θ i b ≤ M.paymentDiff θ i b := by
  have hic := h i (Function.update θ i b) (θ i)
  simp only [SCFWithPayments.utility, toSCFWithPayments, Function.update_self,
    Function.update_idem, Function.update_eq_self] at hic
  dsimp [allocationDiff, paymentDiff]
  linarith

/-- The standard single-parameter payment sandwich implied by DSIC. -/
theorem payment_sandwich {M : SingleParameterMechanism ι}
    (h : M.IsDSIC) (i : ι) (θ : ι → ℝ) (b : ℝ) :
    b * M.allocationDiff θ i b ≤ M.paymentDiff θ i b ∧
      M.paymentDiff θ i b ≤ θ i * M.allocationDiff θ i b :=
  ⟨payment_difference_ge_of_isDSIC h i θ b, payment_difference_le_of_isDSIC h i θ b⟩

/-- The DSIC payment bounds in the direction from report `θ i` to report `b`. -/
theorem payment_difference_bound {M : SingleParameterMechanism ι}
    (h : M.IsDSIC) (i : ι) (θ : ι → ℝ) (b : ℝ) :
    θ i *
        (M.allocation (Function.update θ i b) i - M.allocation θ i) ≤
      M.payment (Function.update θ i b) i - M.payment θ i ∧
    M.payment (Function.update θ i b) i - M.payment θ i ≤
      b * (M.allocation (Function.update θ i b) i - M.allocation θ i) := by
  have hs := payment_sandwich h i (Function.update θ i b) (θ i)
  simp only [Function.update_self, Function.update_idem, Function.update_eq_self,
    allocationDiff, paymentDiff] at hs
  exact hs

/-- DSIC implies monotonicity of the allocation rule in a single-parameter
mechanism. -/
theorem isMonotone_of_isDSIC {M : SingleParameterMechanism ι} (h : M.IsDSIC) :
    M.IsMonotone := by
  intro i θ b hle
  by_cases hlt : θ i < b
  · have hs := payment_sandwich h i θ b
    have hmul :
        0 ≤ (b - θ i) *
          (M.allocation (Function.update θ i b) i - M.allocation θ i) := by
      dsimp [allocationDiff, paymentDiff] at hs
      nlinarith
    rw [mul_comm] at hmul
    have hnonneg : 0 ≤ M.allocation (Function.update θ i b) i - M.allocation θ i :=
      nonneg_of_mul_nonneg_left hmul (sub_pos.mpr hlt)
    linarith
  · have heq : θ i = b := le_antisymm hle (le_of_not_gt hlt)
    subst heq
    simp

/-- Allocation as a one-variable function of player `i`'s report, holding the
other reports in `θ` fixed. -/
abbrev OwnAllocation (allocation : (ι → ℝ) → ι → ℝ) (i : ι) (θ : ι → ℝ) (z : ℝ) :
    ℝ :=
  allocation (Function.update θ i z) i

/-- Integrability hypothesis needed by the envelope-payment theorem.  It asks for
each one-dimensional own-report slice of the allocation rule to be interval
integrable on every compact interval. -/
def IsEnvelopeIntegrable (allocation : (ι → ℝ) → ι → ℝ) : Prop :=
  ∀ (i : ι) (θ : ι → ℝ) (a b : ℝ),
    IntervalIntegrable (OwnAllocation allocation i θ) volume a b

/-- Monotone single-parameter allocation rules have interval-integrable
own-report slices. -/
theorem isEnvelopeIntegrable_of_isMonotone {allocation : (ι → ℝ) → ι → ℝ}
    (hmono : AllocationIsMonotone allocation) : IsEnvelopeIntegrable allocation := by
  intro i θ a b
  have hown : Monotone (OwnAllocation allocation i θ) := by
    intro x y hxy
    have hxy' : (Function.update θ i x) i ≤ y := by
      simpa using hxy
    have h := hmono i (Function.update θ i x) y hxy'
    simpa [OwnAllocation, Function.update_idem] using h
  exact hown.intervalIntegrable

/-- Continuity of every one-dimensional own-report allocation slice. -/
def OwnAllocationContinuous (allocation : (ι → ℝ) → ι → ℝ) : Prop :=
  ∀ (i : ι) (θ : ι → ℝ) (z : ℝ), ContinuousAt (OwnAllocation allocation i θ) z

/-- Continuous own-report allocation slices are interval integrable. -/
theorem isEnvelopeIntegrable_of_continuous {allocation : (ι → ℝ) → ι → ℝ}
    (hcont : OwnAllocationContinuous allocation) : IsEnvelopeIntegrable allocation := by
  intro i θ a b
  exact (continuous_iff_continuousAt.2 (hcont i θ)).intervalIntegrable a b

/-- Payment normalization at zero: when player `i` reports `0`, their payment is
zero, holding other reports fixed. -/
def ZeroNormalized (M : SingleParameterMechanism ι) : Prop :=
  ∀ (i : ι) (θ : ι → ℝ), M.payment (Function.update θ i 0) i = 0

/-- The envelope derivative condition: along each one-dimensional truthful-report
slice, truthful utility has derivative equal to the allocated quantity. -/
def HasEnvelopeDerivative (M : SingleParameterMechanism ι) : Prop :=
  ∀ (i : ι) (θ : ι → ℝ) (z : ℝ),
    HasDerivAt (fun t => M.utility (Function.update θ i t) i t)
      (OwnAllocation M.allocation i θ z) z

private theorem slope_bounds_of_isDSIC {M : SingleParameterMechanism ι}
    (hdsic : M.IsDSIC) (i : ι) (θ : ι → ℝ) {z y : ℝ} (hyz : y ≠ z) :
    min (OwnAllocation M.allocation i θ z) (OwnAllocation M.allocation i θ y) ≤
      slope (fun t => M.utility (Function.update θ i t) i t) z y ∧
    slope (fun t => M.utility (Function.update θ i t) i t) z y ≤
      max (OwnAllocation M.allocation i θ z) (OwnAllocation M.allocation i θ y) := by
  by_cases hzy : z < y
  · have hlow := hdsic i (Function.update θ i y) z
    have hhigh := hdsic i (Function.update θ i z) y
    simp only [SCFWithPayments.utility, toSCFWithPayments, Function.update_self,
      Function.update_idem] at hlow hhigh
    have hpos : 0 < y - z := sub_pos.mpr hzy
    have hmono : OwnAllocation M.allocation i θ z ≤ OwnAllocation M.allocation i θ y := by
      have hm := isMonotone_of_isDSIC hdsic i (Function.update θ i z) y (by
        simp [le_of_lt hzy])
      simpa [OwnAllocation, Function.update_idem] using hm
    constructor
    · rw [min_eq_left hmono]
      rw [slope_def_field]
      exact (le_div_iff₀ hpos).2 (by
        dsimp [utility, OwnAllocation]
        nlinarith)
    · rw [max_eq_right hmono]
      rw [slope_def_field]
      exact (div_le_iff₀ hpos).2 (by
        dsimp [utility, OwnAllocation]
        nlinarith)
  · have hyzlt : y < z := lt_of_le_of_ne (le_of_not_gt hzy) hyz
    have hlow := hdsic i (Function.update θ i z) y
    have hhigh := hdsic i (Function.update θ i y) z
    simp only [SCFWithPayments.utility, toSCFWithPayments, Function.update_self,
      Function.update_idem] at hlow hhigh
    have hpos : 0 < z - y := sub_pos.mpr hyzlt
    have hmono : OwnAllocation M.allocation i θ y ≤ OwnAllocation M.allocation i θ z := by
      have hm := isMonotone_of_isDSIC hdsic i (Function.update θ i y) z (by
        simp [le_of_lt hyzlt])
      simpa [OwnAllocation, Function.update_idem] using hm
    constructor
    · rw [min_eq_right hmono]
      rw [slope_comm, slope_def_field]
      exact (le_div_iff₀ hpos).2 (by
        dsimp [utility, OwnAllocation]
        nlinarith)
    · rw [max_eq_left hmono]
      rw [slope_comm, slope_def_field]
      exact (div_le_iff₀ hpos).2 (by
        dsimp [utility, OwnAllocation]
        nlinarith)

/-- With continuous one-dimensional allocation slices, DSIC implies the envelope
derivative condition.  The proof squeezes truthful-utility slopes between the
allocation at the two endpoints. -/
theorem hasEnvelopeDerivative_of_isDSIC_of_continuous {M : SingleParameterMechanism ι}
    (hdsic : M.IsDSIC) (hcont : OwnAllocationContinuous M.allocation) :
    M.HasEnvelopeDerivative := by
  intro i θ z
  rw [hasDerivAt_iff_tendsto_slope]
  have hx : Filter.Tendsto (fun y => OwnAllocation M.allocation i θ y)
      (nhdsWithin z {z}ᶜ) (nhds (OwnAllocation M.allocation i θ z)) :=
    (hcont i θ z).tendsto.mono_left nhdsWithin_le_nhds
  have hconst : Filter.Tendsto (fun _ : ℝ => OwnAllocation M.allocation i θ z)
      (nhdsWithin z {z}ᶜ) (nhds (OwnAllocation M.allocation i θ z)) :=
    tendsto_const_nhds
  have hmin := hconst.min hx
  have hmax := hconst.max hx
  simp only [min_self] at hmin
  simp only [max_self] at hmax
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hmin hmax ?_ ?_
  · filter_upwards [eventually_mem_nhdsWithin] with y hy
    exact (slope_bounds_of_isDSIC hdsic i θ hy).1
  · filter_upwards [eventually_mem_nhdsWithin] with y hy
    exact (slope_bounds_of_isDSIC hdsic i θ hy).2

private theorem endpoint_mul_le_integral {allocation : (ι → ℝ) → ι → ℝ}
    (hmono : AllocationIsMonotone allocation)
    (hint : IsEnvelopeIntegrable allocation)
    (i : ι) (θ : ι → ℝ) {a b : ℝ} (hab : a ≤ b) :
    (b - a) * allocation (Function.update θ i a) i ≤
      ∫ z in a..b, OwnAllocation allocation i θ z := by
  have hconst : IntervalIntegrable
      (fun _ : ℝ => allocation (Function.update θ i a) i) volume a b := by
    exact intervalIntegrable_const
  have hle : ∫ z in a..b, (allocation (Function.update θ i a) i) ≤
      ∫ z in a..b, OwnAllocation allocation i θ z := by
    refine intervalIntegral.integral_mono_on hab hconst (hint i θ a b) ?_
    intro z hz
    have h := hmono i (Function.update θ i a) z ?_
    · simpa [OwnAllocation, Function.update_idem] using h
    · simpa [Function.update_self] using hz.1
  simpa [intervalIntegral.integral_const, smul_eq_mul] using hle

private theorem integral_le_endpoint_mul {allocation : (ι → ℝ) → ι → ℝ}
    (hmono : AllocationIsMonotone allocation)
    (hint : IsEnvelopeIntegrable allocation)
    (i : ι) (θ : ι → ℝ) {a b : ℝ} (hab : a ≤ b) :
    (∫ z in a..b, OwnAllocation allocation i θ z) ≤
      (b - a) * allocation (Function.update θ i b) i := by
  have hconst : IntervalIntegrable
      (fun _ : ℝ => allocation (Function.update θ i b) i) volume a b := by
    exact intervalIntegrable_const
  have hle : ∫ z in a..b, OwnAllocation allocation i θ z ≤
      ∫ z in a..b, (allocation (Function.update θ i b) i) := by
    refine intervalIntegral.integral_mono_on hab (hint i θ a b) hconst ?_
    intro z hz
    have h := hmono i (Function.update θ i z) b ?_
    · simpa [OwnAllocation, Function.update_idem] using h
    · simpa [Function.update_self] using hz.2
  simpa [intervalIntegral.integral_const, smul_eq_mul] using hle

/-- The Myerson/envelope payment for a single-parameter allocation rule. -/
noncomputable def myersonPayment (allocation : (ι → ℝ) → ι → ℝ)
    (θ : ι → ℝ) (i : ι) : ℝ :=
  θ i * allocation θ i - ∫ z in 0..θ i, OwnAllocation allocation i θ z

/-- The single-parameter mechanism that pairs an allocation rule with its
Myerson/envelope payment. -/
noncomputable def withMyersonPayment (allocation : (ι → ℝ) → ι → ℝ) :
    SingleParameterMechanism ι where
  allocation := allocation
  payment := myersonPayment allocation

/-- Myerson payments are zero-normalized. -/
theorem myersonPayment_zeroNormalized (allocation : (ι → ℝ) → ι → ℝ) :
    (withMyersonPayment allocation).ZeroNormalized := by
  intro i θ
  simp [withMyersonPayment, myersonPayment, OwnAllocation]

/-- The Myerson-payment mechanism satisfies the envelope derivative condition when
allocation slices are continuous. -/
theorem withMyersonPayment_hasEnvelopeDerivative_of_continuous
    (allocation : (ι → ℝ) → ι → ℝ)
    (hcont : OwnAllocationContinuous allocation) :
    (withMyersonPayment allocation).HasEnvelopeDerivative := by
  intro i θ z
  have hint := isEnvelopeIntegrable_of_continuous hcont
  have hmeas : StronglyMeasurableAtFilter (OwnAllocation allocation i θ) (nhds z) volume :=
    ContinuousAt.stronglyMeasurableAtFilter isOpen_univ
      (fun x _ => hcont i θ x) z (Set.mem_univ z)
  have hderiv := intervalIntegral.integral_hasDerivAt_right
    (a := 0) (b := z) (f := OwnAllocation allocation i θ)
    (hint i θ 0 z) hmeas (hcont i θ z)
  simpa [utility, withMyersonPayment, myersonPayment, OwnAllocation] using hderiv

/-- Envelope derivative plus zero normalization forces the Myerson payment formula. -/
theorem payment_eq_myersonPayment_of_zeroNormalized_of_hasEnvelopeDerivative
    {M : SingleParameterMechanism ι}
    (hzero : M.ZeroNormalized)
    (hderiv : M.HasEnvelopeDerivative)
    (hint : IsEnvelopeIntegrable M.allocation)
    (θ : ι → ℝ) (i : ι) :
    M.payment θ i = myersonPayment M.allocation θ i := by
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := θ i)
    (f := fun t => M.utility (Function.update θ i t) i t)
    (f' := OwnAllocation M.allocation i θ)
    (fun z _hz => hderiv i θ z) (hint i θ 0 (θ i))
  simp only [utility, OwnAllocation] at hFTC
  have hupdate : Function.update θ i (θ i) = θ :=
    Function.update_eq_self i θ
  rw [hupdate] at hFTC
  have hzero' := hzero i θ
  dsimp [myersonPayment]
  simp only [OwnAllocation]
  linarith

/-- A zero-normalized DSIC mechanism with continuous allocation slices must use
the Myerson payment formula. -/
theorem payment_eq_myersonPayment_of_isDSIC_of_zeroNormalized
    {M : SingleParameterMechanism ι}
    (hdsic : M.IsDSIC)
    (hzero : M.ZeroNormalized)
    (hcont : OwnAllocationContinuous M.allocation)
    (θ : ι → ℝ) (i : ι) :
    M.payment θ i = myersonPayment M.allocation θ i :=
  payment_eq_myersonPayment_of_zeroNormalized_of_hasEnvelopeDerivative hzero
    (hasEnvelopeDerivative_of_isDSIC_of_continuous hdsic hcont)
    (isEnvelopeIntegrable_of_continuous hcont) θ i

/-- The payment identity written out with the integral formula. -/
theorem payment_formula_of_isDSIC_of_zeroNormalized
    {M : SingleParameterMechanism ι}
    (hdsic : M.IsDSIC)
    (hzero : M.ZeroNormalized)
    (hcont : OwnAllocationContinuous M.allocation)
    (θ : ι → ℝ) (i : ι) :
    M.payment θ i =
      θ i * M.allocation θ i - ∫ z in 0..θ i, OwnAllocation M.allocation i θ z := by
  simpa [myersonPayment] using
    payment_eq_myersonPayment_of_isDSIC_of_zeroNormalized hdsic hzero hcont θ i

/-- The Myerson/envelope payment makes every monotone interval-integrable
single-parameter allocation rule DSIC. -/
theorem withMyersonPayment_isDSIC_of_isMonotone
    (allocation : (ι → ℝ) → ι → ℝ)
    (hmono : AllocationIsMonotone allocation)
    (hint : IsEnvelopeIntegrable allocation) :
    (withMyersonPayment allocation).IsDSIC := by
  rw [isDSIC_iff]
  intro i θ b
  by_cases hbθ : b ≤ θ i
  · have hseg := endpoint_mul_le_integral (allocation := allocation) hmono hint i θ hbθ
    have hsub := intervalIntegral.integral_interval_sub_left
      (hint i θ 0 (θ i)) (hint i θ 0 b)
    simp only [utility, withMyersonPayment, myersonPayment, OwnAllocation,
      Function.update_self, Function.update_idem] at hseg hsub ⊢
    linarith
  · have hθb : θ i ≤ b := le_of_not_ge hbθ
    have hseg := integral_le_endpoint_mul (allocation := allocation) hmono hint i θ hθb
    have hsub := intervalIntegral.integral_interval_sub_left
      (hint i θ 0 b) (hint i θ 0 (θ i))
    simp only [utility, withMyersonPayment, myersonPayment, OwnAllocation,
      Function.update_self, Function.update_idem] at hseg hsub ⊢
    linarith

/-- A single-parameter allocation rule is implementable if some payment rule makes
it DSIC. -/
def IsImplementable (allocation : (ι → ℝ) → ι → ℝ) : Prop :=
  ∃ payment : (ι → ℝ) → ι → ℝ,
    (⟨allocation, payment⟩ : SingleParameterMechanism ι).IsDSIC

/-- DSIC implementability forces monotonicity of the allocation rule. -/
theorem isMonotone_of_isImplementable {allocation : (ι → ℝ) → ι → ℝ}
    (himpl : IsImplementable allocation) : AllocationIsMonotone allocation := by
  rcases himpl with ⟨payment, hdsic⟩
  exact isMonotone_of_isDSIC (M := ⟨allocation, payment⟩) hdsic

/-- A monotone interval-integrable allocation rule is DSIC-implementable by the
Myerson payment. -/
theorem isImplementable_of_isMonotone {allocation : (ι → ℝ) → ι → ℝ}
    (hmono : AllocationIsMonotone allocation) (hint : IsEnvelopeIntegrable allocation) :
    IsImplementable allocation :=
  ⟨myersonPayment allocation, withMyersonPayment_isDSIC_of_isMonotone allocation hmono hint⟩

/-- For continuous monotone allocation rules, the Myerson payment is the unique
zero-normalized payment rule that implements the allocation in dominant
strategies. -/
theorem existsUnique_zeroNormalized_payment_of_isMonotone
    (allocation : (ι → ℝ) → ι → ℝ)
    (hmono : AllocationIsMonotone allocation)
    (hcont : OwnAllocationContinuous allocation) :
    ∃! payment : (ι → ℝ) → ι → ℝ,
      (⟨allocation, payment⟩ : SingleParameterMechanism ι).IsDSIC ∧
        (⟨allocation, payment⟩ : SingleParameterMechanism ι).ZeroNormalized := by
  refine ⟨myersonPayment allocation, ?_, ?_⟩
  · exact ⟨withMyersonPayment_isDSIC_of_isMonotone allocation hmono
      (isEnvelopeIntegrable_of_continuous hcont),
      myersonPayment_zeroNormalized allocation⟩
  · intro payment hpayment
    funext θ i
    exact payment_eq_myersonPayment_of_isDSIC_of_zeroNormalized
      (M := ⟨allocation, payment⟩) hpayment.1 hpayment.2 hcont θ i

end SingleParameterMechanism

end GameTheory
