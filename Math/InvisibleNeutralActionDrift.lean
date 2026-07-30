/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.AlgebraicSelection

/-!
# Analytic drift at a discount scale

This file isolates the scalar analytic calculation left by a response which
is unused along a punctured Bellman germ. A transition drift of order below
the discount scale has a strictly negative leading coefficient and therefore
supplies a bounded centered transition score. A drift divisible by the
discount power instead contributes one finite coefficient to the endpoint
bias inequality.

The endpoint branch deliberately retains this extra coefficient. Absorbing a
finite family of such coefficients into one state potential is a separate
finite-dimensional compatibility problem.
-/

noncomputable section

open Filter Finset Set Topology

namespace Math

/-- The discounted scalar expression after writing the moving value as its
endpoint plus a discount-order correction. -/
def discountScaleExpression
    (q : ℕ) (g D E : ℝ → ℝ) (t : ℝ) : ℝ :=
  t ^ q * g t + (1 - t ^ q) * (D t + t ^ q * E t)

/-- If the transition drift has order `m < q`, its analytic leading factor
is negative. The final component is the corresponding sharp power-law lower
bound for `-D`. -/
theorem analytic_discountScale_factor_negative_of_order_lt
    {q m : ℕ} {g D E : ℝ → ℝ}
    (hq : 0 < q)
    (hg : AnalyticAt ℝ g 0)
    (hD : AnalyticAt ℝ D 0)
    (hE : AnalyticAt ℝ E 0)
    (horder : analyticOrderAt D 0 = m)
    (hm : m < q)
    (hineq :
      ∀ᶠ t in 𝓝[>] (0 : ℝ),
        discountScaleExpression q g D E t ≤ 0) :
    ∃ factor : ℝ → ℝ,
      AnalyticAt ℝ factor 0 ∧
      factor 0 < 0 ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), D t = t ^ m * factor t) ∧
      ∃ c : ℝ, 0 < c ∧
        ∀ᶠ t in 𝓝[>] (0 : ℝ),
          c * t ^ m ≤ -D t := by
  obtain ⟨factor, hfactorAnalytic, hfactorNe, hfactor⟩ :=
    hD.analyticOrderAt_eq_natCast.mp horder
  let normalized : ℝ → ℝ := fun t =>
    t ^ (q - m) * g t +
      (1 - t ^ q) * (factor t + t ^ (q - m) * E t)
  have hnormalizedAnalytic :
      AnalyticAt ℝ normalized 0 := by
    dsimp only [normalized]
    fun_prop
  have hnormalizedNonpos :
      ∀ᶠ t in 𝓝[>] (0 : ℝ), normalized t ≤ 0 := by
    filter_upwards [
      hineq,
      hfactor.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with t ht hfactorAt htpos
    simp only [sub_zero, smul_eq_mul] at hfactorAt
    have hpow : q = m + (q - m) := by omega
    have hpowFactor : t ^ q = t ^ m * t ^ (q - m) := by
      exact (congrArg (fun n : ℕ => t ^ n) hpow).trans
        (pow_add t m (q - m))
    have hexpression :
        discountScaleExpression q g D E t =
          t ^ m * normalized t := by
      rw [discountScaleExpression, hfactorAt]
      dsimp only [normalized]
      rw [hpowFactor]
      ring
    rw [hexpression] at ht
    have htpos' : 0 < t := htpos
    nlinarith [pow_pos htpos' m]
  have hnormalizedLimit :
      Tendsto normalized (𝓝[>] (0 : ℝ))
        (𝓝 (normalized 0)) :=
    hnormalizedAnalytic.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hnormalizedZero : normalized 0 ≤ 0 :=
    le_of_tendsto hnormalizedLimit hnormalizedNonpos
  have hsubPos : 0 < q - m := Nat.sub_pos_of_lt hm
  have hnormalizedAtZero : normalized 0 = factor 0 := by
    simp [normalized, hq.ne', hsubPos.ne']
  have hfactorNeg : factor 0 < 0 := by
    rw [hnormalizedAtZero] at hnormalizedZero
    exact lt_of_le_of_ne hnormalizedZero hfactorNe
  refine ⟨factor, hfactorAnalytic, hfactorNeg, ?_, ?_⟩
  · simpa [sub_zero, smul_eq_mul] using hfactor
  · let c : ℝ := -factor 0 / 2
    have hc : 0 < c := by
      dsimp only [c]
      linarith
    have hfactorUpper :
        ∀ᶠ t in 𝓝 (0 : ℝ), factor t < factor 0 / 2 :=
      hfactorAnalytic.continuousAt.tendsto.eventually_lt_const
        (by linarith)
    refine ⟨c, hc, ?_⟩
    filter_upwards [
      hfactor.filter_mono nhdsWithin_le_nhds,
      hfactorUpper.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with t hfactorAt hupper htpos
    simp only [sub_zero, smul_eq_mul] at hfactorAt
    have hpowNonneg : 0 ≤ t ^ m := (pow_pos htpos m).le
    calc
      c * t ^ m ≤ (-factor t) * t ^ m := by
        apply mul_le_mul_of_nonneg_right _ hpowNonneg
        dsimp only [c]
        linarith
      _ = -D t := by rw [hfactorAt]; ring

/-- If the transition drift is divisible by the discount power, its quotient
contributes a finite coefficient to the endpoint inequality. -/
theorem analytic_discountScale_endpoint_of_order_ge
    {q : ℕ} {g D E : ℝ → ℝ}
    (hq : 0 < q)
    (hg : AnalyticAt ℝ g 0)
    (hD : AnalyticAt ℝ D 0)
    (hE : AnalyticAt ℝ E 0)
    (horder : (q : ℕ∞) ≤ analyticOrderAt D 0)
    (hineq :
      ∀ᶠ t in 𝓝[>] (0 : ℝ),
        discountScaleExpression q g D E t ≤ 0) :
    ∃ quotient : ℝ → ℝ,
      AnalyticAt ℝ quotient 0 ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), D t = t ^ q * quotient t) ∧
      g 0 + E 0 + quotient 0 ≤ 0 := by
  obtain ⟨quotient, hquotientAnalytic, hquotient⟩ :=
    (natCast_le_analyticOrderAt hD).mp horder
  let normalized : ℝ → ℝ := fun t =>
    g t + (1 - t ^ q) * (quotient t + E t)
  have hnormalizedAnalytic :
      AnalyticAt ℝ normalized 0 := by
    dsimp only [normalized]
    fun_prop
  have hnormalizedNonpos :
      ∀ᶠ t in 𝓝[>] (0 : ℝ), normalized t ≤ 0 := by
    filter_upwards [
      hineq,
      hquotient.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with t ht hquotientAt htpos
    have hexpression :
        discountScaleExpression q g D E t =
          t ^ q * normalized t := by
      simp only [sub_zero, smul_eq_mul] at hquotientAt
      rw [discountScaleExpression, hquotientAt]
      dsimp only [normalized]
      ring
    rw [hexpression] at ht
    have htpos' : 0 < t := htpos
    nlinarith [pow_pos htpos' q]
  have hnormalizedLimit :
      Tendsto normalized (𝓝[>] (0 : ℝ))
        (𝓝 (normalized 0)) :=
    hnormalizedAnalytic.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hnormalizedZero : normalized 0 ≤ 0 :=
    le_of_tendsto hnormalizedLimit hnormalizedNonpos
  have hnormalizedAtZero :
      normalized 0 = g 0 + E 0 + quotient 0 := by
    simp [normalized, hq.ne']
    ring
  refine ⟨quotient, hquotientAnalytic, ?_, ?_⟩
  · simpa [sub_zero, smul_eq_mul] using hquotient
  · rwa [hnormalizedAtZero] at hnormalizedZero

/-- Sharp order dichotomy for an analytic drift at a positive integral
discount scale. The first branch records the true order and negative leading
factor. The second includes both an identically zero drift and every drift
whose order is at least the discount order. -/
theorem analytic_discountScale_dichotomy
    {q : ℕ} {g D E : ℝ → ℝ}
    (hq : 0 < q)
    (hg : AnalyticAt ℝ g 0)
    (hD : AnalyticAt ℝ D 0)
    (hE : AnalyticAt ℝ E 0)
    (hineq :
      ∀ᶠ t in 𝓝[>] (0 : ℝ),
        discountScaleExpression q g D E t ≤ 0) :
    (∃ (m : ℕ) (factor : ℝ → ℝ) (c : ℝ),
        m < q ∧
        AnalyticAt ℝ factor 0 ∧
        factor 0 < 0 ∧
        0 < c ∧
        (∀ᶠ t in 𝓝 (0 : ℝ), D t = t ^ m * factor t) ∧
        ∀ᶠ t in 𝓝[>] (0 : ℝ), c * t ^ m ≤ -D t) ∨
      ∃ quotient : ℝ → ℝ,
        AnalyticAt ℝ quotient 0 ∧
        (∀ᶠ t in 𝓝 (0 : ℝ), D t = t ^ q * quotient t) ∧
        g 0 + E 0 + quotient 0 ≤ 0 := by
  by_cases htop : analyticOrderAt D 0 = ⊤
  · right
    apply analytic_discountScale_endpoint_of_order_ge
      hq hg hD hE (by simp [htop]) hineq
  · let m := analyticOrderNatAt D 0
    have horder : analyticOrderAt D 0 = (m : ℕ∞) := by
      exact (Nat.cast_analyticOrderNatAt htop).symm
    rcases lt_or_ge m q with hm | hm
    · left
      obtain ⟨factor, hfactorAnalytic, hfactorNeg,
          hfactor, c, hc, hcharge⟩ :=
        analytic_discountScale_factor_negative_of_order_lt
          hq hg hD hE horder hm hineq
      exact ⟨m, factor, c, hm, hfactorAnalytic,
        hfactorNeg, hc, hfactor, hcharge⟩
    · right
      have horderGe :
          (q : ℕ∞) ≤ analyticOrderAt D 0 := by
        rw [horder]
        exact_mod_cast hm
      exact analytic_discountScale_endpoint_of_order_ge
        hq hg hD hE horderGe hineq

/-- Neutral-endpoint specialization of the order dichotomy. A nonzero
low-order drift then has strictly positive order. -/
theorem analytic_discountScale_neutral_dichotomy
    {q : ℕ} {g D E : ℝ → ℝ}
    (hq : 0 < q)
    (hg : AnalyticAt ℝ g 0)
    (hD : AnalyticAt ℝ D 0)
    (hE : AnalyticAt ℝ E 0)
    (hD0 : D 0 = 0)
    (hineq :
      ∀ᶠ t in 𝓝[>] (0 : ℝ),
        discountScaleExpression q g D E t ≤ 0) :
    (∃ (m : ℕ) (factor : ℝ → ℝ) (c : ℝ),
        0 < m ∧
        m < q ∧
        AnalyticAt ℝ factor 0 ∧
        factor 0 < 0 ∧
        0 < c ∧
        (∀ᶠ t in 𝓝 (0 : ℝ), D t = t ^ m * factor t) ∧
        ∀ᶠ t in 𝓝[>] (0 : ℝ), c * t ^ m ≤ -D t) ∨
      ∃ quotient : ℝ → ℝ,
        AnalyticAt ℝ quotient 0 ∧
        (∀ᶠ t in 𝓝 (0 : ℝ), D t = t ^ q * quotient t) ∧
        g 0 + E 0 + quotient 0 ≤ 0 := by
  rcases analytic_discountScale_dichotomy hq hg hD hE hineq with
      hlow | hendpoint
  · left
    obtain ⟨m, factor, c, hm, hfactorAnalytic,
        hfactorNeg, hc, hfactor, hcharge⟩ := hlow
    have hmpos : 0 < m := by
      by_contra hmzero
      have hm0 : m = 0 := Nat.eq_zero_of_not_pos hmzero
      have hfactorZero := hfactor.self_of_nhds
      rw [hm0, hD0] at hfactorZero
      simp at hfactorZero
      linarith
    exact ⟨m, factor, c, hmpos, hm, hfactorAnalytic,
      hfactorNeg, hc, hfactor, hcharge⟩
  · exact Or.inr hendpoint

section CenteredScore

variable {S : Type*} [Fintype S]

/-- Pairing of a finite signed state mass with a state potential. -/
def finiteStatePairing (mass potential : S → ℝ) : ℝ :=
  ∑ x, mass x * potential x

/-- Difference between forward and baseline expectations of a moving state
potential. -/
def finiteStateTransitionDrift
    (baseline forward : ℝ → S → ℝ)
    (potential : ℝ → S → ℝ) (t : ℝ) : ℝ :=
  finiteStatePairing
    (fun x => forward t x - baseline t x) (potential t)

/-- Affine normalization of a potential whose range lies in `[lower, upper]`.
-/
def rangeNormalizedPotential
    (potential : S → ℝ) (lower upper : ℝ) (x : S) : ℝ :=
  (potential x - lower) / (upper - lower)

/-- The negatively oriented centered score associated with a bounded
potential. It is centered under `baseline` and detects negative
`forward - baseline` drift. -/
def negativeCenteredTransitionScore
    (baseline : ℝ → S → ℝ) (potential : S → ℝ)
    (t : ℝ) (observed : S) : ℝ :=
  finiteStatePairing (baseline t) potential - potential observed

omit [Fintype S] in
/-- Affine range normalization takes values in the unit interval. -/
theorem rangeNormalizedPotential_mem_unitInterval
    (potential : S → ℝ) {lower upper : ℝ}
    (hupper : lower < upper)
    (hrange : ∀ x, lower ≤ potential x ∧ potential x ≤ upper)
    (x : S) :
    rangeNormalizedPotential potential lower upper x ∈
      Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact div_nonneg (sub_nonneg.mpr (hrange x).1)
      (sub_nonneg.mpr hupper.le)
  · change
      (potential x - lower) / (upper - lower) ≤ 1
    rw [div_le_one (sub_pos.mpr hupper)]
    linarith [(hrange x).2]

omit [Fintype S] in
/-- A nonconstant function on a nonempty finite type has strict lower and
upper range endpoints. The witnesses are its finite minimum and maximum. -/
theorem exists_strict_finite_range
    [Finite S] [Nonempty S] (potential : S → ℝ)
    (hnonconstant :
      ∃ x y, potential x ≠ potential y) :
    ∃ lower upper : ℝ,
      lower < upper ∧
      ∀ x, lower ≤ potential x ∧ potential x ≤ upper := by
  letI := Fintype.ofFinite S
  let values : Finset ℝ := Finset.univ.image potential
  have hvalues : values.Nonempty :=
    Finset.univ_nonempty.image potential
  let lower := values.min' hvalues
  let upper := values.max' hvalues
  have hrange :
      ∀ x, lower ≤ potential x ∧ potential x ≤ upper := by
    intro x
    have hx : potential x ∈ values := by
      exact Finset.mem_image.mpr
        ⟨x, Finset.mem_univ x, rfl⟩
    exact ⟨Finset.min'_le values (potential x) hx,
      Finset.le_max' values (potential x) hx⟩
  have hlowerUpper : lower ≤ upper := by
    obtain ⟨x, hx⟩ := hvalues
    exact (Finset.min'_le values x hx).trans
      (Finset.le_max' values x hx)
  refine ⟨lower, upper, lt_of_le_of_ne hlowerUpper ?_, hrange⟩
  intro heq
  obtain ⟨x, y, hxy⟩ := hnonconstant
  apply hxy
  apply le_antisymm
  · calc
      potential x ≤ upper := (hrange x).2
      _ = lower := heq.symm
      _ ≤ potential y := (hrange y).1
  · calc
      potential y ≤ upper := (hrange y).2
      _ = lower := heq.symm
      _ ≤ potential x := (hrange x).1

/-- A constant endpoint value has zero drift between any two unit-mass
transition laws. -/
theorem finiteStateTransitionDrift_const
    (baseline forward : ℝ → S → ℝ)
    (constant : ℝ) (t : ℝ)
    (hbaselineMass : ∑ x, baseline t x = 1)
    (hforwardMass : ∑ x, forward t x = 1) :
    finiteStateTransitionDrift baseline forward
        (fun _ _ => constant) t = 0 := by
  unfold finiteStateTransitionDrift finiteStatePairing
  calc
    (∑ x, (forward t x - baseline t x) * constant) =
        (∑ x, (forward t x - baseline t x)) * constant := by
          rw [Finset.sum_mul]
    _ = 0 := by
      rw [Finset.sum_sub_distrib,
        hforwardMass, hbaselineMass, sub_self, zero_mul]

/-- Subtracting a constant and rescaling preserves a zero-mass pairing. -/
theorem finiteStatePairing_rangeNormalized_of_sum_eq_zero
    (mass potential : S → ℝ) {lower upper : ℝ}
    (hupper : lower < upper)
    (hmass : ∑ x, mass x = 0) :
    finiteStatePairing mass
          (rangeNormalizedPotential potential lower upper) =
      finiteStatePairing mass potential / (upper - lower) := by
  rw [finiteStatePairing, finiteStatePairing]
  calc
    (∑ x, mass x *
          rangeNormalizedPotential potential lower upper x) =
        (∑ x, mass x * (potential x - lower)) /
          (upper - lower) := by
            rw [eq_div_iff (sub_ne_zero.mpr hupper.ne')]
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro x _
            simp only [rangeNormalizedPotential]
            field_simp [sub_ne_zero.mpr hupper.ne']
    _ = (∑ x, mass x * potential x) /
          (upper - lower) := by
            congr 1
            calc
              (∑ x, mass x * (potential x - lower)) =
                  ∑ x,
                    (mass x * potential x - mass x * lower) := by
                      apply Finset.sum_congr rfl
                      intro x _
                      ring
              _ =
                  (∑ x, mass x * potential x) -
                    (∑ x, mass x) * lower := by
                      rw [Finset.sum_sub_distrib,
                        Finset.sum_mul]
              _ = ∑ x, mass x * potential x := by rw [hmass]; ring

/-- The negative centered score has exactly zero baseline expectation. -/
theorem negativeCenteredTransitionScore_baseline_centered
    (baseline : ℝ → S → ℝ) (potential : S → ℝ)
    (t : ℝ) (hmass : ∑ x, baseline t x = 1) :
    ∑ x, baseline t x *
        negativeCenteredTransitionScore baseline potential t x = 0 := by
  unfold negativeCenteredTransitionScore finiteStatePairing
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hmass]
  ring

/-- Under a forward probability mass, the expectation of the negative
centered score is the negative potential drift from baseline to forward. -/
theorem negativeCenteredTransitionScore_forward_expectation
    (baseline forward : ℝ → S → ℝ) (potential : S → ℝ)
    (t : ℝ) (hmass : ∑ x, forward t x = 1) :
    ∑ x, forward t x *
        negativeCenteredTransitionScore baseline potential t x =
      -(finiteStatePairing (forward t) potential -
          finiteStatePairing (baseline t) potential) := by
  unfold negativeCenteredTransitionScore finiteStatePairing
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hmass]
  ring

/-- A centered score built from a `[0,1]` potential is bounded by one under
a nonnegative unit-mass baseline. -/
theorem abs_negativeCenteredTransitionScore_le_one
    (baseline : ℝ → S → ℝ) (potential : S → ℝ)
    (hpotential : ∀ x, potential x ∈ Set.Icc (0 : ℝ) 1)
    (t : ℝ)
    (hnonneg : ∀ x, 0 ≤ baseline t x)
    (hmass : ∑ x, baseline t x = 1)
    (observed : S) :
    |negativeCenteredTransitionScore baseline potential t observed| ≤ 1 := by
  have hmeanNonneg :
      0 ≤ finiteStatePairing (baseline t) potential := by
    exact Finset.sum_nonneg fun x _ =>
      mul_nonneg (hnonneg x) (hpotential x).1
  have hmeanLe :
      finiteStatePairing (baseline t) potential ≤ 1 := by
    calc
      finiteStatePairing (baseline t) potential ≤
          ∑ x, baseline t x * 1 := by
            apply Finset.sum_le_sum
            intro x _
            exact mul_le_mul_of_nonneg_left
              (hpotential x).2 (hnonneg x)
      _ = 1 := by simpa using hmass
  rw [abs_le]
  constructor <;>
    dsimp only [negativeCenteredTransitionScore] <;>
    linarith [(hpotential observed).1, (hpotential observed).2]

/-- A negative power-law drift of an arbitrary finite-range potential becomes
a positive power-law expectation of a fixed bounded score after affine range
normalization. -/
theorem negativeCenteredTransitionScore_powerCharge
    (baseline forward : ℝ → S → ℝ)
    (potential : S → ℝ) {lower upper c : ℝ} {m : ℕ}
    (hupper : lower < upper)
    (hrange : ∀ x, lower ≤ potential x ∧ potential x ≤ upper)
    (hbaselineNonneg : ∀ t x, 0 ≤ baseline t x)
    (hbaselineMass : ∀ t, ∑ x, baseline t x = 1)
    (hforwardMass : ∀ t, ∑ x, forward t x = 1)
    (hcharge :
      ∀ᶠ t in 𝓝[>] (0 : ℝ),
        c * t ^ m ≤
          -(finiteStatePairing (forward t) potential -
            finiteStatePairing (baseline t) potential)) :
    let normalized :=
      rangeNormalizedPotential potential lower upper
    let score :=
      negativeCenteredTransitionScore baseline normalized
    (∀ x, normalized x ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ t x, |score t x| ≤ 1) ∧
      (∀ t, ∑ x, baseline t x * score t x = 0) ∧
      ∀ᶠ t in 𝓝[>] (0 : ℝ),
        (c / (upper - lower)) * t ^ m ≤
          ∑ x, forward t x * score t x := by
  dsimp only
  let normalized :=
    rangeNormalizedPotential potential lower upper
  let score :=
    negativeCenteredTransitionScore baseline normalized
  have hnormalized :
      ∀ x, normalized x ∈ Set.Icc (0 : ℝ) 1 :=
    rangeNormalizedPotential_mem_unitInterval
      potential hupper hrange
  refine ⟨hnormalized, ?_, ?_, ?_⟩
  · intro t x
    exact abs_negativeCenteredTransitionScore_le_one
      baseline normalized hnormalized t
      (hbaselineNonneg t) (hbaselineMass t) x
  · intro t
    exact negativeCenteredTransitionScore_baseline_centered
      baseline normalized t (hbaselineMass t)
  · filter_upwards [hcharge] with t ht
    have hzeroMass :
        ∑ x, (forward t x - baseline t x) = 0 := by
      rw [Finset.sum_sub_distrib,
        hforwardMass t, hbaselineMass t, sub_self]
    have hnormalizedDrift :
        finiteStatePairing (forward t) normalized -
            finiteStatePairing (baseline t) normalized =
          (finiteStatePairing (forward t) potential -
            finiteStatePairing (baseline t) potential) /
              (upper - lower) := by
      have hpairing :=
        finiteStatePairing_rangeNormalized_of_sum_eq_zero
          (fun x => forward t x - baseline t x)
          potential hupper hzeroMass
      change
        (∑ x, forward t x * normalized x) -
              (∑ x, baseline t x * normalized x) =
            ((∑ x, forward t x * potential x) -
              (∑ x, baseline t x * potential x)) /
                (upper - lower)
      simpa only [finiteStatePairing, normalized, sub_mul,
        Finset.sum_sub_distrib] using hpairing
    rw [negativeCenteredTransitionScore_forward_expectation
      baseline forward normalized t (hforwardMass t)]
    rw [hnormalizedDrift]
    have hdenom : 0 < upper - lower := sub_pos.mpr hupper
    rw [div_mul_eq_mul_div]
    calc
      c * t ^ m / (upper - lower) ≤
          -(finiteStatePairing (forward t) potential -
              finiteStatePairing (baseline t) potential) /
            (upper - lower) :=
        (div_le_div_iff_of_pos_right hdenom).2 ht
      _ = -((finiteStatePairing (forward t) potential -
              finiteStatePairing (baseline t) potential) /
            (upper - lower)) := by ring

/-- The scalar dichotomy applied to analytic finite-state transition laws and
a moving value `W(t) = W₀ + t^q H(t)`. No probability-mass assumption is
needed for this analytic reduction. -/
theorem analytic_finiteStateTransitionDrift_dichotomy
    (baseline forward : ℝ → S → ℝ)
    (W H : ℝ → S → ℝ) (W₀ : S → ℝ)
    (g : ℝ → ℝ) {q : ℕ}
    (hq : 0 < q)
    (hbaseline : AnalyticAt ℝ baseline 0)
    (hforward : AnalyticAt ℝ forward 0)
    (hW : ∀ᶠ t in 𝓝 (0 : ℝ),
      W t = fun x => W₀ x + t ^ q * H t x)
    (hH : AnalyticAt ℝ H 0)
    (hg : AnalyticAt ℝ g 0)
    (hineq :
      ∀ᶠ t in 𝓝[>] (0 : ℝ),
        t ^ q * g t +
          (1 - t ^ q) *
            finiteStateTransitionDrift baseline forward W t ≤ 0) :
    let D : ℝ → ℝ := fun t =>
      finiteStateTransitionDrift baseline forward
        (fun _ => W₀) t
    let E : ℝ → ℝ := fun t =>
      finiteStateTransitionDrift baseline forward H t
    (∃ (m : ℕ) (factor : ℝ → ℝ) (c : ℝ),
        m < q ∧
        AnalyticAt ℝ factor 0 ∧
        factor 0 < 0 ∧
        0 < c ∧
        (∀ᶠ t in 𝓝 (0 : ℝ), D t = t ^ m * factor t) ∧
        ∀ᶠ t in 𝓝[>] (0 : ℝ), c * t ^ m ≤ -D t) ∨
      ∃ quotient : ℝ → ℝ,
        AnalyticAt ℝ quotient 0 ∧
        (∀ᶠ t in 𝓝 (0 : ℝ), D t = t ^ q * quotient t) ∧
        g 0 + E 0 + quotient 0 ≤ 0 := by
  dsimp only
  let D : ℝ → ℝ := fun t =>
    finiteStateTransitionDrift baseline forward
      (fun _ => W₀) t
  let E : ℝ → ℝ := fun t =>
    finiteStateTransitionDrift baseline forward H t
  have hD : AnalyticAt ℝ D 0 := by
    apply Finset.univ.analyticAt_fun_sum
    intro x _
    exact
      (((analyticAt_pi_iff.mp hforward) x).sub
        ((analyticAt_pi_iff.mp hbaseline) x)).mul analyticAt_const
  have hE : AnalyticAt ℝ E 0 := by
    apply Finset.univ.analyticAt_fun_sum
    intro x _
    exact
      (((analyticAt_pi_iff.mp hforward) x).sub
        ((analyticAt_pi_iff.mp hbaseline) x)).mul
          ((analyticAt_pi_iff.mp hH) x)
  have hscaled :
      ∀ᶠ t in 𝓝[>] (0 : ℝ),
        discountScaleExpression q g D E t ≤ 0 := by
    filter_upwards [
      hineq,
      hW.filter_mono nhdsWithin_le_nhds] with t ht hWAt
    have hdrift :
        finiteStateTransitionDrift baseline forward W t =
          D t + t ^ q * E t := by
      change
        (∑ x, (forward t x - baseline t x) * W t x) =
          (∑ x, (forward t x - baseline t x) * W₀ x) +
            t ^ q *
              ∑ x, (forward t x - baseline t x) * H t x
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      rw [congrFun hWAt x]
      ring
    rw [discountScaleExpression, ← hdrift]
    exact ht
  exact analytic_discountScale_dichotomy hq hg hD hE hscaled

end CenteredScore

end Math
