/-
# Lindeberg replacement

Replacing the summands of an independent sum one at a time by summands with
the same first two moments changes the expectation of a smooth bounded function
by at most a third-derivative bound times the third absolute moments of the two
summands, once per replaced summand. The quadratic Taylor polynomial of the
function has the same expectation under both summands, so only the cubic
Taylor remainder contributes.

`ThirdOrderControl f M` carries explicit first, second, and third derivatives
of `f` with the third bounded by `M`; it is stable under affine changes of
argument and value, which is how test functions are rescaled.
-/
import GameTheory.Math.Probability.SampleSum
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section

namespace GameTheory.Math.Probability

/-- A real function with explicit derivatives up to third order, the third
bounded by `M`. -/
structure ThirdOrderControl (f : ℝ → ℝ) (M : ℝ) where
  /-- The first derivative. -/
  d1 : ℝ → ℝ
  /-- The second derivative. -/
  d2 : ℝ → ℝ
  /-- The third derivative. -/
  d3 : ℝ → ℝ
  hasDerivAt_f : ∀ x, HasDerivAt f (d1 x) x
  hasDerivAt_d1 : ∀ x, HasDerivAt d1 (d2 x) x
  hasDerivAt_d2 : ∀ x, HasDerivAt d2 (d3 x) x
  abs_d3_le : ∀ x, |d3 x| ≤ M

namespace ThirdOrderControl

variable {f : ℝ → ℝ} {M : ℝ}

theorem nonneg (hf : ThirdOrderControl f M) : 0 ≤ M :=
  (abs_nonneg _).trans (hf.abs_d3_le 0)

private theorem abs_sub_le_of_hasDerivAt {g g' : ℝ → ℝ} (hg : ∀ x, HasDerivAt g (g' x) x)
    (t C : ℝ) (hC : ∀ u ∈ Set.uIcc 0 t, |g' u| ≤ C) : |g t - g 0| ≤ C * |t| := by
  have := (convex_uIcc (0 : ℝ) t).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := g) (f' := g') (fun x _ => (hg x).hasDerivWithinAt) hC Set.left_mem_uIcc
    Set.right_mem_uIcc
  simpa [Real.norm_eq_abs] using this

private theorem abs_le_of_mem_uIcc_zero {u t : ℝ} (hu : u ∈ Set.uIcc 0 t) : |u| ≤ |t| := by
  simpa using Set.abs_sub_left_of_mem_uIcc hu

private theorem hasDerivAt_shift {g g' : ℝ → ℝ} (hg : ∀ x, HasDerivAt g (g' x) x) (b s : ℝ) :
    HasDerivAt (fun t => g (b + t)) (g' (b + s)) s := by
  exact ((hg (b + s)).comp s ((hasDerivAt_id s).const_add b)).congr_deriv (by simp)

/-- Taylor's theorem with a cubic remainder. -/
theorem abs_taylor_remainder_le (hf : ThirdOrderControl f M) (b x : ℝ) :
    |f (b + x) - (f b + hf.d1 b * x + hf.d2 b / 2 * x ^ 2)| ≤ M * |x| ^ 3 := by
  have h2 : ∀ t, |hf.d2 (b + t) - hf.d2 b| ≤ M * |t| := by
    intro t
    simpa using abs_sub_le_of_hasDerivAt (hasDerivAt_shift hf.hasDerivAt_d2 b) t M
      (fun u _ => hf.abs_d3_le _)
  have h1 : ∀ t, |hf.d1 (b + t) - hf.d1 b - hf.d2 b * t| ≤ M * |t| ^ 2 := by
    intro t
    have hderiv : ∀ s, HasDerivAt (fun s => hf.d1 (b + s) - hf.d1 b - hf.d2 b * s)
        (hf.d2 (b + s) - hf.d2 b) s := by
      intro s
      exact (((hasDerivAt_shift hf.hasDerivAt_d1 b s).sub_const (hf.d1 b)).sub
        ((hasDerivAt_id s).const_mul (hf.d2 b))).congr_deriv (by simp)
    have := abs_sub_le_of_hasDerivAt hderiv t (M * |t|)
      (fun u hu => (h2 u).trans (mul_le_mul_of_nonneg_left (abs_le_of_mem_uIcc_zero hu)
        hf.nonneg))
    simpa [pow_two, mul_assoc] using this
  have hderiv : ∀ s, HasDerivAt
      (fun s => f (b + s) - (f b + hf.d1 b * s + hf.d2 b / 2 * s ^ 2))
      (hf.d1 (b + s) - hf.d1 b - hf.d2 b * s) s := by
    intro s
    have := (hasDerivAt_shift hf.hasDerivAt_f b s).sub
      (((hasDerivAt_id s).const_mul (hf.d1 b)).const_add (f b) |>.add
        ((hasDerivAt_pow 2 s).const_mul (hf.d2 b / 2)))
    exact this.congr_deriv (by norm_num; ring)
  have := abs_sub_le_of_hasDerivAt hderiv x (M * |x| ^ 2)
    (fun u hu => (h1 u).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg _) (abs_le_of_mem_uIcc_zero hu) 2) hf.nonneg))
  simpa [pow_succ, mul_assoc] using this

/-- Rescaling argument and value multiplies the third-derivative bound by
`|a| * |b| ^ 3`. -/
def affine (hf : ThirdOrderControl f M) (a b c e : ℝ) :
    ThirdOrderControl (fun x => a * f (b * x + c) + e) (|a| * |b| ^ 3 * M) where
  d1 x := a * (hf.d1 (b * x + c) * b)
  d2 x := a * (hf.d2 (b * x + c) * b * b)
  d3 x := a * (hf.d3 (b * x + c) * b * b * b)
  hasDerivAt_f x := by
    have hinner : HasDerivAt (fun x => b * x + c) b x := by
      simpa using ((hasDerivAt_id x).const_mul b).add_const c
    exact ((hf.hasDerivAt_f (b * x + c)).comp x hinner |>.const_mul a).add_const e
  hasDerivAt_d1 x := by
    have hinner : HasDerivAt (fun x => b * x + c) b x := by
      simpa using ((hasDerivAt_id x).const_mul b).add_const c
    exact (((hf.hasDerivAt_d1 (b * x + c)).comp x hinner).mul_const b).const_mul a
  hasDerivAt_d2 x := by
    have hinner : HasDerivAt (fun x => b * x + c) b x := by
      simpa using ((hasDerivAt_id x).const_mul b).add_const c
    exact ((((hf.hasDerivAt_d2 (b * x + c)).comp x hinner).mul_const b).mul_const b).const_mul a
  abs_d3_le x := by
    rw [abs_mul, abs_mul, abs_mul, abs_mul]
    have := hf.abs_d3_le (b * x + c)
    calc
      |a| * (|hf.d3 (b * x + c)| * |b| * |b| * |b|) = |a| * |b| ^ 3 * |hf.d3 (b * x + c)| := by
        ring
      _ ≤ |a| * |b| ^ 3 * M := mul_le_mul_of_nonneg_left this (by positivity)

end ThirdOrderControl

section Replacement

variable {f : ℝ → ℝ} {M B R : ℝ}

/-- The expectation of a quadratic under a law of bounded support is determined
by the first two moments. -/
theorem expect_quadratic {μ : PMF ℝ} (hμ : ∀ x ∈ μ.support, |x| ≤ R) (c₀ c₁ c₂ : ℝ) :
    expect μ (fun x => c₀ + c₁ * x + c₂ * x ^ 2) =
      c₀ + c₁ * expect μ id + c₂ * expect μ (fun x => x ^ 2) := by
  have hlin : PayoffIntegrable μ (fun x => c₁ * x) :=
    payoffIntegrable_of_support_abs_le hμ _ (C := |c₁| * R) fun x hx => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hx (abs_nonneg _)
  have hsq : PayoffIntegrable μ (fun x => c₂ * x ^ 2) :=
    payoffIntegrable_of_support_abs_le hμ _ (C := |c₂| * R ^ 2) fun x hx => by
      rw [abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hx 2) (abs_nonneg _)
  rw [expect_add (payoffIntegrable_add (payoffIntegrable_constant μ _) hlin) hsq,
    expect_add (payoffIntegrable_constant μ _) hlin, expect_constant, expect_const_mul,
    expect_const_mul]
  rfl

private theorem abs_expect_le_of_abs_le {μ : PMF ℝ}
    {g h : ℝ → ℝ} (hg : PayoffIntegrable μ g) (hh : PayoffIntegrable μ h)
    (hgh : ∀ x ∈ μ.support, |g x| ≤ h x) : |expect μ g| ≤ expect μ h := by
  have hupper := expect_mono (fun x hx => (abs_le.mp (hgh x hx)).2) hg hh
  have hlower := expect_mono (fun x hx => (abs_le.mp (hgh x hx)).1) (payoffIntegrable_neg hh) hg
  rw [expect_neg] at hlower
  exact abs_le.mpr ⟨hlower, hupper⟩

/-- Averaging `f (a + ·)` separates the quadratic Taylor part from the
remainder. -/
private theorem expect_shift_eq (hf : ThirdOrderControl f M) (hB : ∀ x, |f x| ≤ B)
    {μ : PMF ℝ} (hμ : ∀ x ∈ μ.support, |x| ≤ R) (a : ℝ) :
    expect μ (fun x => f (a + x)) =
      (f a + hf.d1 a * expect μ id + hf.d2 a / 2 * expect μ (fun x => x ^ 2)) +
        expect μ (fun x => f (a + x) - (f a + hf.d1 a * x + hf.d2 a / 2 * x ^ 2)) := by
  have hq : PayoffIntegrable μ (fun x => f a + hf.d1 a * x + hf.d2 a / 2 * x ^ 2) :=
    payoffIntegrable_of_support_abs_le hμ _
      (C := |f a| + |hf.d1 a| * R + |hf.d2 a / 2| * R ^ 2) fun x hx => by
        refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans ?_) ?_)
        · rw [abs_mul]
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hx (abs_nonneg _))
        · rw [abs_mul, abs_pow]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hx 2)
            (abs_nonneg _)
  have hr : PayoffIntegrable μ
      (fun x => f (a + x) - (f a + hf.d1 a * x + hf.d2 a / 2 * x ^ 2)) :=
    payoffIntegrable_sub (payoffIntegrable_of_bounded μ _ fun x => hB (a + x)) hq
  rw [← expect_quadratic hμ, ← expect_add hq hr]
  apply expect_congr_on_support
  intro x _
  ring

/-- **One Lindeberg swap**: replacing one independent summand by one with the
same first two moments. -/
theorem abs_expect_addLaw_sub_le (hf : ThirdOrderControl f M) (hB : ∀ x, |f x| ≤ B)
    (A : PMF ℝ) {μ ρ : PMF ℝ} (hμ : ∀ x ∈ μ.support, |x| ≤ R)
    (hρ : ∀ x ∈ ρ.support, |x| ≤ R) (hmean : expect μ id = expect ρ id)
    (hsq : expect μ (fun x => x ^ 2) = expect ρ (fun x => x ^ 2)) :
    |expect (addLaw A μ) f - expect (addLaw A ρ) f| ≤
      M * (expect μ (fun x => |x| ^ 3) + expect ρ (fun x => |x| ^ 3)) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hcube : ∀ {ν : PMF ℝ}, (∀ x ∈ ν.support, |x| ≤ R) →
      ∀ a, |expect ν (fun x => f (a + x) - (f a + hf.d1 a * x + hf.d2 a / 2 * x ^ 2))| ≤
        M * expect ν (fun x => |x| ^ 3) := by
    intro ν hν a
    have hcubeInt : PayoffIntegrable ν (fun x => |x| ^ 3) :=
      payoffIntegrable_of_support_abs_le hν _ (C := R ^ 3) fun x hx => by
        rw [abs_pow, abs_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hx 3
    have hq : PayoffIntegrable ν (fun x => f a + hf.d1 a * x + hf.d2 a / 2 * x ^ 2) :=
      payoffIntegrable_of_support_abs_le hν _
        (C := |f a| + |hf.d1 a| * R + |hf.d2 a / 2| * R ^ 2) fun x hx => by
          refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans ?_) ?_)
          · rw [abs_mul]
            exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hx (abs_nonneg _))
          · rw [abs_mul, abs_pow]
            exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hx 2)
              (abs_nonneg _)
    rw [← expect_const_mul]
    exact abs_expect_le_of_abs_le
      (payoffIntegrable_sub (payoffIntegrable_of_bounded ν _ fun x => hB (a + x)) hq)
      (payoffIntegrable_const_mul hcubeInt)
      (fun x _ => hf.abs_taylor_remainder_le a x)
  have hpoint : ∀ a, |expect μ (fun x => f (a + x)) - expect ρ (fun x => f (a + x))| ≤
      M * (expect μ (fun x => |x| ^ 3) + expect ρ (fun x => |x| ^ 3)) := by
    intro a
    rw [expect_shift_eq hf hB hμ a, expect_shift_eq hf hB hρ a, hmean, hsq, add_sub_add_left_eq_sub,
      mul_add]
    exact (abs_sub _ _).trans (add_le_add (hcube hμ a) (hcube hρ a))
  have hinner : ∀ ν : PMF ℝ, PayoffIntegrable A (fun a => expect ν (fun x => f (a + x))) :=
    fun ν => payoffIntegrable_of_bounded A _ fun a =>
      expect_abs_le_of_bounded hB0 fun x => hB (a + x)
  rw [expect_addLaw A μ f (payoffIntegrable_of_bounded _ _ hB),
    expect_addLaw A ρ f (payoffIntegrable_of_bounded _ _ hB),
    ← expect_sub (hinner μ) (hinner ρ)]
  exact expect_abs_le_of_bounded
    (mul_nonneg hf.nonneg (add_nonneg (expect_nonneg _ _ fun _ _ => by positivity)
      (expect_nonneg _ _ fun _ _ => by positivity))) hpoint

/-- **Lindeberg replacement**: replacing all `m` summands, each swap costing the
third-order term once. -/
theorem abs_expect_sampleSum_sub_le (hf : ThirdOrderControl f M) (hB : ∀ x, |f x| ≤ B)
    {μ ρ : PMF ℝ} (hμ : ∀ x ∈ μ.support, |x| ≤ R) (hρ : ∀ x ∈ ρ.support, |x| ≤ R)
    (hmean : expect μ id = expect ρ id)
    (hsq : expect μ (fun x => x ^ 2) = expect ρ (fun x => x ^ 2)) (m : ℕ) :
    |expect (sampleSum μ m) f - expect (sampleSum ρ m) f| ≤
      m * (M * (expect μ (fun x => |x| ^ 3) + expect ρ (fun x => |x| ^ 3))) := by
  set K := M * (expect μ (fun x => |x| ^ 3) + expect ρ (fun x => |x| ^ 3))
  suffices h : ∀ A : PMF ℝ,
      |expect (addLaw A (sampleSum μ m)) f - expect (addLaw A (sampleSum ρ m)) f| ≤ m * K by
    simpa using h (PMF.pure 0)
  induction m with
  | zero => intro A; simp
  | succ m ih =>
    intro A
    have hμsplit : addLaw A (sampleSum μ (m + 1)) = addLaw (addLaw A μ) (sampleSum μ m) := by
      rw [sampleSum_succ, addLaw_comm (sampleSum μ m), addLaw_assoc]
    have hρsplit : addLaw A (sampleSum ρ (m + 1)) = addLaw (addLaw A ρ) (sampleSum ρ m) := by
      rw [sampleSum_succ, addLaw_comm (sampleSum ρ m), addLaw_assoc]
    have hswap : ∀ ν : PMF ℝ,
        addLaw (addLaw A ν) (sampleSum ρ m) = addLaw (addLaw A (sampleSum ρ m)) ν := by
      intro ν
      rw [addLaw_assoc, addLaw_comm ν, ← addLaw_assoc]
    rw [hμsplit, hρsplit]
    calc
      |expect (addLaw (addLaw A μ) (sampleSum μ m)) f -
            expect (addLaw (addLaw A ρ) (sampleSum ρ m)) f| ≤
          |expect (addLaw (addLaw A μ) (sampleSum μ m)) f -
              expect (addLaw (addLaw A μ) (sampleSum ρ m)) f| +
            |expect (addLaw (addLaw A μ) (sampleSum ρ m)) f -
              expect (addLaw (addLaw A ρ) (sampleSum ρ m)) f| := abs_sub_le _ _ _
      _ ≤ m * K + K := by
        refine add_le_add (ih (addLaw A μ)) ?_
        rw [hswap μ, hswap ρ]
        exact abs_expect_addLaw_sub_le hf hB _ hμ hρ hmean hsq
      _ = ((m + 1 : ℕ) : ℝ) * K := by push_cast; ring

end Replacement

end GameTheory.Math.Probability
