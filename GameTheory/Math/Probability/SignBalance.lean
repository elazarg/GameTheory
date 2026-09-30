/-
# Sign balance of centred sums

A sum of `m` independent draws from a centred law of bounded support is
positive about as often as it is negative: the expected sign of the sum is
`O(m ^ (-1 / 8))`. This is the quantitative content of the central limit
theorem needed to compare empirical means of laws with equal expectations, and
it is proved without any Gaussian.

The sign lies below a smooth step that rises over `[-h, 0]`. Lindeberg
replacement moves the step's expectation to the sum of symmetric `±σ` draws
with the same variance, whose expected sign is zero by symmetry, at a cost of
order `m / h ^ 3`. The step exceeds the sign only on `[-h, 0]`, which the
symmetric walk rarely visits. Taking `m = n ^ 8` draws and `h = σ n ^ 3` makes
both errors of order `1 / n`; the reflected law bounds the sign from below.
-/
import GameTheory.Math.Probability.Lindeberg
import GameTheory.Math.Probability.RademacherWalk
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Basic.Real.Sign

noncomputable section

namespace GameTheory.Math.Probability

open Filter Topology

/-! ## A smooth step with bounded third derivative -/

private theorem deriv_eqOn_zero_of_eqOn_const {g : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    {c : ℝ} (hg : Set.EqOn g (fun _ => c) U) : Set.EqOn (deriv g) 0 U := by
  intro y hy
  have hlocal : g =ᶠ[𝓝 y] fun _ => c :=
    Filter.eventually_of_mem (hU.mem_nhds hy) hg
  rw [hlocal.deriv_eq, deriv_const, Pi.zero_apply]

private theorem iteratedDeriv_eqOn_zero_of_eqOn_const {g : ℝ → ℝ} {U : Set ℝ}
    (hU : IsOpen U) {c : ℝ} (hg : Set.EqOn g (fun _ => c) U) :
    ∀ k : ℕ, Set.EqOn (iteratedDeriv (k + 1) g) 0 U := by
  intro k
  induction k with
  | zero =>
    rw [iteratedDeriv_one]
    exact deriv_eqOn_zero_of_eqOn_const hU hg
  | succ k ih =>
    rw [iteratedDeriv_succ]
    exact deriv_eqOn_zero_of_eqOn_const hU ih

/-- Mathlib's smooth transition from `0` on `(-∞, 0]` to `1` on `[1, ∞)` has a
bounded third derivative. -/
theorem exists_smoothTransition_control :
    ∃ M, Nonempty (ThirdOrderControl Real.smoothTransition M) := by
  have hcd : ContDiff ℝ (4 : ℕ∞) Real.smoothTransition := Real.smoothTransition.contDiff
  have hstep : ∀ k : ℕ, k < 4 → ∀ x, HasDerivAt (iteratedDeriv k Real.smoothTransition)
      (iteratedDeriv (k + 1) Real.smoothTransition x) x := by
    intro k hk x
    have hdiff := hcd.differentiable_iteratedDeriv k (by exact_mod_cast hk)
    rw [iteratedDeriv_succ]
    exact (hdiff x).hasDerivAt
  have hcont : Continuous (iteratedDeriv 3 Real.smoothTransition) :=
    continuous_iff_continuousAt.mpr fun x => (hstep 3 (by norm_num) x).continuousAt
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Set.Icc (0 : ℝ) 1) hcont.continuousOn
  have hlow : Set.EqOn (iteratedDeriv 3 Real.smoothTransition) 0 (Set.Iio 0) :=
    iteratedDeriv_eqOn_zero_of_eqOn_const isOpen_Iio
      (fun x hx => Real.smoothTransition.zero_of_nonpos (le_of_lt hx)) 2
  have hhigh : Set.EqOn (iteratedDeriv 3 Real.smoothTransition) 0 (Set.Ioi 1) :=
    iteratedDeriv_eqOn_zero_of_eqOn_const isOpen_Ioi
      (fun x hx => Real.smoothTransition.one_of_one_le (le_of_lt hx)) 2
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 ⟨le_rfl, zero_le_one⟩)
  refine ⟨C, ⟨{
    d1 := iteratedDeriv 1 Real.smoothTransition
    d2 := iteratedDeriv 2 Real.smoothTransition
    d3 := iteratedDeriv 3 Real.smoothTransition
    hasDerivAt_f := fun x => by simpa using hstep 0 (by norm_num) x
    hasDerivAt_d1 := hstep 1 (by norm_num)
    hasDerivAt_d2 := hstep 2 (by norm_num)
    abs_d3_le := fun x => ?_ }⟩⟩
  rcases lt_or_ge x 0 with hx | hx
  · rw [hlow hx, Pi.zero_apply, abs_zero]
    exact hC0
  rcases le_or_gt x 1 with hx' | hx'
  · simpa [Real.norm_eq_abs] using hC x ⟨hx, hx'⟩
  · rw [hhigh hx', Pi.zero_apply, abs_zero]
    exact hC0

/-- A smooth step equal to `-1` below `-h` and to `1` from `0` on. -/
private def upperStep (h x : ℝ) : ℝ :=
  2 * Real.smoothTransition (h⁻¹ * x + 1) + -1

private theorem abs_upperStep_le (h x : ℝ) : |upperStep h x| ≤ 1 := by
  have h0 := Real.smoothTransition.nonneg (h⁻¹ * x + 1)
  have h1 := Real.smoothTransition.le_one (h⁻¹ * x + 1)
  rw [upperStep, abs_le]
  constructor <;> linarith

private theorem abs_sign_le (x : ℝ) : |Real.sign x| ≤ 1 := by
  rcases Real.sign_apply_eq x with h | h | h <;> simp [h]

/-- The step dominates the sign, and exceeds it only on `[-h, h]`, by at most
two. -/
private theorem sign_le_upperStep {h : ℝ} (hh : 0 < h) (x : ℝ) :
    Real.sign x ≤ upperStep h x ∧
      upperStep h x ≤ Real.sign x + 2 * (if |x| ≤ h then 1 else 0) := by
  have h0 := Real.smoothTransition.nonneg (h⁻¹ * x + 1)
  have h1 := Real.smoothTransition.le_one (h⁻¹ * x + 1)
  rcases le_or_gt x (-h) with hx | hx
  · have hneg : x < 0 := by linarith
    have harg : h⁻¹ * x + 1 ≤ 0 := by
      have : h⁻¹ * x ≤ h⁻¹ * (-h) := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hh.le)
      rw [mul_neg, inv_mul_cancel₀ hh.ne'] at this
      linarith
    rw [upperStep, Real.smoothTransition.zero_of_nonpos harg, Real.sign_of_neg hneg]
    constructor
    · norm_num
    · split_ifs <;> norm_num
  rcases lt_or_ge x 0 with hx' | hx'
  · have hin : |x| ≤ h := by rw [abs_of_neg hx']; linarith
    rw [upperStep, Real.sign_of_neg hx']
    simp only [hin, ite_true]
    constructor <;> linarith
  · have harg : 1 ≤ h⁻¹ * x + 1 := by
      have : 0 ≤ h⁻¹ * x := mul_nonneg (inv_nonneg.mpr hh.le) hx'
      linarith
    rw [upperStep, Real.smoothTransition.one_of_one_le harg]
    rcases hx'.lt_or_eq with hpos | hzero
    · rw [Real.sign_of_pos hpos]
      constructor
      · norm_num
      · split_ifs <;> norm_num
    · have hin : |(0 : ℝ)| ≤ h := by rw [abs_zero]; exact hh.le
      rw [← hzero, Real.sign_zero]
      simp only [hin, ite_true]
      constructor <;> norm_num

/-! ## Symmetric sums -/

/-- The sum of draws from a symmetric law has expected sign zero. -/
theorem expect_sign_sampleSum_of_symmetric {ρ : PMF ℝ} (hρ : ρ.map Neg.neg = ρ) (m : ℕ) :
    expect (sampleSum ρ m) Real.sign = 0 := by
  have hsymm : (sampleSum ρ m).map Neg.neg = sampleSum ρ m := by
    rw [← sampleSum_map_neg, hρ]
  have h := expect_map Neg.neg (sampleSum ρ m) Real.sign
  rw [hsymm] at h
  have hneg : (Real.sign ∘ Neg.neg : ℝ → ℝ) = fun x => -Real.sign x := by
    funext x
    exact Real.sign_neg
  rw [hneg, expect_neg] at h
  linarith

/-! ## The sign bound -/

private theorem abs_le_max_left {x R σ : ℝ} (hx : |x| ≤ R) : |x| ≤ max R σ :=
  hx.trans (le_max_left _ _)

/-- For a centred law of bounded support with positive variance, the sum of
`n ^ 8` draws has expected sign at most `C / n`. -/
private theorem exists_expect_sign_sampleSum_le {μ : PMF ℝ} {R : ℝ}
    (hbound : ∀ x ∈ μ.support, |x| ≤ R) (hmean : expect μ id = 0)
    (hvar : 0 < expect μ (fun x => x ^ 2)) :
    ∃ C, ∀ n : ℕ, 1 ≤ n → expect (sampleSum μ (n ^ 8)) Real.sign ≤ C / n := by
  set v := expect μ (fun x => x ^ 2)
  set σ := Real.sqrt v
  have hσ : 0 < σ := Real.sqrt_pos.mpr hvar
  have hσsq : σ ^ 2 = v := Real.sq_sqrt hvar.le
  set ρ := signLaw σ
  set R' := max R σ
  have hμ' : ∀ x ∈ μ.support, |x| ≤ R' := fun x hx => abs_le_max_left (hbound x hx)
  have hρ' : ∀ x ∈ ρ.support, |x| ≤ R' := fun x hx =>
    ((abs_le_of_mem_support_signLaw σ x hx).trans_eq (abs_of_pos hσ)).trans (le_max_right _ _)
  have hmean' : expect μ id = expect ρ id := by
    rw [hmean, expect_signLaw]
    simp
  have hsq' : expect μ (fun x => x ^ 2) = expect ρ (fun x => x ^ 2) := by
    rw [expect_signLaw, neg_sq, ← two_mul, mul_div_cancel_left₀ _ two_ne_zero, hσsq]
  set K := expect μ (fun x => |x| ^ 3) + expect ρ (fun x => |x| ^ 3)
  have hK : 0 ≤ K := add_nonneg (expect_nonneg _ _ fun _ _ => by positivity)
    (expect_nonneg _ _ fun _ _ => by positivity)
  obtain ⟨M, ⟨hΦ⟩⟩ := exists_smoothTransition_control
  have hM : 0 ≤ M := hΦ.nonneg
  refine ⟨2 * M * K / σ ^ 3 + 4, fun n hn => ?_⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set h := σ * (n : ℝ) ^ 3
  have hh : 0 < h := by positivity
  set m := n ^ 8
  let hU := hΦ.affine 2 h⁻¹ 1 (-1)
  have hUfun : (fun x => 2 * Real.smoothTransition (h⁻¹ * x + 1) + -1) = upperStep h := rfl
  have hUbound : ∀ x, |upperStep h x| ≤ 1 := abs_upperStep_le h
  -- Lindeberg replacement of the step's expectation
  have hlind := abs_expect_sampleSum_sub_le hU (B := 1) (fun x => hUbound x) hμ' hρ' hmean'
    hsq' m
  rw [hUfun] at hlind
  have hsignInt : ∀ law : PMF ℝ, PayoffIntegrable law Real.sign :=
    fun law => payoffIntegrable_of_bounded law _ abs_sign_le
  have hstepInt : ∀ law : PMF ℝ, PayoffIntegrable law (upperStep h) :=
    fun law => payoffIntegrable_of_bounded law _ hUbound
  -- the sign lies below the step
  have hS : expect (sampleSum μ m) Real.sign ≤ expect (sampleSum μ m) (upperStep h) :=
    expect_mono (fun x _ => (sign_le_upperStep hh x).1) (hsignInt _) (hstepInt _)
  -- the step exceeds the sign only near zero, where the walk is rare
  have hwindowInt : PayoffIntegrable (sampleSum ρ m)
      (fun x => Real.sign x + 2 * (if |x| ≤ h then (1 : ℝ) else 0)) :=
    payoffIntegrable_of_bounded _ _ (C := 3) fun x => by
      refine (abs_add_le _ _).trans ?_
      have := abs_sign_le x
      split_ifs <;> norm_num <;> linarith
  have hT : expect (sampleSum ρ m) (upperStep h) ≤
      2 * ((sampleSum ρ m).toOuterMeasure {x | |x| ≤ h}).toReal := by
    classical
    have hmono := expect_mono (fun x _ => (sign_le_upperStep hh x).2) (hstepInt _) hwindowInt
    rw [expect_add (hsignInt _) (payoffIntegrable_const_mul
        (payoffIntegrable_of_bounded _ _ (C := 1) fun x => by split_ifs <;> simp)),
      expect_sign_sampleSum_of_symmetric (signLaw_map_neg σ), zero_add, expect_const_mul]
      at hmono
    rw [← expect_indicator]
    exact hmono
  have hwalk : ((sampleSum ρ m).toOuterMeasure {x | |x| ≤ h}).toReal ≤ 2 / n := by
    have hlaw : sampleSum ρ m = (sampleSum (signLaw 1) m).map (σ * ·) := by
      rw [show ρ = (signLaw 1).map (σ * ·) from signLaw_eq_map_mul σ, sampleSum_map_mul]
    have hpre : (σ * ·) ⁻¹' {x : ℝ | |x| ≤ h} = {x | |x| ≤ ((n ^ 3 : ℕ) : ℝ)} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, abs_mul, abs_of_pos hσ, h]
      push_cast
      exact mul_le_mul_iff_right₀ hσ
    rw [hlaw, PMF.toOuterMeasure_map_apply, hpre]
    exact signWalk_window_pow_eight_le n hn
  have hlindUpper := (abs_le.mp hlind).2
  have hconst : (m : ℝ) * (|(2 : ℝ)| * |h⁻¹| ^ 3 * M * K) = 2 * M * K / σ ^ 3 / n := by
    simp only [m, h]
    rw [abs_of_pos two_pos, abs_of_pos (inv_pos.mpr hh)]
    push_cast
    field_simp
    ring
  calc
    expect (sampleSum μ m) Real.sign ≤ expect (sampleSum μ m) (upperStep h) := hS
    _ ≤ expect (sampleSum ρ m) (upperStep h) + (m : ℝ) * (|(2 : ℝ)| * |h⁻¹| ^ 3 * M * K) := by
      linarith
    _ ≤ 2 * (2 / n) + 2 * M * K / σ ^ 3 / n := by
      rw [hconst]
      linarith
    _ = (2 * M * K / σ ^ 3 + 4) / n := by ring

/-- **Sign balance.** For a centred law of bounded support, the sum of `n ^ 8`
independent draws has expected sign `O(1 / n)`. -/
theorem exists_abs_expect_sign_sampleSum_le {μ : PMF ℝ} {R : ℝ}
    (hbound : ∀ x ∈ μ.support, |x| ≤ R) (hmean : expect μ id = 0) :
    ∃ C, ∀ n : ℕ, 1 ≤ n → |expect (sampleSum μ (n ^ 8)) Real.sign| ≤ C / n := by
  by_cases hvar : 0 < expect μ (fun x => x ^ 2)
  · obtain ⟨C₁, hC₁⟩ := exists_expect_sign_sampleSum_le hbound hmean hvar
    have hbound' : ∀ x ∈ (μ.map Neg.neg).support, |x| ≤ R := by
      intro x hx
      rw [PMF.mem_support_map_iff] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      simpa using hbound y hy
    have hmean' : expect (μ.map Neg.neg) id = 0 := by
      rw [expect_map]
      change expect μ (fun x => -id x) = 0
      rw [expect_neg, hmean, neg_zero]
    have hvar' : 0 < expect (μ.map Neg.neg) (fun x => x ^ 2) := by
      rw [expect_map]
      simpa [Function.comp_def] using hvar
    obtain ⟨C₂, hC₂⟩ := exists_expect_sign_sampleSum_le hbound' hmean' hvar'
    refine ⟨max C₁ C₂, fun n hn => abs_le.mpr ⟨?_, ?_⟩⟩
    · have h := hC₂ n hn
      rw [sampleSum_map_neg, expect_map] at h
      have hneg : (Real.sign ∘ Neg.neg : ℝ → ℝ) = fun x => -Real.sign x := by
        funext x
        exact Real.sign_neg
      rw [hneg, expect_neg] at h
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      have : C₂ / n ≤ max C₁ C₂ / n := div_le_div_of_nonneg_right (le_max_right _ _) hnpos.le
      linarith
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      exact (hC₁ n hn).trans (div_le_div_of_nonneg_right (le_max_left _ _) hnpos.le)
  · -- zero variance: every draw is zero
    have hzero : ∀ x ∈ μ.support, x = 0 := by
      intro x hx
      by_contra hne
      have hsqInt : PayoffIntegrable μ (fun x => x ^ 2) :=
        payoffIntegrable_of_support_abs_le hbound _ (C := R ^ 2) fun y hy => by
          rw [abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) hy 2
      have hlt := expect_lt_of_mem_support (payoffIntegrable_constant μ 0) hsqInt
        (fun y _ => sq_nonneg y) x hx (by positivity)
      rw [expect_constant] at hlt
      exact hvar hlt
    have hpure : μ = PMF.pure 0 :=
      pmf_eq_pure_of_support_subset_singleton μ 0 (fun x hx => hzero x hx)
    refine ⟨0, fun n _ => ?_⟩
    have hsum : ∀ k, sampleSum (PMF.pure (0 : ℝ)) k = PMF.pure 0 := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => rw [sampleSum_succ, ih, addLaw_pure_zero]
    rw [hpure, hsum, expect_pure, Real.sign_zero]
    simp

end GameTheory.Math.Probability
