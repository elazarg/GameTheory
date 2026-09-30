/-
# Negligible functions

A function of a size parameter `κ` is negligible when it vanishes faster than
every inverse polynomial in `κ`. This is Mathlib's superpolynomial decay along
the natural numbers; the name records the cryptographic reading, where `κ` is a
security parameter and the function is a distinguishing advantage.

The decay is two-sided: a negligible function is small in absolute value, so
negligibility of a difference of advantages bounds it in both directions.
-/
import Mathlib.Analysis.Asymptotics.SuperpolynomialDecay
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed

namespace GameTheory.Math

open Filter Asymptotics Topology

/-- `f κ` vanishes faster than every inverse polynomial in `κ`. -/
abbrev Negligible (f : ℕ → ℝ) : Prop :=
  SuperpolynomialDecay atTop (fun κ : ℕ => (κ : ℝ)) f

/-- A negligible function is eventually below every inverse power. -/
theorem Negligible.eventually_abs_lt {f : ℕ → ℝ} (hf : Negligible f) (c : ℕ) :
    ∀ᶠ κ : ℕ in atTop, |f κ| < ((κ : ℝ) ^ c)⁻¹ := by
  have hsmall : ∀ᶠ κ : ℕ in atTop, |(κ : ℝ) ^ c * f κ| < 1 := by
    have := (hf c).eventually (Metric.ball_mem_nhds (0 : ℝ) one_pos)
    filter_upwards [this] with κ hκ
    simpa [Metric.mem_ball, Real.dist_eq] using hκ
  filter_upwards [hsmall, eventually_ge_atTop 1] with κ hκ hone
  have hpos : 0 < (κ : ℝ) ^ c := pow_pos (by exact_mod_cast hone) c
  rw [abs_mul, abs_of_pos hpos] at hκ
  rw [← one_div, lt_div_iff₀ hpos, mul_comm]
  exact hκ

/-- Eventual bounds by every inverse power make a function negligible. -/
theorem negligible_of_eventually_abs_le {f : ℕ → ℝ}
    (hf : ∀ c : ℕ, ∀ᶠ κ : ℕ in atTop, |f κ| ≤ ((κ : ℝ) ^ c)⁻¹) : Negligible f := by
  intro c
  rw [tendsto_zero_iff_abs_tendsto_zero]
  have hdecay : Tendsto (fun κ : ℕ => ((κ : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  refine squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) ?_ hdecay
  filter_upwards [hf (c + 1), eventually_ge_atTop 1] with κ hκ hone
  have hpos : 0 < (κ : ℝ) := by exact_mod_cast hone
  simp only [Function.comp_apply]
  rw [abs_mul, abs_of_pos (pow_pos hpos c)]
  calc
    (κ : ℝ) ^ c * |f κ| ≤ (κ : ℝ) ^ c * ((κ : ℝ) ^ (c + 1))⁻¹ :=
      mul_le_mul_of_nonneg_left hκ (pow_nonneg hpos.le c)
    _ = (κ : ℝ)⁻¹ := by
      rw [pow_succ, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero c hpos.ne'),
        one_mul]

theorem Negligible.add {f g : ℕ → ℝ} (hf : Negligible f) (hg : Negligible g) :
    Negligible (fun κ => f κ + g κ) :=
  SuperpolynomialDecay.add hf hg

theorem Negligible.neg {f : ℕ → ℝ} (hf : Negligible f) :
    Negligible (fun κ => -f κ) := by
  simpa using hf.mul_const (-1)

theorem Negligible.sub {f g : ℕ → ℝ} (hf : Negligible f) (hg : Negligible g) :
    Negligible (fun κ => f κ - g κ) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

theorem negligible_zero : Negligible (fun _ => 0) :=
  superpolynomialDecay_zero _ _

/-- A function eventually bounded by a negligible one is negligible. -/
theorem Negligible.of_eventually_abs_le {f g : ℕ → ℝ} (hg : Negligible g)
    (hfg : ∀ᶠ κ : ℕ in atTop, |f κ| ≤ |g κ|) : Negligible f :=
  hg.trans_eventually_abs_le hfg

/-- `2 ^ (-κ)` is negligible. -/
theorem negligible_inv_two_pow : Negligible fun κ : ℕ => 1 / (2 : ℝ) ^ κ := by
  intro n
  exact (tendsto_pow_const_div_const_pow_of_one_lt n (by norm_num : (1 : ℝ) < 2)).congr
    fun κ => (mul_one_div _ _).symm

end GameTheory.Math
