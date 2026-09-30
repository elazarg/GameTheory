/-
# Uniform trembles

Mixing a law with the uniform law on a finite carrier reserves the same floor
for every point: a tremble of total mass `t` gives each of `n` points at least
`t / n`. Conversely, a law with that floor is a uniform tremble of some
residual law, so trembles are exactly the laws with a uniform floor.
-/

import GameTheory.Math.Probability.Mixture
import Mathlib.Probability.Distributions.Uniform

noncomputable section

namespace GameTheory.Math.Probability

variable {α : Type*} [Fintype α] [Nonempty α]

/-- Real atom mass of a uniform tremble. -/
theorem mix_uniform_apply_toReal (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) (law : PMF α) (a : α) :
    (mix t h0 h1 (PMF.uniformOfFintype α) law a).toReal =
      t / Fintype.card α + (1 - t) * (law a).toReal := by
  rw [mix_apply_toReal, PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, div_eq_mul_inv]

/-- A uniform tremble of total mass `t` gives every point at least `t / n`. -/
theorem div_card_le_mix_uniform_apply (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) (law : PMF α)
    (a : α) : t / Fintype.card α ≤ (mix t h0 h1 (PMF.uniformOfFintype α) law a).toReal := by
  rw [mix_uniform_apply_toReal]
  exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr h1) ENNReal.toReal_nonneg)

/-- A positive uniform tremble has full support. -/
theorem mem_support_mix_uniform (t : ℝ) (positive : 0 < t) (h1 : t ≤ 1) (law : PMF α)
    (a : α) : a ∈ (mix t positive.le h1 (PMF.uniformOfFintype α) law).support := by
  apply (PMF.mem_support_iff _ a).mpr
  intro zero
  have lower := div_card_le_mix_uniform_apply t positive.le h1 law a
  rw [zero, ENNReal.toReal_zero] at lower
  exact (lower.trans_lt' (div_pos positive (Nat.cast_pos.mpr Fintype.card_pos))).false

/-- **Uniform floors are trembles.** A law giving every point at least `t / n`,
with `t < 1`, is the uniform tremble of total mass `t` of some residual law. -/
theorem exists_mix_uniform_eq_of_floor (law : PMF α) (t : ℝ) (h0 : 0 ≤ t) (h1 : t < 1)
    (floor : ∀ a, t / Fintype.card α ≤ (law a).toReal) :
    ∃ residual : PMF α, mix t h0 h1.le (PMF.uniformOfFintype α) residual = law :=
  exists_mix_eq_of_le law _ t h0 h1 fun a => by
    rw [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ← div_eq_mul_inv]
    exact floor a

end GameTheory.Math.Probability
