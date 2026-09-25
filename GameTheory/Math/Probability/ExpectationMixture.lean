import GameTheory.Math.Probability.ExpectationAlgebra
import GameTheory.Math.Probability.Mixture

noncomputable section

open scoped BigOperators

namespace GameTheory.Math.Probability

theorem payoffIntegrable_mix {α : Type*} (t : ℝ) (h0 : 0 ≤ t)
    (h1 : t ≤ 1) (μ ν : PMF α) (f : α → ℝ)
    (hμ : PayoffIntegrable μ f) (hν : PayoffIntegrable ν f) :
    PayoffIntegrable (mix t h0 h1 μ ν) f := by
  have hμsum : Summable (fun a => (μ a).toReal * |f a|) := by
    simpa only [PayoffIntegrable] using hμ
  have hνsum : Summable (fun a => (ν a).toReal * |f a|) := by
    simpa only [PayoffIntegrable] using hν
  have hsum : Summable (fun a =>
      t * ((μ a).toReal * |f a|) +
        (1 - t) * ((ν a).toReal * |f a|)) :=
    (hμsum.mul_left t).add (hνsum.mul_left (1 - t))
  have hmixsum : Summable (fun a =>
      (mix t h0 h1 μ ν a).toReal * |f a|) := by
    apply hsum.congr
    intro a
    rw [mix_apply_toReal t h0 h1 μ ν a]
    ring
  simpa only [PayoffIntegrable] using hmixsum

theorem expect_mix {α : Type*} (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (μ ν : PMF α) (f : α → ℝ)
    (hμ : PayoffIntegrable μ f) (hν : PayoffIntegrable ν f) :
    expect (mix t h0 h1 μ ν) f
        (payoffIntegrable_mix t h0 h1 μ ν f hμ hν) =
      t * expect μ f hμ + (1 - t) * expect ν f hν := by
  have hμsum := hμ.summable
  have hνsum := hν.summable
  have hμscale := hμsum.mul_left t
  have hνscale := hνsum.mul_left (1 - t)
  unfold expect
  calc
    (∑' a, (mix t h0 h1 μ ν a).toReal * f a) =
        ∑' a, (t * ((μ a).toReal * f a) +
          (1 - t) * ((ν a).toReal * f a)) := by
      refine tsum_congr fun a => ?_
      rw [mix_apply_toReal t h0 h1 μ ν a]
      ring
    _ = (∑' a, t * ((μ a).toReal * f a)) +
        (∑' a, (1 - t) * ((ν a).toReal * f a)) :=
      Summable.tsum_add hμscale hνscale
    _ = t * expect μ f hμ + (1 - t) * expect ν f hν := by
      rw [tsum_mul_left, tsum_mul_left]
      rfl

private theorem expect_ofReal_tsum {α : Type*} (μ : PMF α)
    (f : α → ℝ) (hf : PayoffIntegrable μ f) (h0 : ∀ a, 0 ≤ f a) :
    ENNReal.ofReal (expect μ f hf) =
      ∑' a, μ a * ENNReal.ofReal (f a) := by
  unfold expect
  rw [ENNReal.ofReal_tsum_of_nonneg]
  · apply tsum_congr
    intro a
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (μ.apply_ne_top a)]
  · intro a
    exact mul_nonneg ENNReal.toReal_nonneg (h0 a)
  · exact hf.summable

/-- Binding a PMF through a mixture of two fixed laws mixes those laws at
the expected weight. The pointwise interval bound supplies integration of
the weight for arbitrary source carriers. -/
theorem bind_mix_expect {α β : Type*} (μ : PMF α)
    (weight : α → ℝ) (h0 : ∀ a, 0 ≤ weight a)
    (h1 : ∀ a, weight a ≤ 1) (ν ξ : PMF β) :
    let hw : PayoffIntegrable μ weight :=
      payoffIntegrable_of_bounded μ weight (C := 1) (fun a => by
        rw [abs_of_nonneg (h0 a)]
        exact h1 a)
    μ.bind (fun a => mix (weight a) (h0 a) (h1 a) ν ξ) =
      mix (expect μ weight hw)
        (expect_nonneg μ weight hw (fun a _ => h0 a))
        (expect_le_const μ weight hw 1 (fun a _ => h1 a)) ν ξ := by
  dsimp only
  let hw : PayoffIntegrable μ weight :=
    payoffIntegrable_of_bounded μ weight (C := 1) (fun a => by
      rw [abs_of_nonneg (h0 a)]
      exact h1 a)
  let hc : PayoffIntegrable μ (fun a => 1 - weight a) :=
    payoffIntegrable_sub (payoffIntegrable_constant μ 1) hw
  have hc0 : ∀ a, 0 ≤ 1 - weight a := fun a => by linarith [h1 a]
  have hcomp : expect μ (fun a => 1 - weight a) hc =
      1 - expect μ weight hw := by
    calc
      expect μ (fun a => 1 - weight a) hc =
          expect μ (fun _ => 1) (payoffIntegrable_constant μ 1) -
            expect μ weight hw := by
        exact expect_sub (payoffIntegrable_constant μ 1) hw
      _ = 1 - expect μ weight hw := by rw [expect_constant]
  ext b
  rw [PMF.bind_apply, mix_apply]
  simp_rw [mix_apply]
  calc
    (∑' a, μ a *
      (ENNReal.ofReal (weight a) * ν b +
        ENNReal.ofReal (1 - weight a) * ξ b)) =
        (∑' a, μ a * ENNReal.ofReal (weight a) * ν b) +
          ∑' a, μ a * ENNReal.ofReal (1 - weight a) * ξ b := by
      rw [← ENNReal.tsum_add]
      apply tsum_congr
      intro a
      rw [mul_add]
      ring
    _ = (∑' a, μ a * ENNReal.ofReal (weight a)) * ν b +
          (∑' a, μ a * ENNReal.ofReal (1 - weight a)) * ξ b := by
      rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_right]
    _ = ENNReal.ofReal (expect μ weight hw) * ν b +
          ENNReal.ofReal (1 - expect μ weight hw) * ξ b := by
      rw [← expect_ofReal_tsum μ weight hw h0,
        ← expect_ofReal_tsum μ (fun a => 1 - weight a) hc hc0, hcomp]
    _ = _ := by ring

end GameTheory.Math.Probability
