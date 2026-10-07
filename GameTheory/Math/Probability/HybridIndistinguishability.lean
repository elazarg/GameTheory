/-
# Uniform hybrid arguments

A polynomial number of intermediate laws preserves indistinguishability when
one negligible bound controls every adjacent advantage at each size. The bound
may depend on the test, but its eventual threshold cannot depend on the hybrid
index. Merely requiring negligible advantage for each fixed index would miss
a distinguishing jump whose location moves with the size parameter.
-/
import GameTheory.Math.Probability.Indistinguishability

noncomputable section

namespace GameTheory.Math.Probability

open GameTheory.Math Filter

universe u
variable {α : Type u}

/-- Each test has one negligible bound valid uniformly over all adjacent
hybrids at each sufficiently large size. -/
structure UniformHybridBound (tests : Set (SampleTest α))
    (H : ℕ → ℕ → PMF α) (steps : ℕ → ℕ) : Prop where
  /-- The same eventual bound applies to every active hybrid index. -/
  bound : ∀ T ∈ tests, ∃ ε : ℕ → ℝ, Negligible ε ∧
    ∀ᶠ κ in atTop, ∀ j < steps κ,
      |T.acceptProb (fun κ => H κ j) κ -
        T.acceptProb (fun κ => H κ (j + 1)) κ| ≤ |ε κ|

/-- The endpoint advantage is bounded by the sum of adjacent advantages. -/
theorem SampleTest.abs_acceptProb_hybrid_le (T : SampleTest α)
    (H : ℕ → ℕ → PMF α) (steps κ : ℕ) :
    |T.acceptProb (fun κ => H κ 0) κ - T.acceptProb (fun κ => H κ steps) κ| ≤
      ∑ j ∈ Finset.range steps,
        |T.acceptProb (fun κ => H κ j) κ -
          T.acceptProb (fun κ => H κ (j + 1)) κ| := by
  let a : ℕ → ℝ := fun j => T.acceptProb (fun κ => H κ j) κ
  change |a 0 - a steps| ≤ ∑ j ∈ Finset.range steps, |a j - a (j + 1)|
  rw [abs_sub_comm, ← Finset.sum_range_sub a]
  simpa only [abs_sub_comm] using Finset.abs_sum_le_sum_abs
    (fun j => a (j + 1) - a j) (Finset.range steps)

/-- Polynomially many uniformly negligible adjacent changes give
indistinguishable endpoint ensembles. -/
theorem indistinguishableBy_of_uniform_hybrid
    {tests : Set (SampleTest α)} {H : ℕ → ℕ → PMF α} {steps : ℕ → ℕ}
    (hsteps : ∃ d : ℕ, ∀ᶠ κ in atTop, steps κ ≤ κ ^ d)
    (h : UniformHybridBound tests H steps) :
    IndistinguishableBy tests (fun κ => H κ 0) (fun κ => H κ (steps κ)) := by
  obtain ⟨d, hd⟩ := hsteps
  intro T hT
  obtain ⟨ε, hε, hbound⟩ := h.bound T hT
  have hpoly : Negligible (fun κ => (κ : ℝ) ^ d * ε κ) := hε.param_pow_mul d
  refine hpoly.of_eventually_abs_le ?_
  filter_upwards [hd, hbound] with κ hκ hgap
  have hcount : (steps κ : ℝ) ≤ (κ : ℝ) ^ d := by exact_mod_cast hκ
  calc
    _ ≤ ∑ j ∈ Finset.range (steps κ),
        |T.acceptProb (fun κ => H κ j) κ -
          T.acceptProb (fun κ => H κ (j + 1)) κ| :=
      T.abs_acceptProb_hybrid_le H (steps κ) κ
    _ ≤ ∑ _j ∈ Finset.range (steps κ), |ε κ| :=
      Finset.sum_le_sum fun j hj => hgap j (Finset.mem_range.mp hj)
    _ = (steps κ : ℝ) * |ε κ| := by simp
    _ ≤ (κ : ℝ) ^ d * |ε κ| := mul_le_mul_of_nonneg_right hcount (abs_nonneg _)
    _ = |(κ : ℝ) ^ d * ε κ| := by
      have hnonneg : 0 ≤ (κ : ℝ) ^ d := by positivity
      simp only [abs_mul, abs_of_nonneg hnonneg]

end GameTheory.Math.Probability
