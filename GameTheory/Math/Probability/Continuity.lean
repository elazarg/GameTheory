/-
# Coordinate continuity of finite-carrier PMF operations

These statements use real coordinates in the finite-dimensional cases that
need them, without placing a topology on the semantic PMF carrier.
-/

import GameTheory.Math.Probability.Convergence

noncomputable section

namespace GameTheory.Math.Probability

variable {X α β : Type*} [TopologicalSpace X]

/-- Expectation is jointly continuous in finite-carrier masses and payoff
coordinates. -/
theorem continuous_pmf_expect [Fintype α]
    (law : X → PMF α) (observable : X → α → ℝ)
    (hlaw : ∀ value, Continuous fun x => (law x value).toReal)
    (hobservable : ∀ value, Continuous fun x => observable x value) :
    Continuous fun x => expect (law x) (observable x)
      (payoffIntegrable_of_finite (law x) (observable x)) := by
  simp_rw [expect_eq_sum]
  exact continuous_finsetSum _ fun value _ =>
    (hlaw value).mul (hobservable value)

/-- A finite-source PMF bind has continuously varying real mass at each
target atom when source and kernel masses vary continuously. -/
theorem continuous_pmf_bind_mass [Fintype α]
    (law : X → PMF α) (kernel : X → α → PMF β)
    (hlaw : ∀ source, Continuous fun x => (law x source).toReal)
    (hkernel : ∀ source value, Continuous fun x => (kernel x source value).toReal)
    (value : β) :
    Continuous fun x => ((law x).bind (kernel x) value).toReal := by
  have hformula (x : X) :
      ((law x).bind (kernel x) value).toReal =
        ∑ source : α, (law x source).toReal * (kernel x source value).toReal := by
    rw [PMF.bind_apply, ENNReal.tsum_toReal_eq
      (fun source => ENNReal.mul_ne_top ((law x).apply_ne_top source)
        ((kernel x source).apply_ne_top value))]
    simp only [ENNReal.toReal_mul, tsum_fintype]
  simp_rw [hformula]
  exact continuous_finsetSum _ fun source _ =>
    (hlaw source).mul (hkernel source value)

end GameTheory.Math.Probability
