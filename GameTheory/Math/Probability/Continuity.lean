/-
# Coordinate continuity of finite-law operations

Continuity is stated on real masses, without imposing a topology on the
semantic probability carrier. The parameter space is arbitrary.
-/

import GameTheory.Math.Probability.Convergence

noncomputable section

namespace GameTheory.Math.Probability

variable {X α β : Type*} [TopologicalSpace X]

/-- Finite expectation is jointly continuous in masses and observables. -/
theorem continuous_finDist_expect [Fintype α]
    (law : X → FinDist α) (observable : X → α → ℝ)
    (hlaw : ∀ a, Continuous fun x => (law x).prob a)
    (hobservable : ∀ a, Continuous fun x => observable x a) :
    Continuous fun x => (law x).expect (observable x) := by
  simp_rw [FinDist.expect_eq_sum]
  exact continuous_finsetSum _ fun a _ => (hlaw a).mul (hobservable a)

/-- Finite-source bind is jointly continuous in source and kernel masses. -/
theorem continuous_finDist_bind_prob [Fintype α]
    (law : X → FinDist α) (kernel : X → α → FinDist β)
    (hlaw : ∀ a, Continuous fun x => (law x).prob a)
    (hkernel : ∀ a b, Continuous fun x => (kernel x a).prob b) (b : β) :
    Continuous fun x => ((law x).bind (kernel x)).prob b := by
  simp_rw [FinDist.prob_bind]
  exact continuous_finDist_expect law (fun x a => (kernel x a).prob b)
    hlaw (fun a => hkernel a b)

end GameTheory.Math.Probability
