/-
# Finite online-learning laws

This is the representation adapter for `GameTheory.Math.OnlineLearning`.
The reusable theorem speaks about a normalized real vector; this module alone
packages that vector as the library's canonical finite law.
-/

import GameTheory.Math.Probability.FinDist
import GameTheory.Math.OnlineLearning

noncomputable section

namespace GameTheory.Math.Probability.OnlineLearning

open GameTheory.Math

variable {A : Type*} [Fintype A] [Nonempty A]

/-- The canonical finite law produced by multiplicative weights. -/
def multiplicativeWeights (eta : ℝ) (gain : ℕ → A → ℝ) (t : ℕ) : FinDist A :=
  FinDist.ofWeights
    (OnlineLearning.probability eta gain t)
    (OnlineLearning.probability_nonneg eta gain t)
    (OnlineLearning.sum_probability eta gain t)

@[simp]
theorem prob_multiplicativeWeights (eta : ℝ) (gain : ℕ → A → ℝ) (t : ℕ) (a : A) :
    (multiplicativeWeights eta gain t).prob a =
      OnlineLearning.probability eta gain t a := by
  simp [multiplicativeWeights]

theorem expect_multiplicativeWeights
    (eta : ℝ) (gain : ℕ → A → ℝ) (t : ℕ) (f : A → ℝ) :
    (multiplicativeWeights eta gain t).expect f =
      OnlineLearning.expected eta gain t f := by
  rw [FinDist.expect_eq_sum]
  simp [OnlineLearning.expected]

/-- Exponential weights applied directly to a score vector. -/
def exponentialWeights (eta : ℝ) (score : A → ℝ) : FinDist A :=
  FinDist.ofWeights
    (OnlineLearning.scoreProbability eta score)
    (OnlineLearning.scoreProbability_nonneg eta score)
    (OnlineLearning.sum_scoreProbability eta score)

@[simp]
theorem prob_exponentialWeights (eta : ℝ) (score : A → ℝ) (a : A) :
    (exponentialWeights eta score).prob a =
      OnlineLearning.scoreProbability eta score a := by
  simp [exponentialWeights]

theorem multiplicativeWeights_eq_exponentialWeights
    (eta : ℝ) (gain : ℕ → A → ℝ) (t : ℕ) :
    multiplicativeWeights eta gain t =
      exponentialWeights eta (OnlineLearning.cumGain gain t) := by
  apply FinDist.ext_of_prob
  intro a
  rw [prob_multiplicativeWeights, prob_exponentialWeights]
  exact congrFun (OnlineLearning.probability_eq_scoreProbability eta gain t) a

end GameTheory.Math.Probability.OnlineLearning
