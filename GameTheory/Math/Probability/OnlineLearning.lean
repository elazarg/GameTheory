/-
# Finite online-learning laws

This is the representation adapter for `GameTheory.Math.OnlineLearning`.
The reusable theorem speaks about a normalized real vector; this module alone
packages that vector as an ordinary probability mass function.
-/

import GameTheory.Math.Probability.ExpectationAlgebra
import GameTheory.Math.OnlineLearning

noncomputable section

namespace GameTheory.Math.Probability.OnlineLearning

open GameTheory.Math.Probability

variable {A : Type*} [Fintype A] [Nonempty A]

/-- Convert a normalized nonnegative real vector to a PMF. -/
private def ofProbabilityVector (probability : A → ℝ)
    (hnonneg : ∀ a, 0 ≤ probability a)
    (hsum : ∑ a, probability a = 1) : PMF A :=
  PMF.ofFintype (fun a => ENNReal.ofReal (probability a)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => hnonneg a), hsum]
    norm_num)

/-- The canonical finite law produced by multiplicative weights. -/
def multiplicativeWeights (eta : ℝ) (gain : ℕ → A → ℝ) (t : ℕ) : PMF A :=
  ofProbabilityVector (OnlineLearning.probability eta gain t)
    (OnlineLearning.probability_nonneg eta gain t)
    (OnlineLearning.sum_probability eta gain t)

@[simp]
theorem toReal_multiplicativeWeights (eta : ℝ) (gain : ℕ → A → ℝ)
    (t : ℕ) (a : A) :
    (multiplicativeWeights eta gain t a).toReal =
      OnlineLearning.probability eta gain t a := by
  simp [multiplicativeWeights, ofProbabilityVector, PMF.ofFintype_apply,
    OnlineLearning.probability_nonneg]

theorem expect_multiplicativeWeights
    (eta : ℝ) (gain : ℕ → A → ℝ) (t : ℕ) (f : A → ℝ)
    (h : PayoffIntegrable (multiplicativeWeights eta gain t) f) :
    expect (multiplicativeWeights eta gain t) f h =
      OnlineLearning.expected eta gain t f := by
  rw [expect_eq_sum]
  simp [OnlineLearning.expected, toReal_multiplicativeWeights]

/-- Exponential weights applied directly to a score vector. -/
def exponentialWeights (eta : ℝ) (score : A → ℝ) : PMF A :=
  ofProbabilityVector (OnlineLearning.scoreProbability eta score)
    (OnlineLearning.scoreProbability_nonneg eta score)
    (OnlineLearning.sum_scoreProbability eta score)

@[simp]
theorem toReal_exponentialWeights (eta : ℝ) (score : A → ℝ) (a : A) :
    (exponentialWeights eta score a).toReal =
      OnlineLearning.scoreProbability eta score a := by
  simp [exponentialWeights, ofProbabilityVector, PMF.ofFintype_apply,
    OnlineLearning.scoreProbability_nonneg]

theorem multiplicativeWeights_eq_exponentialWeights
    (eta : ℝ) (gain : ℕ → A → ℝ) (t : ℕ) :
    multiplicativeWeights eta gain t =
      exponentialWeights eta (OnlineLearning.cumGain gain t) := by
  apply PMF.ext
  intro a
  simp only [multiplicativeWeights, exponentialWeights, ofProbabilityVector,
    PMF.ofFintype_apply]
  exact congrArg ENNReal.ofReal
    (congrFun (OnlineLearning.probability_eq_scoreProbability eta gain t) a)

end GameTheory.Math.Probability.OnlineLearning
