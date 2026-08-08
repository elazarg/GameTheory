/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Examples.BigMatch.Markov
import GameTheory.Concepts.Stochastic.UniformEquilibrium.VanishingDiscount.Fink.MarkovEndpoint

/-!
# The Big Match has no scheduled-Markov uniform equilibrium at its value

Every calendar-time state-Markov stopping schedule of the maximizer has a
single minimizer behavior response that eventually drives the maximizer's
average payoff arbitrarily close to zero. Consequently no such scheduled
profile can witness the Big Match value `(1/2, -1/2)` as a uniform
equilibrium payoff.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace BigMatch

open Filter

/-- Any scheduled-Markov maximizer rule admits one fixed minimizer behavior
response whose actual long-horizon payoff to the maximizer is below any
prescribed positive bound. -/
theorem exists_minimizer_deviation_eventually_payoff_lt
    (x : ℕ → game.StationaryMixedProfile) {ε : ℝ} (hε : 0 < ε) :
    ∃ dev : game.BehaviorStrategy true, ∀ᶠ T in atTop,
      game.finiteAveragePayoff .live T
          (Function.update (game.scheduledMarkovBehaviorProfile x) true dev)
          false < ε := by
  have hresponse :=
    MarkovScalar.exists_response_eventually_average_lt_unconditional
      (stopProbability x) (stopProbability_nonneg x)
        (stopProbability_le_one x) hε
  rcases hresponse with ⟨N, hcutoff⟩ | hright
  · refine ⟨cutoffMinimizer N, ?_⟩
    filter_upwards [hcutoff] with T hT
    change game.finiteAveragePayoff .live T
      (Function.update (timeStateBehaviorProfile x) true (cutoffMinimizer N))
        false < ε
    rw [finiteAveragePayoff_update_cutoffMinimizer]
    exact hT
  · refine ⟨allRightMinimizer, ?_⟩
    filter_upwards [hright] with T hT
    change game.finiteAveragePayoff .live T
      (Function.update (timeStateBehaviorProfile x) true allRightMinimizer)
        false < ε
    rw [finiteAveragePayoff_update_allRightMinimizer]
    exact hT

/-- Calendar-time state-Markov profiles cannot witness the classical Big
Match uniform value `(1/2, -1/2)`. -/
theorem not_isUniformScheduledMarkovEquilibriumPayoff_half :
    ¬ game.IsUniformScheduledMarkovEquilibriumPayoff .live
      (fun who => if who then -(1 / 2 : ℝ) else (1 / 2 : ℝ)) := by
  intro huniform
  have hε : (0 : ℝ) < 1 / 8 := by norm_num
  obtain ⟨x, T₀, hx⟩ := huniform (1 / 8) hε
  obtain ⟨dev, hdev⟩ :=
    exists_minimizer_deviation_eventually_payoff_lt x hε
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.1 hdev
  let T := max T₀ T₁
  have hT₀ : T₀ ≤ T := le_max_left _ _
  have hT₁' : T₁ ≤ T := le_max_right _ _
  obtain ⟨hnash, hnear⟩ := hx T hT₀
  have hlow := hT₁ T hT₁'
  have hnearMax :
      |game.finiteAveragePayoff .live T
          (game.scheduledMarkovBehaviorProfile x) false - (1 / 2 : ℝ)| ≤
        1 / 8 := by
    simpa using hnear false
  have hmaxLower := (abs_le.mp hnearMax).1
  have hnashMin := hnash true dev
  have hzeroOn := finiteAveragePayoff_minimizer .live T
    (game.scheduledMarkovBehaviorProfile x)
  have hzeroDev := finiteAveragePayoff_minimizer .live T
    (Function.update (game.scheduledMarkovBehaviorProfile x) true dev)
  linarith

end BigMatch
end StochasticGame
end GameTheory
