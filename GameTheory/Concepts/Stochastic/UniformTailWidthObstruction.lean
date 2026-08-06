/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.UniformTailWidth

/-!
# Positive tail-width obstruction to uniform equilibrium

The tail-interval characterization has a quantitative contrapositive.  If no
uniform-equilibrium payoff exists, then one positive coordinatewise width is
unavoidable: every profile and every eventual interval containing prescribed
play below all unilateral deviation caps exceeds that width in some player
coordinate.

This is a global behavioral obstruction.  It does not restrict the profile to
stationary, periodic, finite-memory, or public strategies.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

variable {ι : Type}

/-- Nonexistence forces a fixed positive uniform-tail width. -/
theorem exists_pos_tailWidth_of_not_exists_uniformEquilibriumPayoff
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (s₀ : G.State)
    (hno : ¬ ∃ v : Payoff ι, G.IsUniformEquilibriumPayoff s₀ v) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (σ : G.BehaviorProfile) (lower upper : Payoff ι),
        G.HasUniformTailInterval s₀ σ lower upper →
          ∃ who, δ < upper who - lower who := by
  classical
  by_contra hcontra
  push Not at hcontra
  have hthin : G.HasArbitrarilyThinTailIntervals s₀ := by
    intro δ hδ
    obtain ⟨σ, lower, upper, htail, hwidth⟩ := hcontra δ hδ
    exact ⟨σ, lower, upper, hwidth, htail⟩
  exact hno
    ((G.exists_uniformEquilibriumPayoff_iff_hasArbitrarilyThinTailIntervals s₀).2
      hthin)

/-- Equivalent negated form: there is no uniform-equilibrium payoff exactly
when some positive width defeats every proposed uniform tail interval. -/
theorem not_exists_uniformEquilibriumPayoff_iff_exists_pos_tailWidth
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (s₀ : G.State) :
    (¬ ∃ v : Payoff ι, G.IsUniformEquilibriumPayoff s₀ v) ↔
      ∃ δ : ℝ, 0 < δ ∧
        ∀ (σ : G.BehaviorProfile) (lower upper : Payoff ι),
          G.HasUniformTailInterval s₀ σ lower upper →
            ∃ who, δ < upper who - lower who := by
  constructor
  · exact G.exists_pos_tailWidth_of_not_exists_uniformEquilibriumPayoff s₀
  · rintro ⟨δ, hδ, hwidth⟩ ⟨v, hv⟩
    obtain ⟨σ, lower, upper, hthin, htail⟩ :=
      IsUniformEquilibriumPayoff.hasArbitrarilyThinTailIntervals G hv δ hδ
    obtain ⟨who, hwho⟩ := hwidth σ lower upper htail
    exact (not_lt_of_ge (hthin who)) hwho

end StochasticGame
end GameTheory


