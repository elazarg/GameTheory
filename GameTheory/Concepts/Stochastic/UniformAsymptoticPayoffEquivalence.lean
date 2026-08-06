/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.UniformPayoffExistenceClosure

/-!
# Uniform equilibrium under asymptotically negligible payoff changes

A fixed-skeleton payoff transformation need not be uniformly small at every
horizon.  It is enough that its effect on every behavior profile—including
every unilateral behavioral deviation—is bounded by one horizon modulus that
tends to zero.

This file isolates that semantic equivalence theorem.  Expected potential
shaping is the intended application: a bounded coboundary contributes only a
bounded endpoint term, hence an `O(1 / T)` finite-average gap.  The telescoping
lemma for a particular transformation remains a separate obligation.
-/

noncomputable section

open Filter

namespace GameTheory
namespace StochasticGame

variable {ι : Type}

/-- A horizon modulus bounds the finite-average payoff change caused by
replacing the stage-payoff table, uniformly over every behavior profile and
player. -/
def HasFiniteAverageGapAtMost
    (G : StochasticGame ι) [Fintype ι]
    (s₀ : G.State)
    (reward : G.State → G.JointAct → ι → ℝ)
    (gap : ℕ → ℝ) : Prop :=
  ∀ (T : ℕ) (σ : G.BehaviorProfile) (who : ι),
    |(G.withStagePayoff reward).finiteAveragePayoff s₀ T σ who -
        G.finiteAveragePayoff s₀ T σ who| ≤ gap T

private theorem eventually_gap_le_quarter
    {gap : ℕ → ℝ} (hgap0 : Tendsto gap atTop (nhds 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Tgap : ℕ, ∀ T, Tgap ≤ T → gap T ≤ ε / 4 := by
  have hquarter : 0 < ε / 4 := by linarith
  obtain ⟨Tgap, hTgap⟩ := eventually_atTop.mp
    ((tendsto_order.mp hgap0).2 (ε / 4) hquarter)
  exact ⟨Tgap, fun T hT => (hTgap T hT).le⟩

/-- A payoff table with a uniformly vanishing finite-average gap has every
uniform-equilibrium payoff of the transformed game as a uniform-equilibrium
payoff of the original game.

The same profile is reused.  One copy of the horizon gap pays for prescribed
play, and two copies pay for a Nash inequality. -/
theorem isUniformEquilibriumPayoff_of_withStagePayoff_of_tendsto_gap_zero
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    (s₀ : G.State)
    (reward : G.State → G.JointAct → ι → ℝ)
    (gap : ℕ → ℝ)
    (hgap : G.HasFiniteAverageGapAtMost s₀ reward gap)
    (hgap0 : Tendsto gap atTop (nhds 0))
    (v : Payoff ι)
    (hUE : (G.withStagePayoff reward).IsUniformEquilibriumPayoff s₀ v) :
    G.IsUniformEquilibriumPayoff s₀ v := by
  intro ε hε
  have hquarter : 0 < ε / 4 := by linarith
  obtain ⟨Tgap, hTgap⟩ := eventually_gap_le_quarter hgap0 hε
  obtain ⟨σ, Tue, hσ⟩ := hUE (ε / 4) hquarter
  let T₀ := max Tgap Tue
  refine ⟨σ, T₀, fun T hT => ?_⟩
  have hTgapT : Tgap ≤ T := (Nat.le_max_left Tgap Tue).trans hT
  have hTueT : Tue ≤ T := (Nat.le_max_right Tgap Tue).trans hT
  have hsmall : gap T ≤ ε / 4 := hTgap T hTgapT
  obtain ⟨hNash, hon⟩ := hσ T hTueT
  constructor
  · intro who dev
    have honGap := hgap T σ who
    have hdevGap := hgap T (Function.update σ who dev) who
    have hnewOnUpper :
        (G.withStagePayoff reward).finiteAveragePayoff s₀ T σ who ≤
          G.finiteAveragePayoff s₀ T σ who + ε / 4 := by
      have h := (abs_le.mp honGap).2
      linarith
    have holdDevUpper :
        G.finiteAveragePayoff s₀ T (Function.update σ who dev) who ≤
          (G.withStagePayoff reward).finiteAveragePayoff s₀ T
            (Function.update σ who dev) who + ε / 4 := by
      have h := (abs_le.mp hdevGap).1
      linarith
    have hnewNash := hNash who dev
    linarith
  · intro who
    have hgame := hgap T σ who
    have hgame' :
        |G.finiteAveragePayoff s₀ T σ who -
          (G.withStagePayoff reward).finiteAveragePayoff s₀ T σ who| ≤
            ε / 4 := by
      rw [abs_sub_comm]
      exact hgame.trans hsmall
    calc
      |G.finiteAveragePayoff s₀ T σ who - v who|
          ≤ |G.finiteAveragePayoff s₀ T σ who -
                (G.withStagePayoff reward).finiteAveragePayoff s₀ T σ who| +
              |(G.withStagePayoff reward).finiteAveragePayoff s₀ T σ who -
                v who| := abs_sub_le _ _ _
      _ ≤ ε / 4 + ε / 4 := add_le_add hgame' (hon who)
      _ ≤ ε := by linarith

/-- The converse transfer: every uniform-equilibrium payoff of the original
game remains one after a fixed-skeleton payoff transformation whose uniform
finite-average gap tends to zero. -/
theorem isUniformEquilibriumPayoff_withStagePayoff_of_tendsto_gap_zero
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    (s₀ : G.State)
    (reward : G.State → G.JointAct → ι → ℝ)
    (gap : ℕ → ℝ)
    (hgap : G.HasFiniteAverageGapAtMost s₀ reward gap)
    (hgap0 : Tendsto gap atTop (nhds 0))
    (v : Payoff ι)
    (hUE : G.IsUniformEquilibriumPayoff s₀ v) :
    (G.withStagePayoff reward).IsUniformEquilibriumPayoff s₀ v := by
  intro ε hε
  have hquarter : 0 < ε / 4 := by linarith
  obtain ⟨Tgap, hTgap⟩ := eventually_gap_le_quarter hgap0 hε
  obtain ⟨σ, Tue, hσ⟩ := hUE (ε / 4) hquarter
  let T₀ := max Tgap Tue
  refine ⟨σ, T₀, fun T hT => ?_⟩
  have hTgapT : Tgap ≤ T := (Nat.le_max_left Tgap Tue).trans hT
  have hTueT : Tue ≤ T := (Nat.le_max_right Tgap Tue).trans hT
  have hsmall : gap T ≤ ε / 4 := hTgap T hTgapT
  obtain ⟨hNash, hon⟩ := hσ T hTueT
  constructor
  · intro who dev
    have honGap := hgap T σ who
    have hdevGap := hgap T (Function.update σ who dev) who
    have holdOnUpper :
        G.finiteAveragePayoff s₀ T σ who ≤
          (G.withStagePayoff reward).finiteAveragePayoff s₀ T σ who +
            ε / 4 := by
      have h := (abs_le.mp honGap).1
      linarith
    have hnewDevUpper :
        (G.withStagePayoff reward).finiteAveragePayoff s₀ T
            (Function.update σ who dev) who ≤
          G.finiteAveragePayoff s₀ T (Function.update σ who dev) who +
            ε / 4 := by
      have h := (abs_le.mp hdevGap).2
      linarith
    have holdNash := hNash who dev
    linarith
  · intro who
    have hgame := hgap T σ who
    calc
      |(G.withStagePayoff reward).finiteAveragePayoff s₀ T σ who - v who|
          ≤ |(G.withStagePayoff reward).finiteAveragePayoff s₀ T σ who -
                G.finiteAveragePayoff s₀ T σ who| +
              |G.finiteAveragePayoff s₀ T σ who - v who| :=
        abs_sub_le _ _ _
      _ ≤ ε / 4 + ε / 4 := add_le_add (hgame.trans hsmall) (hon who)
      _ ≤ ε := by linarith

/-- Exact preservation of a fixed uniform-equilibrium target under a uniformly
vanishing finite-average payoff transformation. -/
theorem isUniformEquilibriumPayoff_withStagePayoff_iff_of_tendsto_gap_zero
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    (s₀ : G.State)
    (reward : G.State → G.JointAct → ι → ℝ)
    (gap : ℕ → ℝ)
    (hgap : G.HasFiniteAverageGapAtMost s₀ reward gap)
    (hgap0 : Tendsto gap atTop (nhds 0))
    (v : Payoff ι) :
    (G.withStagePayoff reward).IsUniformEquilibriumPayoff s₀ v ↔
      G.IsUniformEquilibriumPayoff s₀ v := by
  constructor
  · exact G.isUniformEquilibriumPayoff_of_withStagePayoff_of_tendsto_gap_zero
      s₀ reward gap hgap hgap0 v
  · exact G.isUniformEquilibriumPayoff_withStagePayoff_of_tendsto_gap_zero
      s₀ reward gap hgap hgap0 v

end StochasticGame
end GameTheory
