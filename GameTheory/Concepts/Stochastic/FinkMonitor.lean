/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.FinkObstruction
import Math.OnlineLearning.AnytimeMultiplicativeWeights

/-!
# Anytime public monitors for Fink transition obstructions

The fixed coordinate-test family from `FinkObstruction` is used as the action set of the
horizon-independent signed multiplicative-weights learner. For any realized successor-state
stream, the learner captures the cumulative score of every destination/sign monitor up to
vanishing average regret.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability
open Filter

/-- The finite monitor family: a destination state and one of its two score orientations. -/
abbrev PMFCoordinateMonitor (Ω : Type) := Ω × Bool

/-- Realized signed gain of a coordinate monitor on an observed outcome stream. -/
def pmfCoordinateMonitorGain {Ω : Type} [DecidableEq Ω]
    (baseline : PMF Ω) (observation : ℕ → Ω)
    (round : ℕ) (monitor : PMFCoordinateMonitor Ω) : ℝ :=
  pmfCoordinateTestScore baseline monitor.1 monitor.2 (observation round)

theorem pmfCoordinateMonitorGain_mem_Icc {Ω : Type} [DecidableEq Ω]
    (baseline : PMF Ω) (observation : ℕ → Ω) :
    ∀ round monitor,
      pmfCoordinateMonitorGain baseline observation round monitor ∈
        Set.Icc (-1 : ℝ) 1 := by
  intro round monitor
  exact abs_le.mp
    (abs_pmfCoordinateTestScore_le_one baseline monitor.1 monitor.2 (observation round))

/-- Total weighted score of the fixed anytime learner on the coordinate-monitor family. -/
def anytimePMFCoordinateMonitorAlgGain {Ω : Type} [Fintype Ω] [Nonempty Ω]
    [DecidableEq Ω] (baseline : PMF Ω) (observation : ℕ → Ω) (T : ℕ) : ℝ :=
  Math.OnlineLearning.anytimeSignedAlgGain
    (pmfCoordinateMonitorGain baseline observation) T

/-- Every fixed coordinate monitor has vanishing positive average regret against the one
    horizon-independent weighted monitor. This statement is pathwise in the observed outcomes. -/
theorem eventually_anytimePMFCoordinateMonitor_regret_div_lt
    {Ω : Type} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
    (baseline : PMF Ω) (observation : ℕ → Ω) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T in atTop, ∀ monitor : PMFCoordinateMonitor Ω,
      (Math.OnlineLearning.cumGain
          (pmfCoordinateMonitorGain baseline observation) T monitor
          - anytimePMFCoordinateMonitorAlgGain baseline observation T) / T < ε := by
  exact Math.OnlineLearning.eventually_anytimeSigned_fixedActionRegret_div_lt
    (pmfCoordinateMonitorGain_mem_Icc baseline observation) hε

/-- Equivalent capture form: every fixed monitor's average realized score is eventually below
    the learner's average weighted score plus any positive tolerance. -/
theorem eventually_pmfCoordinateMonitor_cumGain_div_lt_algGain_div_add
    {Ω : Type} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
    (baseline : PMF Ω) (observation : ℕ → Ω) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T in atTop, ∀ monitor : PMFCoordinateMonitor Ω,
      Math.OnlineLearning.cumGain
          (pmfCoordinateMonitorGain baseline observation) T monitor / T
        < anytimePMFCoordinateMonitorAlgGain baseline observation T / T + ε := by
  filter_upwards [
    eventually_anytimePMFCoordinateMonitor_regret_div_lt baseline observation hε
  ] with T hT
  intro monitor
  have hmonitor := hT monitor
  rw [sub_div] at hmonitor
  linarith

namespace NormalizedFinkSupportTangentObstructionFlow

/-- Pair-valued form of the transition-visible monitor certificate, matching the action type of
    the anytime coordinate-monitor learner. -/
theorem exists_pureDeviationCoordinateMonitor_spec
    (G : StochasticGame ι)
    [Fintype G.State] [DecidableEq G.State]
    [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] {U : ℝ} (z : G.finkDomain U)
    (s : G.State) (who : ι) (d : G.Act who)
    (hkernel :
      G.finkPureDeviationStateKernel z s who d ≠
        G.finkStateKernel z s) :
    ∃ monitor : PMFCoordinateMonitor G.State,
      expect (G.finkStateKernel z s)
          (pmfCoordinateTestScore
            (G.finkStateKernel z s) monitor.1 monitor.2) = 0 ∧
        0 <
          expect (G.finkPureDeviationStateKernel z s who d)
            (pmfCoordinateTestScore
              (G.finkStateKernel z s) monitor.1 monitor.2) ∧
        ∀ x,
          |pmfCoordinateTestScore
            (G.finkStateKernel z s) monitor.1 monitor.2 x| ≤ 1 := by
  obtain ⟨t, positive, hbaseline, hpositive, hbound⟩ :=
    exists_pureDeviationCoordinateTestScore_spec G z s who d hkernel
  exact ⟨(t, positive), hbaseline, hpositive, hbound⟩

end NormalizedFinkSupportTangentObstructionFlow

end StochasticGame
end GameTheory
