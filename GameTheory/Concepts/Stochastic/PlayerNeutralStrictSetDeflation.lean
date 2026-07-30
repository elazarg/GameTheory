/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.PlayerNeutralStrictSetBudget
import Math.Probability.AdaptiveOccupationSetDeflation

/-!
# Asymptotic deflation of the player-neutral strict set

The complete strict set selected by a player-neutral leading-drift
certificate has a horizon-uniform occupation budget.  Consequently its
expected pure use and expected predictable mixed mass, divided by the
horizon, converge to zero.  The same holds for every cumulative contribution
whose absolute value is pathwise dominated by a fixed multiple of the
corresponding strict-set occupation.

This is the asymptotic accounting conclusion of strict separation.  It does
not construct a strategy on the complementary zero-drift family or assert
that deleting the strict set preserves incentives.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace StochasticGame

open Filter Math Math.Probability
open Math.Probability.AnalyticScaledChargedOccupationPotential

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

namespace AnalyticBellmanGerm
namespace PlayerNeutralStrictLeadingDrift

local instance strictSetOccupationIndexDecidableEq
    (germ : G.AnalyticBellmanGerm) (who : ι) :
    DecidableEq (germ.PlayerNeutralOccupationIndex who) :=
  Classical.decEq _

variable
    {germ : G.AnalyticBellmanGerm}
    {B : G.State → Payoff ι} {who : ι}
    {P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who)}
    {anchor : G.State}
    {jet : GaugeFixedPotentialJet P anchor}

/-- Expected total pure use of the complete strict set before horizon `T`. -/
def strictSetExpectedUse
    (C : germ.PlayerNeutralStrictLeadingDrift B who jet)
    (initial : G.State)
    (choice :
      ∀ n, (Fin (n + 1) → G.State) →
        germ.PlayerNeutralOccupationIndex who)
    (T : ℕ) : ℝ :=
  transitionSetExpectedUse initial
    (germ.playerNeutralOccupationKernel who)
    choice C.strictIndexSet T

/-- Expected predictable mixed mass placed on the complete strict set before
horizon `T`. -/
def strictSetExpectedMass
    (C : germ.PlayerNeutralStrictLeadingDrift B who jet)
    (initial : G.State)
    (selection :
      ∀ n, (Fin (n + 1) → G.State) →
        PMF (germ.PlayerNeutralOccupationIndex who))
    (T : ℕ) : ℝ :=
  transitionSetExpectedMass initial
    (germ.playerNeutralOccupationKernel who)
    selection C.strictIndexSet T

/-- The expected total number of pure uses of every strictly separated
player-neutral column is sublinear. -/
theorem strictSetExpectedUse_isAsymptoticallySublinear
    (C : germ.PlayerNeutralStrictLeadingDrift B who jet)
    (initial : G.State)
    (choice :
      ∀ n, (Fin (n + 1) → G.State) →
        germ.PlayerNeutralOccupationIndex who)
    (source_compatible :
      ∀ n history,
        germ.playerNeutralOccupationSource who (choice n history) =
          history (Fin.last n)) :
    IsAsymptoticallySublinear
      (C.strictSetExpectedUse initial choice) := by
  change IsAsymptoticallySublinear
    (transitionSetExpectedUse initial
      (germ.playerNeutralOccupationKernel who)
      choice C.strictIndexSet)
  exact transitionSetExpectedUse_isAsymptoticallySublinear
      initial
      (germ.playerNeutralOccupationKernel who)
      (germ.playerNeutralOccupationSource who)
      choice C.strictIndexSet C.potential C.strictMargin_pos C.bounded
      source_compatible
      (by
        intro index
        simpa only [normalizedDrift] using C.drift_nonneg index)
      (by
        intro index index_mem
        exact C.strictMargin_le_normalizedDrift index_mem)

/-- Direct ratio form: expected total pure strict-set use divided by the
horizon converges to zero. -/
theorem tendsto_strictSetExpectedUse_div_horizon_zero
    (C : germ.PlayerNeutralStrictLeadingDrift B who jet)
    (initial : G.State)
    (choice :
      ∀ n, (Fin (n + 1) → G.State) →
        germ.PlayerNeutralOccupationIndex who)
    (source_compatible :
      ∀ n history,
        germ.playerNeutralOccupationSource who (choice n history) =
          history (Fin.last n)) :
    Tendsto
      (fun T : ℕ => C.strictSetExpectedUse initial choice T / T)
      atTop (nhds 0) := by
  simpa only [IsAsymptoticallySublinear, div_eq_mul_inv, mul_comm] using
    C.strictSetExpectedUse_isAsymptoticallySublinear
      initial choice source_compatible

/-- The expected predictable mass placed on every strictly separated
player-neutral column is sublinear. -/
theorem strictSetExpectedMass_isAsymptoticallySublinear
    (C : germ.PlayerNeutralStrictLeadingDrift B who jet)
    (initial : G.State)
    (selection :
      ∀ n, (Fin (n + 1) → G.State) →
        PMF (germ.PlayerNeutralOccupationIndex who))
    (source_compatible :
      ∀ n history index,
        selection n history index ≠ 0 →
          germ.playerNeutralOccupationSource who index =
            history (Fin.last n)) :
    IsAsymptoticallySublinear
      (C.strictSetExpectedMass initial selection) := by
  change IsAsymptoticallySublinear
    (transitionSetExpectedMass initial
      (germ.playerNeutralOccupationKernel who)
      selection C.strictIndexSet)
  exact transitionSetExpectedMass_isAsymptoticallySublinear
      initial
      (germ.playerNeutralOccupationKernel who)
      (germ.playerNeutralOccupationSource who)
      selection C.strictIndexSet C.potential C.strictMargin_pos C.bounded
      source_compatible
      (by
        intro index
        simpa only [normalizedDrift] using C.drift_nonneg index)
      (by
        intro index index_mem
        exact C.strictMargin_le_normalizedDrift index_mem)

/-- Direct ratio form: expected predictable strict-set mass divided by the
horizon converges to zero. -/
theorem tendsto_strictSetExpectedMass_div_horizon_zero
    (C : germ.PlayerNeutralStrictLeadingDrift B who jet)
    (initial : G.State)
    (selection :
      ∀ n, (Fin (n + 1) → G.State) →
        PMF (germ.PlayerNeutralOccupationIndex who))
    (source_compatible :
      ∀ n history index,
        selection n history index ≠ 0 →
          germ.playerNeutralOccupationSource who index =
            history (Fin.last n)) :
    Tendsto
      (fun T : ℕ => C.strictSetExpectedMass initial selection T / T)
      atTop (nhds 0) := by
  simpa only [IsAsymptoticallySublinear, div_eq_mul_inv, mul_comm] using
    C.strictSetExpectedMass_isAsymptoticallySublinear
      initial selection source_compatible

/-- A cumulative contribution supported on pure uses of the strict set is
sublinear whenever its absolute value is bounded by `L` per such use. -/
theorem strictSetUseContribution_isAsymptoticallySublinear
    (C : germ.PlayerNeutralStrictLeadingDrift B who jet)
    (initial : G.State)
    (choice :
      ∀ n, (Fin (n + 1) → G.State) →
        germ.PlayerNeutralOccupationIndex who)
    (source_compatible :
      ∀ n history,
        germ.playerNeutralOccupationSource who (choice n history) =
          history (Fin.last n))
    (contribution : ∀ T, (Fin (T + 1) → G.State) → ℝ)
    (L : ℝ)
    (hdominated :
      ∀ T history,
        |contribution T history| ≤
          L *
            ∑ index : {index // index ∈ C.strictIndexSet},
              selectedTransitionUseCount choice index.1 T history) :
    IsAsymptoticallySublinear
      (fun T =>
        expect
          (adaptiveHistoryLaw
            (adaptiveMarkovStep initial
              (selectedTransitionComparison
                (germ.playerNeutralOccupationKernel who) choice))
            (T + 1))
          (fun history => |contribution T history|)) := by
  exact transitionSetUseContribution_isAsymptoticallySublinear
    initial (germ.playerNeutralOccupationKernel who) choice
    C.strictIndexSet contribution L hdominated
    (C.strictSetExpectedUse_isAsymptoticallySublinear
      initial choice source_compatible)

/-- A cumulative contribution supported on mixed mass of the strict set is
sublinear whenever its absolute value is bounded by `L` per unit of that
mass. -/
theorem strictSetMassContribution_isAsymptoticallySublinear
    (C : germ.PlayerNeutralStrictLeadingDrift B who jet)
    (initial : G.State)
    (selection :
      ∀ n, (Fin (n + 1) → G.State) →
        PMF (germ.PlayerNeutralOccupationIndex who))
    (source_compatible :
      ∀ n history index,
        selection n history index ≠ 0 →
          germ.playerNeutralOccupationSource who index =
            history (Fin.last n))
    (contribution : ∀ T, (Fin (T + 1) → G.State) → ℝ)
    (L : ℝ)
    (hdominated :
      ∀ T history,
        |contribution T history| ≤
          L *
            ∑ index : {index // index ∈ C.strictIndexSet},
              selectedTransitionMassSum selection index.1 T history) :
    IsAsymptoticallySublinear
      (fun T =>
        expect
          (adaptiveHistoryLaw
            (adaptiveMarkovStep initial
              (mixedTransitionComparison
                (germ.playerNeutralOccupationKernel who) selection))
            (T + 1))
          (fun history => |contribution T history|)) := by
  exact transitionSetMassContribution_isAsymptoticallySublinear
    initial (germ.playerNeutralOccupationKernel who) selection
    C.strictIndexSet contribution L hdominated
    (C.strictSetExpectedMass_isAsymptoticallySublinear
      initial selection source_compatible)

end PlayerNeutralStrictLeadingDrift
end AnalyticBellmanGerm
end StochasticGame
end GameTheory
