/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.SorinOccupationStopping
import GameTheory.Concepts.Stochastic.SorinUniformSeparation

/-!
# Discharging Sorin's bottom-right occupation hypothesis

This module connects the quantitative stopping theorem to the exact occupation
accounting in `SorinUniformSeparation`.  The live `(Bottom, Right)` stage mass
is bounded by the live-state probability.  The latter has Cesaro limit equal
to `survivalLimit`, which the stopping theorem bounds by `14 * epsilon` for
every uniform positive-`epsilon` equilibrium profile.

The capstone proves the previously isolated proposition
`UniformEquilibriaForceBottomRightOccupationVanishing` unconditionally.
-/

noncomputable section

open scoped BigOperators Topology

namespace GameTheory
namespace StochasticGame
namespace SorinAbsorbingGame

open Filter Math.Probability

/-- Extending a history by one stage adds exactly that stage's bottom-right
indicator. -/
theorem bottomRightCount_snoc {time : ℕ} (history : game.Hist time)
    (action : game.JointAct) (next : State) :
    bottomRightCount
        ((Fin.snoc history.1 (history.2, action), next) :
          game.Hist (time + 1)) =
      bottomRightCount history + bottomRightIndicator history.2 action := by
  simp [bottomRightCount, Fin.sum_univ_castSucc]

/-- Expected probability mass of live `(Bottom, Right)` at one stage. -/
def bottomRightStageMass (profile : game.BehaviorProfile) (time : ℕ) : ℝ :=
  expect (game.histDist profile .live time) fun history =>
    expect (game.stageActionDist profile history) fun action =>
      bottomRightIndicator history.2 action

/-- One-step recursion for the expected bottom-right count. -/
theorem expect_bottomRightCount_succ
    (profile : game.BehaviorProfile) (time : ℕ) :
    expect (game.histDist profile .live (time + 1)) bottomRightCount =
      expect (game.histDist profile .live time) bottomRightCount +
        bottomRightStageMass profile time := by
  have hstep : ∀ history : game.Hist time,
      expect ((game.stageActionDist profile history).bind fun action =>
          (game.transition history.2 action).bind fun next =>
            PMF.pure
              ((Fin.snoc history.1 (history.2, action), next) :
                game.Hist (time + 1)))
        bottomRightCount =
      bottomRightCount history +
        expect (game.stageActionDist profile history)
          (fun action => bottomRightIndicator history.2 action) := by
    intro history
    rw [expect_bind]
    have hinner : ∀ action : game.JointAct,
        expect ((game.transition history.2 action).bind fun next =>
            PMF.pure
              ((Fin.snoc history.1 (history.2, action), next) :
                game.Hist (time + 1)))
          bottomRightCount =
      bottomRightCount history +
          bottomRightIndicator history.2 action := by
      intro action
      rw [expect_bind, transition_eq, expect_pure, expect_pure,
        bottomRightCount_snoc]
    simp only [hinner]
    rw [expect_add, expect_const]
  rw [game.histDist_succ, expect_bind]
  simp only [hstep]
  rw [expect_add]
  rfl

/-- Expected bottom-right count is the sum of the per-stage masses. -/
theorem expect_bottomRightCount_eq_sum_bottomRightStageMass
    (profile : game.BehaviorProfile) :
    ∀ horizon : ℕ,
      expect (game.histDist profile .live horizon) bottomRightCount =
        ∑ time ∈ Finset.range horizon, bottomRightStageMass profile time := by
  intro horizon
  induction horizon with
  | zero => simp [bottomRightCount]
  | succ horizon ih =>
      rw [expect_bottomRightCount_succ, ih, Finset.sum_range_succ]

/-- The bottom-right cell indicator is bounded by the current live-state
indicator. -/
theorem bottomRightIndicator_le_liveIndicator
    (state : State) (action : game.JointAct) :
    bottomRightIndicator state action ≤ liveIndicator state := by
  unfold bottomRightIndicator
  split
  · rename_i hcell
    rcases hcell with ⟨rfl, _⟩
    norm_num
  · exact liveIndicator_nonneg state

/-- Consequently each bottom-right stage mass is bounded by survival at that
stage. -/
theorem bottomRightStageMass_le_liveProbability
    (profile : game.BehaviorProfile) (time : ℕ) :
    bottomRightStageMass profile time ≤ liveProbability profile time := by
  unfold bottomRightStageMass liveProbability
    StochasticGame.expectedStateValue
  apply expect_mono
  intro history
  calc
    expect (game.stageActionDist profile history)
        (fun action => bottomRightIndicator history.2 action) ≤
      expect (game.stageActionDist profile history)
        (fun _action => liveIndicator history.2) := by
          apply expect_mono
          intro action
          exact bottomRightIndicator_le_liveIndicator history.2 action
    _ = liveIndicator history.2 := expect_const _ _

/-- Finite-horizon occupation is bounded by the Cesaro average of survival. -/
theorem bottomRightOccupation_le_survivalCesaro
    (profile : game.BehaviorProfile) (horizon : ℕ) :
    bottomRightOccupation profile .live horizon ≤
      (horizon : ℝ)⁻¹ *
        ∑ time ∈ Finset.range horizon, liveProbability profile time := by
  unfold bottomRightOccupation
  rw [expect_bottomRightCount_eq_sum_bottomRightStageMass]
  exact mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum fun time _ =>
      bottomRightStageMass_le_liveProbability profile time)
    (inv_nonneg.mpr (Nat.cast_nonneg horizon))

/-- The Cesaro survival averages converge to the infinite-survival mass. -/
theorem tendsto_survivalCesaro_survivalLimit
    (profile : game.BehaviorProfile) :
    Tendsto
      (fun horizon : ℕ =>
        (horizon : ℝ)⁻¹ *
          ∑ time ∈ Finset.range horizon, liveProbability profile time)
      atTop (nhds (survivalLimit profile)) :=
  (tendsto_liveProbability_survivalLimit profile).cesaro

/-- Quantitative occupation consequence for one fixed uniform equilibrium
profile: every target strictly above `14 * epsilon` eventually bounds the
bottom-right occupation. -/
theorem bottomRightOccupation_eventually_le_of_isUniformεEquilibrium
    (profile : game.BehaviorProfile) {epsilon delta : ℝ}
    (hepsilon : 0 < epsilon)
    (huniform : game.IsUniformεEquilibrium .live epsilon profile)
    (hdelta : 14 * epsilon < delta) :
    ∃ threshold : ℕ, ∀ horizon : ℕ, threshold ≤ horizon →
      bottomRightOccupation profile .live horizon ≤ delta := by
  have hlimit :=
    survivalLimit_le_fourteen_mul_of_isUniformεEquilibrium
      profile hepsilon huniform
  have htendsto := tendsto_survivalCesaro_survivalLimit profile
  have heventually : ∀ᶠ horizon : ℕ in atTop,
      (horizon : ℝ)⁻¹ *
          ∑ time ∈ Finset.range horizon, liveProbability profile time <
        delta := by
    exact (tendsto_order.1 htendsto).2 delta (lt_of_le_of_lt hlimit hdelta)
  rw [eventually_atTop] at heventually
  obtain ⟨threshold, hthreshold⟩ := heventually
  refine ⟨threshold, fun horizon hhorizon => ?_⟩
  exact (bottomRightOccupation_le_survivalCesaro profile horizon).trans
    (hthreshold horizon hhorizon).le

/-- **Unconditional discharge of the named strategic hypothesis.** -/
theorem uniformEquilibriaForceBottomRightOccupationVanishing :
    UniformEquilibriaForceBottomRightOccupationVanishing := by
  intro delta hdelta
  refine ⟨delta / 28, by positivity, fun epsilon hepsilon hepsilonBar
    profile huniform => ?_⟩
  apply bottomRightOccupation_eventually_le_of_isUniformεEquilibrium
    profile hepsilon huniform
  nlinarith

/-- Sorin's separation line now follows without a strategic hypothesis. -/
theorem uniformEquilibriumPayoff_weighted_eq_two
    (payoff : Payoff Player)
    (hpayoff : game.IsUniformEquilibriumPayoff .live payoff) :
    2 * payoff false + payoff true = 2 :=
  uniformEquilibriumPayoff_weighted_eq_two_of_bottomRightOccupation_vanishing
    uniformEquilibriaForceBottomRightOccupationVanishing payoff hpayoff

/-- The discount-constant endpoint `(1/2, 2/3)` is not a uniform equilibrium
payoff. -/
theorem discountedEndpoint_not_isUniformEquilibriumPayoff :
    ¬ game.IsUniformEquilibriumPayoff .live (pair (1 / 2) (2 / 3)) :=
  discountedEndpoint_not_isUniformEquilibriumPayoff_of_bottomRightOccupation_vanishing
    uniformEquilibriaForceBottomRightOccupationVanishing

end SorinAbsorbingGame
end StochasticGame
end GameTheory
