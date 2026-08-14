/-
# Finite-horizon stochastic-game evaluation

Every finite truncation is the canonical behavioral Protocol form with an
external average stage utility. No second history runner or evaluator appears.
-/

import GameTheory.Stochastic.PerfectMonitoring
import GameTheory.Core.Utility

noncomputable section

namespace GameTheory.Stochastic

open Probability Protocol Protocol.ExecutionProtocol

universe uι us ua

namespace Game

variable {ι : Type uι} (G : Game.{uι, us, ua} ι)

/-- Utility contributed by one realized stochastic transition. -/
def eventUtility (initial : G.State) [∀ i, Nonempty (G.Action i)]
    (event : (G.toExecution initial).StepEvent) (who : ι) : ℝ :=
  G.stageUtility event.source (G.stageRecordOfEvent initial event).joint who

/-- Average stage utility of one canonical Protocol history. -/
def historyAverageUtility (initial : G.State) [∀ i, Nonempty (G.Action i)]
    (horizon : ℕ) (history : (G.toExecution initial).History) (who : ι) : ℝ :=
  (horizon : ℝ)⁻¹ * history.valueSum (fun event => G.eventUtility initial event who)

/-- The zero-horizon convention is the empty average `0`. -/
@[simp]
theorem historyAverageUtility_zero (initial : G.State)
    [∀ i, Nonempty (G.Action i)]
    (history : (G.toExecution initial).History) (who : ι) :
    G.historyAverageUtility initial 0 history who = 0 := by
  simp [historyAverageUtility]

variable [Fintype ι]

/-- The finite-horizon behavioral form is exactly the existing Protocol
compiler. -/
@[reducible]
def horizonForm (initial : G.State) [∀ i, Nonempty (G.Action i)] (horizon : ℕ) :
    GameForm ι :=
  (G.perfectMonitoring initial).toBehavioralGameForm horizon

/-- Horizon-average utility remains separate data over the compiled form. -/
def horizonUtility (initial : G.State) [∀ i, Nonempty (G.Action i)] (horizon : ℕ) :
    Utility (G.horizonForm initial horizon).sig :=
  fun history who => G.historyAverageUtility initial horizon history who

/-- Ergonomic bundle of the canonical horizon form and its average utility. -/
def horizonGame (initial : G.State) [∀ i, Nonempty (G.Action i)]
    (horizon : ℕ) : UtilityGame ι where
  form := G.horizonForm initial horizon
  utility := G.horizonUtility initial horizon

@[simp]
theorem horizonForm_play (initial : G.State) [∀ i, Nonempty (G.Action i)]
    (horizon : ℕ) (profile : G.BehaviorProfile initial) :
    (G.horizonForm initial horizon).play profile =
      (G.perfectMonitoring initial).runBehavioral profile horizon :=
  rfl

/-- Expected finite-horizon average payoff, transparently evaluated by the
canonical expected-utility function. -/
abbrev finiteAveragePayoff (initial : G.State) [∀ i, Nonempty (G.Action i)]
    (horizon : ℕ) (profile : G.BehaviorProfile initial) (who : ι) : ℝ :=
  expectedUtility (G.horizonUtility initial horizon) who
    ((G.horizonForm initial horizon).play profile)

/-- The utility-game bundle has exactly the named finite-horizon evaluation. -/
@[simp]
theorem horizonGame_expectedUtility (initial : G.State)
    [∀ i, Nonempty (G.Action i)] (horizon : ℕ)
    (profile : G.BehaviorProfile initial) (who : ι) :
    expectedUtility (G.horizonGame initial horizon).utility who
        ((G.horizonGame initial horizon).form.play profile) =
      G.finiteAveragePayoff initial horizon profile who :=
  rfl

/-- With no transitions, every profile's expected average payoff is zero. -/
@[simp]
theorem finiteAveragePayoff_zero (initial : G.State)
    [∀ i, Nonempty (G.Action i)] (profile : G.BehaviorProfile initial)
    (who : ι) :
    G.finiteAveragePayoff initial 0 profile who = 0 := by
  rw [finiteAveragePayoff, horizonForm_play]
  unfold InformationModel.runBehavioral InformationModel.runBehavioralFrom
  rw [ExecutionProtocol.runRandomizedFor_zero, expectedUtility_pure]
  simp [horizonUtility, historyAverageUtility]

end Game

end GameTheory.Stochastic
