/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Protocol.Randomized

/-! # State kernels of history-based randomized play

When the state retains everything consulted by a fixed profile, forgetting
the canonical history commutes with iteration of the one-step state law.
Iteration here is ordinary function iteration on distributions; the game
continues to use the canonical randomized history runner.
-/

noncomputable section

namespace GameTheory.Protocol.ExecutionProtocol

open GameTheory.Math.Probability

universe uι us ua

variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}

theorem runRandomizedFor_map_state (chooser : E.RandomizedChooser)
    (kernel : E.State → PMF E.State)
    (terminal : ∀ state, E.terminal state → kernel state = PMF.pure state)
    (step : ∀ (history : E.History) (running : ¬ E.terminal history.state),
      (chooser history running).bind (E.step history.state) = kernel history.state)
    (fuel : ℕ) (history : E.History) :
    (E.runRandomizedFor chooser fuel history).map History.state =
      (fun law => law.bind kernel)^[fuel] (PMF.pure history.state) := by
  have one (current : E.History) :
      (E.runRandomizedFor chooser 1 current).map History.state = kernel current.state := by
    by_cases stopped : E.terminal current.state
    · rw [runRandomizedFor_of_terminal chooser _ stopped, PMF.pure_map,
        terminal current.state stopped]
    · rw [runRandomizedFor_succ_of_not_terminal chooser 0 stopped, PMF.map_bind]
      calc
        _ = (chooser current stopped).bind (E.step current.state) := by
          apply GameTheory.Math.Probability.bind_congr_on_support
          intro joint _
          rw [GameTheory.Math.Probability.map_bindOnSupport]
          calc
            _ = (E.step current.state joint).bind PMF.pure := by
              apply GameTheory.Math.Probability.bindOnSupport_eq_bind_of_eq_on_support
              intro target realized
              simp only [runRandomizedFor_zero, PMF.pure_map, History.extend_state]
            _ = _ := PMF.bind_pure _
        _ = _ := step current stopped
  induction fuel with
  | zero => simp only [runRandomizedFor_zero, PMF.pure_map, Function.iterate_zero_apply]
  | succ fuel ih =>
      rw [runRandomizedFor_add, PMF.map_bind]
      calc
        _ = (E.runRandomizedFor chooser fuel history).bind
            (fun final => kernel final.state) :=
          GameTheory.Math.Probability.bind_congr_on_support _ fun final _ => one final
        _ = ((E.runRandomizedFor chooser fuel history).map History.state).bind kernel :=
          (PMF.bind_map ..).symm
        _ = _ := by rw [ih, Function.iterate_succ_apply']

end GameTheory.Protocol.ExecutionProtocol
