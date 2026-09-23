/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Protocol.Randomized

/-! # Reading a continuation law from randomized histories

A decreasing rank and a one-step law identify the output of the existing
randomized runner. The chooser may depend on the full history. The law being
read can retain hidden state without exposing that state to the chooser.
-/

noncomputable section

namespace GameTheory.Protocol.ExecutionProtocol

open GameTheory.Math.Probability

universe uι us ua uω

variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι} {Ω : Type uω}

theorem runRandomizedFor_readout_eq (chooser : E.RandomizedChooser)
    (rank : E.State → ℕ)
    (zero_terminal : ∀ state, rank state = 0 → E.terminal state)
    (decreases : ∀ (history : E.History)
      (joint : {actions : ∀ who, Option (E.Action who) // E.Legal history.state actions})
      after, after ∈ (E.step history.state joint).support → rank after < rank history.state)
    (readout : E.State → Ω) (law : E.State → FinDist Ω)
    (terminal_law : ∀ state, E.terminal state → law state = FinDist.pure (readout state))
    (step_law : ∀ (history : E.History) (running : ¬ E.terminal history.state),
      (chooser history running).bind (fun joint => (E.step history.state joint).bind law) =
        law history.state)
    (fuel : ℕ) (history : E.History) (enough : rank history.state ≤ fuel) :
    (E.runRandomizedFor chooser fuel history).map (fun final => readout final.state) =
      law history.state := by
  induction fuel generalizing history with
  | zero =>
      rw [runRandomizedFor_zero, FinDist.map_pure,
        terminal_law history.state (zero_terminal history.state (by omega))]
  | succ fuel ih =>
      by_cases stopped : E.terminal history.state
      · rw [runRandomizedFor_of_terminal _ _ stopped, FinDist.map_pure,
          terminal_law history.state stopped]
      · rw [runRandomizedFor_succ_of_not_terminal _ _ stopped, FinDist.map_bind]
        calc
          _ = (chooser history stopped).bind
              (fun joint => (E.step history.state joint).bind law) := by
            apply FinDist.bind_congr
            intro joint _
            rw [FinDist.map_bindOnSupport]
            apply FinDist.bindOnSupport_eq_bind_of_eq_on_support
            intro after reached
            exact ih (history.extend joint.2 reached)
              (by have smaller := decreases history joint after reached; exact Nat.le_of_lt_succ
                    (lt_of_lt_of_le smaller enough))
          _ = _ := step_law history stopped

end GameTheory.Protocol.ExecutionProtocol
