/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Certificates.Public.FirstHitStoppingRule

/-!
# Acceptance model for history-dependent first-hit stopping

The public action in the first record chooses between stopping at time one
and stopping at time two.  Time two is a mandatory stopping prefix, so every
length-three history stops strictly before the fuel.  This gives a genuinely
history-dependent inhabitant of the repaired online stopping-rule API.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace PublicHistoryFirstHitStoppingAcceptance

open Math.Probability

/-- A one-player, one-state game with a public Boolean action. -/
def game : StochasticGame Unit where
  State := Unit
  Act := fun _ => Bool
  stagePayoff := fun _ _ _ => 0
  transition := fun _ _ => PMF.pure ()
  discount := 0
  discount_nonneg := le_rfl
  discount_lt_one := by norm_num

/-- Stop at time one when the first public action is `true`; otherwise stop
at time two. -/
def stop : ∀ time, game.Hist time → Prop
  | 0, _ => False
  | 1, history => (history.1 0).2 () = true
  | 2, _ => True
  | _ + 3, _ => False

instance stop_decidable (time : ℕ) :
    DecidablePred (stop time) :=
  fun history => Classical.propDecidable (stop time history)

@[simp] theorem firstAction_prefix_one
    (history : game.Hist 3) :
    ((game.boundedHistoryPrefix history
      ⟨1, by decide⟩).1 0).2 () =
      (history.1 0).2 () :=
  rfl

/-- Every length-three history stops at time one or two. -/
theorem stopsBeforeFuel (history : game.Hist 3) :
    ∃ stage : Fin 4,
      game.firstPublicHit? stop history = some stage ∧
        stage.val < 3 := by
  by_cases hfirst : (history.1 0).2 () = true
  · refine ⟨⟨1, by decide⟩, ?_, by decide⟩
    rw [game.firstPublicHit?_eq_some_iff]
    constructor
    · change (history.1 0).2 () = true
      exact hfirst
    · intro earlier hearlier
      fin_cases earlier <;> simp [stop] at hearlier ⊢
  · refine ⟨⟨2, by decide⟩, ?_, by decide⟩
    rw [game.firstPublicHit?_eq_some_iff]
    constructor
    · simp [stop]
    · intro earlier hearlier
      fin_cases earlier
      · simp [stop] at hearlier
      · change
          ((game.boundedHistoryPrefix history
            ⟨1, by decide⟩).1 0).2 () = true at hearlier
        rw [firstAction_prefix_one] at hearlier
        exact (hfirst hearlier).elim
      · decide
      · decide

/-- The repaired online rule for this history-dependent stopping region. -/
def rule : game.OnlineCausalBoundedStoppingRule 3 :=
  game.onlineCausalBoundedStoppingRuleOfFirstHit
    stop 3 stopsBeforeFuel

/-- A full history whose first public action requests the early stop. -/
def earlyHistory : game.Hist 3 :=
  (fun _ => ((), fun _ => true), ())

/-- A full history whose first public action defers to the time-two stop. -/
def lateHistory : game.Hist 3 :=
  (fun _ => ((), fun _ => false), ())

theorem early_first_hit :
    game.firstPublicHit? stop earlyHistory =
      some ⟨1, by decide⟩ := by
  rw [game.firstPublicHit?_eq_some_iff]
  constructor
  · change true = true
    rfl
  · intro earlier hearlier
    fin_cases earlier <;> simp [stop, earlyHistory] at hearlier ⊢

theorem late_first_hit :
    game.firstPublicHit? stop lateHistory =
      some ⟨2, by decide⟩ := by
  rw [game.firstPublicHit?_eq_some_iff]
  constructor
  · simp [stop]
  · intro earlier hearlier
    fin_cases earlier
    · simp [stop] at hearlier
    · change
        ((game.boundedHistoryPrefix lateHistory
          ⟨1, by decide⟩).1 0).2 () = true at hearlier
      rw [firstAction_prefix_one] at hearlier
      change false = true at hearlier
      contradiction
    · decide
    · decide

/-- Two histories of the same fuel select different stopping times. -/
theorem selector_is_history_dependent :
    rule.selector earlyHistory = ⟨1, by decide⟩ ∧
      rule.selector lateHistory = ⟨2, by decide⟩ := by
  constructor
  · exact game.firstHitStopSelector_eq_of_hit
      stop earlyHistory _ early_first_hit
  · exact game.firstHitStopSelector_eq_of_hit
      stop lateHistory _ late_first_hit

/-- The complete repaired structure is inhabited by a rule with genuinely
different stopping times on two full public histories. -/
theorem rule_nonempty :
    Nonempty (game.OnlineCausalBoundedStoppingRule 3) :=
  ⟨rule⟩

end PublicHistoryFirstHitStoppingAcceptance
end StochasticGame
end GameTheory
