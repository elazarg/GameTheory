/-
# Own-play recall on forgetful and delayed protocols

The two-vote protocol observes only whether play has stopped, so it forgets its
own first vote. Refining it by own-play recall restores perfect recall and
separates the two decision points that the original model merged.

The delayed protocol checks what the refinement must not add. Chance inserts
either zero or one idle round before the player's only decision, and the player
observes nothing. Both histories reach the decision with the same refined
information: recall of one's own moves reveals no timing.
-/

import GameTheory.Protocol.OwnPlayRecall
import GameTheory.Tests.Randomized

noncomputable section

namespace GameTheory.Tests.OwnPlayRecall

open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Protocol.ExecutionProtocol (Trace)

/-! ## Restoring recall -/

open GameTheory.Tests.Randomized in
/-- The refinement has perfect recall although the original model does not
(`Randomized.not_perfectRecall`). -/
theorem twice_withOwnPlayRecall_perfectRecall : signals.withOwnPlayRecall.PerfectRecall :=
  signals.withOwnPlayRecall_perfectRecall

open GameTheory.Tests.Randomized in
/-- Before and after the first vote the original information agrees, but the
refined information differs. -/
theorem twice_withOwnPlayRecall_separates :
    signals.infoOf () Trace.start = signals.infoOf () votedOnce ∧
      signals.withOwnPlayRecall.infoOf () Trace.start ≠
        signals.withOwnPlayRecall.infoOf () votedOnce := by
  refine ⟨rfl, fun hsame => ?_⟩
  have hplay := ((signals.withOwnPlayRecall_infoOf_eq_iff () _ _).1 hsame).2
  simp [InfoSignals.ownPlay, votedOnce] at hplay

/-! ## Revealing no timing -/

/-- Before the random delay, during it, at the decision, and after it. -/
inductive Stage | start | waiting | ready | done

/-- Chance delays the one decision by zero or one idle round. -/
@[reducible]
def delayed : ExecutionProtocol Unit where
  State := Stage
  Action _ := Bool
  init := .start
  active state _ := state = .ready
  available _ _ := Set.univ
  terminal state := state = .done
  step state _ :=
    match state with
    | .start => mix (1 / 2) (by norm_num) (by norm_num) (PMF.pure .waiting) (PMF.pure .ready)
    | .waiting => PMF.pure .ready
    | .ready => PMF.pure .done
    | .done => PMF.pure .done
  progress := by
    intro state hterminal
    cases state with
    | ready => exact ⟨fun _ => some true, fun _ => ⟨rfl, Set.mem_univ _⟩⟩
    | start => exact ⟨fun _ => none, fun _ => Stage.noConfusion⟩
    | waiting => exact ⟨fun _ => none, fun _ => Stage.noConfusion⟩
    | done => exact absurd rfl hterminal

/-- The player observes nothing at all. -/
@[reducible]
def blind : InfoSignals delayed where
  PublicSignal := Unit
  PrivateSignal _ := Unit
  initialPublic := ()
  initialPrivate _ := ()
  publicSignal _ := ()
  privateSignal _ _ := ()
  InfoState _ := Unit
  initInfo _ _ _ := ()
  pushInfo _ _ _ _ _ := ()

theorem idle_legal (state : Stage) (hidle : state ≠ .ready) (hterminal : state ≠ .done) :
    delayed.Legal state (fun _ => none) :=
  ⟨hterminal, fun _ => hidle⟩

/-- Chance goes straight to the decision. -/
def direct : Trace delayed Stage.ready :=
  .extend .start _ (idle_legal .start Stage.noConfusion Stage.noConfusion)
    (mem_support_mix_right (1 / 2) (by norm_num) (by norm_num) (by norm_num)
      ((PMF.mem_support_pure_iff _ _).2 rfl))

/-- Chance inserts one idle round before the decision. -/
def late : Trace delayed Stage.ready :=
  .extend
    (.extend .start _ (idle_legal .start Stage.noConfusion Stage.noConfusion)
      (mem_support_mix_left (1 / 2) (by norm_num) (by norm_num) (by norm_num)
        ((PMF.mem_support_pure_iff _ _).2 rfl)))
    _ (idle_legal .waiting Stage.noConfusion Stage.noConfusion)
    ((PMF.mem_support_pure_iff _ _).2 rfl)

/-- The histories differ in length, yet the refined information at the decision
is the same. -/
theorem withOwnPlayRecall_hides_delay :
    blind.withOwnPlayRecall.infoOf () direct = blind.withOwnPlayRecall.infoOf () late := by
  rw [blind.withOwnPlayRecall_infoOf_eq_iff]
  exact ⟨rfl, by simp [InfoSignals.ownPlay, direct, late]⟩

end GameTheory.Tests.OwnPlayRecall
