/-
# The one-shot deviation principle, exercised

Checking a strategy against every alternative *strategy* is checking infinitely
many things. The principle says checking it against every alternative *action*,
one step at a time and against its own continued play, is enough.

This file exercises it on the smallest protocol that can tell the two apart: a
coin decides whether the player gets to choose at all, and its one choice is
between a payoff of `1` and a payoff of `0`. Both directions are checked — the
policy that grabs satisfies the one-step condition and the policy that passes
provably does not — so what the principle detects is optimality rather than
anything the protocol would have handed to any policy. The equivalence is
exercised in both directions too: the one-step condition gives global
optimality, and global optimality gives it back.
-/

import GameTheory.Tests.Backward

noncomputable section

namespace GameTheory.Tests.OneShot

open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Protocol.ExecutionProtocol
open GameTheory.Tests.Backward

/-- The backward value of grabbing, at every state. -/
theorem value_grab :
    ∀ state, probe.backwardValue probe_wellFoundedPlay (policy .grab) basePayoff state =
      match state with
      | .flip => 1 / 2
      | .pick => 1
      | .grabbed => 1
      | .passed => 0
  | .flip => by rw [backwardValue_flip]; norm_num [basePayoff, Move.outcome]
  | .pick => by rw [backwardValue_pick]; rfl
  | .grabbed => backwardValue_of_terminal (by simp)
  | .passed => backwardValue_of_terminal (by simp)

/-- **Grabbing survives every one-shot deviation.** At the chance node no choice
is available to change, and at the decision node the alternative is worth no
more. -/
theorem grab_isOneShotOptimal :
    probe.IsOneShotOptimal probe_wellFoundedPlay (policy .grab) basePayoff := by
  rintro state hterm ⟨joint, isLegal⟩
  match state with
  | .grabbed | .passed => exact absurd (by simp) hterm
  | .flip =>
    -- Nobody is active, so every legal joint action induces the same coin.
    show (probe.step Spot.flip ⟨joint, isLegal⟩).expect _ ≤
      (probe.step Spot.flip (policy .grab Spot.flip hterm)).expect _
    rw [show probe.step Spot.flip ⟨joint, isLegal⟩ = coin from rfl]
  | .pick =>
    show (probe.step Spot.pick ⟨joint, isLegal⟩).expect _ ≤
      (probe.step Spot.pick (policy .grab Spot.pick hterm)).expect _
    rw [show probe.step Spot.pick ⟨joint, isLegal⟩ =
        FinDist.pure ((joint ()).elim Spot.passed Move.outcome) from rfl,
      show probe.step Spot.pick (policy .grab Spot.pick hterm) =
        FinDist.pure Spot.grabbed from rfl,
      FinDist.expect_pure, FinDist.expect_pure, value_grab, value_grab]
    rcases hjoint : joint () with _ | move
    · norm_num
    · cases move <;> norm_num [Move.outcome]

/-- **Passing does not.** Grabbing instead is worth strictly more against the
same continuation, so the one-step condition fails — and fails at the one state
where a choice exists. -/
theorem pass_not_isOneShotOptimal :
    ¬ probe.IsOneShotOptimal probe_wellFoundedPlay (policy .pass) basePayoff := by
  intro hopt
  have hlegal : probe.Legal Spot.pick (fun _ => some Move.grab) :=
    ⟨pick_not_terminal, fun _ => ⟨rfl, Set.mem_univ _⟩⟩
  have hgrab := hopt Spot.pick pick_not_terminal ⟨fun _ => some Move.grab, hlegal⟩
  rw [show probe.step Spot.pick ⟨fun _ => some Move.grab, hlegal⟩ =
      FinDist.pure Spot.grabbed from rfl,
    show probe.step Spot.pick (policy .pass Spot.pick pick_not_terminal) =
      FinDist.pure Spot.passed from rfl,
    FinDist.expect_pure, FinDist.expect_pure,
    backwardValue_of_terminal (by simp : probe.terminal Spot.grabbed),
    backwardValue_of_terminal (by simp : probe.terminal Spot.passed)] at hgrab
  norm_num [basePayoff] at hgrab

/-- **The principle, applied.** Grabbing is at least as good as every chooser —
not merely as good as passing, and without comparing against any of them one by
one. -/
theorem grab_best (other : probe.Chooser) (state : Spot) :
    probe.backwardValue probe_wellFoundedPlay other basePayoff state ≤
      probe.backwardValue probe_wellFoundedPlay (policy .grab) basePayoff state :=
  backwardValue_le_of_isOneShotOptimal grab_isOneShotOptimal other state

/-- **And back again.** The principle is an equivalence: being best among all
choosers recovers the one-step condition, so nothing is lost by checking only
single actions. -/
theorem grab_isOneShotOptimal_of_best :
    probe.IsOneShotOptimal probe_wellFoundedPlay (policy .grab) basePayoff :=
  isOneShotOptimal_of_backwardValue_le grab_best

/-- And the conclusion is not vacuous: passing really is worse at the root. -/
theorem pass_strictly_worse :
    probe.backwardValue probe_wellFoundedPlay (policy .pass) basePayoff Spot.flip <
      probe.backwardValue probe_wellFoundedPlay (policy .grab) basePayoff Spot.flip := by
  rw [backwardValue_flip, backwardValue_flip]
  norm_num [basePayoff, Move.outcome]

end GameTheory.Tests.OneShot
