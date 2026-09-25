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

local instance : Fintype Spot := spotFintype

/-- The backward value of grabbing, at every state. -/
theorem value_grab :
    ∀ state, probe.backwardValue probe_wellFoundedPlay (policy .grab)
      basePayoff state (payoffIntegrable_of_finite _ _) =
      match state with
      | .flip => 1 / 2
      | .pick => 1
      | .grabbed => 1
      | .passed => 0
  | .flip => by rw [backwardValue_flip]; norm_num [basePayoff, Move.outcome]
  | .pick => by rw [backwardValue_pick]; rfl
  | .grabbed => backwardValue_of_terminal (by simp) _
  | .passed => backwardValue_of_terminal (by simp) _

/-- **Grabbing survives every one-shot deviation.** At the chance node no choice
is available to change, and at the decision node the alternative is worth no
more. -/
theorem grab_isOneShotOptimal :
    probe.IsOneShotOptimal probe_wellFoundedPlay (policy .grab) basePayoff := by
  intro state hterm
  refine ⟨payoffIntegrable_of_finite _ _,
    (fun _ _ => payoffIntegrable_of_finite _ _), ?_⟩
  rintro ⟨joint, isLegal⟩ _ hchoice halt
  match state with
  | .grabbed | .passed => exact absurd (by simp) hterm
  | .flip =>
    -- Nobody is active, so every legal joint action induces the same coin.
    dsimp only [Context.value, Context.IntegrableAt,
      ExecutionProtocol.oneShotContext] at hchoice halt ⊢
    have hsame : probe.step Spot.flip ⟨joint, isLegal⟩ =
        probe.step Spot.flip (policy .grab Spot.flip hterm) := rfl
    exact le_of_eq (expect_congr_law
      (congrArg (fun law => law.bind
        (probe.backwardLaw probe_wellFoundedPlay (policy .grab))) hsame)
      basePayoff _ _)
  | .pick =>
    dsimp only [Context.value, Context.IntegrableAt,
      ExecutionProtocol.oneShotContext] at hchoice halt ⊢
    have hleft :
        (probe.step Spot.pick ⟨joint, isLegal⟩).bind
            (probe.backwardLaw probe_wellFoundedPlay (policy .grab)) =
          PMF.pure ((joint ()).elim Spot.passed Move.outcome) := by
      rw [show probe.step Spot.pick ⟨joint, isLegal⟩ =
          PMF.pure ((joint ()).elim Spot.passed Move.outcome) from rfl,
        PMF.pure_bind]
      cases hchoice : joint () with
      | none => exact backwardLaw_of_terminal passed_terminal
      | some move => exact backwardLaw_of_terminal (outcome_terminal move)
    have hright :
        (probe.step Spot.pick (policy .grab Spot.pick hterm)).bind
            (probe.backwardLaw probe_wellFoundedPlay (policy .grab)) =
          PMF.pure Spot.grabbed := by
      rw [show probe.step Spot.pick (policy .grab Spot.pick hterm) =
          PMF.pure Spot.grabbed from rfl, PMF.pure_bind,
        backwardLaw_of_terminal (by simp : probe.terminal Spot.grabbed)]
    calc
      _ = basePayoff ((joint ()).elim Spot.passed Move.outcome) := by
        have hpure := payoffIntegrable_pure
          ((joint ()).elim Spot.passed Move.outcome) basePayoff
        exact (expect_congr_law hleft basePayoff halt hpure).trans
          (expect_pure _ _ hpure)
      _ ≤ 1 := by
        cases hchoice : joint () with
        | none => norm_num [basePayoff]
        | some move => cases move <;> norm_num [basePayoff, Move.outcome]
      _ = _ := by
        have hpure := payoffIntegrable_pure Spot.grabbed basePayoff
        have hvalue := (expect_congr_law hright basePayoff hchoice hpure).trans
          (expect_pure _ _ hpure)
        simpa only [basePayoff] using hvalue.symm

/-- **Passing does not.** Grabbing instead is worth strictly more against the
same continuation, so the one-step condition fails — and fails at the one state
where a choice exists. -/
theorem pass_not_isOneShotOptimal :
    ¬ probe.IsOneShotOptimal probe_wellFoundedPlay (policy .pass) basePayoff := by
  intro hopt
  have hle := backwardValue_le_of_isOneShotOptimal hopt
    (policy .grab) Spot.flip (payoffIntegrable_of_finite _ _)
  rw [backwardValue_grab_base, backwardValue_pass_base] at hle
  norm_num at hle

/-- **The principle, applied.** Grabbing is at least as good as every chooser —
not merely as good as passing, and without comparing against any of them one by
one. -/
theorem grab_best (other : probe.Chooser) (state : Spot) :
    probe.backwardValue probe_wellFoundedPlay other basePayoff state
        (payoffIntegrable_of_finite _ _) ≤
      probe.backwardValue probe_wellFoundedPlay (policy .grab) basePayoff state
        (payoffIntegrable_of_finite _ _) :=
  backwardValue_le_of_isOneShotOptimal grab_isOneShotOptimal other state
    (payoffIntegrable_of_finite _ _)

/-- **And back again.** The principle is an equivalence: being best among all
choosers recovers the one-step condition, so nothing is lost by checking only
single actions. -/
theorem grab_isOneShotOptimal_of_best :
    probe.IsOneShotOptimal probe_wellFoundedPlay (policy .grab) basePayoff :=
  isOneShotOptimal_of_backwardValue_le (fun other state =>
    ⟨payoffIntegrable_of_finite _ _, payoffIntegrable_of_finite _ _,
      grab_best other state⟩)

/-- And the conclusion is not vacuous: passing really is worse at the root. -/
theorem pass_strictly_worse :
    probe.backwardValue probe_wellFoundedPlay (policy .pass) basePayoff Spot.flip
        (payoffIntegrable_of_finite _ _) <
      probe.backwardValue probe_wellFoundedPlay (policy .grab) basePayoff Spot.flip
        (payoffIntegrable_of_finite _ _) := by
  rw [backwardValue_flip, backwardValue_flip]
  norm_num [basePayoff, Move.outcome]

end GameTheory.Tests.OneShot
