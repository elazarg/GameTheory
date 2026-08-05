/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.PunishmentLevel
import GameTheory.Concepts.Stochastic.QuittingSimpleBranches

/-!
# Punishment Levels in Quitting Games

Specializes `StochasticGame.punishmentLevel` to the quitting subclass at the
active state.  The clean form proved here is a **ceiling**: a player's
punishment level never exceeds the larger of zero and their own singleton
quitting reward, because opponents who commit to never quitting already
force it.  Under the all-continue opponent profile, the only terminal state
any response can reach is the deviator's own singleton quitter state (this
is `QuittingSimpleBranches.lean`'s exact `Never` test), so the resulting
finite-horizon average is capped at every horizon, with no limiting
argument.

This is a bound "in the right direction" rather than an exact
characterization: computing the punishment level exactly would require
optimizing over every opponent hazard law, not just the all-continue one,
and is out of scope here.

## Main results

* `StochasticGame.finiteAveragePayoff_le_of_forall_expectedStagePayoff_le` —
  a uniform per-stage bound below horizon `T` bounds the finite-horizon
  average (the finite-horizon analogue of
  `StochasticGame.discountedPayoff_le_of_forall_expectedStagePayoff_le`)
* `finiteAveragePayoff_update_quittingAlwaysContinue_le_max` — the finite-`T`
  analogue of `quittingTerminalPayoff_update_quittingAlwaysContinue_le_max`
* `punishmentLevel_quittingGame_le_max` — the punishment-level ceiling
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- If every per-stage expected payoff below horizon `T` is at most a
nonnegative bound `M`, the finite-horizon average payoff is at most `M`
too.  The finite-horizon analogue of
`discountedPayoff_le_of_forall_expectedStagePayoff_le`. -/
theorem StochasticGame.finiteAveragePayoff_le_of_forall_expectedStagePayoff_le
    (G : StochasticGame ι) [Finite G.State] [∀ i, Finite (G.Act i)]
    (σ : G.BehaviorProfile) (s₀ : G.State) (who : ι) (T : ℕ) {M : ℝ}
    (hM0 : 0 ≤ M)
    (hbound : ∀ t < T, G.expectedStagePayoff σ s₀ t who ≤ M) :
    G.finiteAveragePayoff s₀ T σ who ≤ M := by
  rw [G.finiteAveragePayoff_eq_sum_expectedStagePayoff]
  rcases Nat.eq_zero_or_pos T with hT0 | hTpos
  · subst hT0
    simpa using hM0
  · have hsum : ∑ t ∈ Finset.range T, G.expectedStagePayoff σ s₀ t who ≤
        (T : ℝ) * M := by
      calc ∑ t ∈ Finset.range T, G.expectedStagePayoff σ s₀ t who
          ≤ ∑ _t ∈ Finset.range T, M :=
            Finset.sum_le_sum fun t ht => hbound t (Finset.mem_range.mp ht)
        _ = (T : ℝ) * M := by
            simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    calc (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, G.expectedStagePayoff σ s₀ t who
        ≤ (T : ℝ)⁻¹ * ((T : ℝ) * M) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = M := by field_simp

/-- The finite-horizon analogue of
`quittingTerminalPayoff_update_quittingAlwaysContinue_le_max`: at every
finite horizon `T`, not just in the limit, a unilateral deviation from the
all-continue profile pays `who` at most the larger of zero and their own
singleton quitting reward.  Every reachable state under such a deviation is
either still active or the deviator's own singleton terminal state
(`state_eq_none_or_singleton_of_mem_support_update_quittingAlwaysContinue`),
so every one of the `T` stage payoffs already obeys the bound. -/
theorem finiteAveragePayoff_update_quittingAlwaysContinue_le_max
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who : ι) (deviation : (quittingGame reward).BehaviorStrategy who) (T : ℕ) :
    (quittingGame reward).finiteAveragePayoff none T
        (Function.update (quittingAlwaysContinueProfile reward) who deviation) who ≤
      max 0 (reward (quittingSingletonTerminal who) who) := by
  letI : Finite (quittingGame reward).State :=
    inferInstanceAs (Finite (Option {S : Finset ι // S.Nonempty}))
  letI : ∀ player : ι, Finite ((quittingGame reward).Act player) :=
    fun _ => inferInstanceAs (Finite Bool)
  let profile :=
    Function.update (quittingAlwaysContinueProfile reward) who deviation
  change (quittingGame reward).finiteAveragePayoff none T profile who ≤ _
  apply (quittingGame reward).finiteAveragePayoff_le_of_forall_expectedStagePayoff_le
    profile none who T (le_max_left _ _)
  intro t _ht
  unfold StochasticGame.expectedStagePayoff
  apply Math.ProbabilityMassFunction.expect_le_of_le_on_support
  intro h hh
  rw [stageEUAt_quittingGame_eq_stateReward]
  rcases state_eq_none_or_singleton_of_mem_support_update_quittingAlwaysContinue
      reward who deviation t h (by simpa [profile] using hh) with
    hnone | hsingleton
  · rw [hnone]; exact le_max_left _ _
  · rw [hsingleton]; exact le_max_right _ _

/-- **Punishment-level ceiling for quitting games.**  At the active state,
player `who`'s punishment level at any horizon `T` is at most the larger of
zero and their own singleton quitting reward: opponents who always continue
already force this ceiling, since `who`'s own singleton state is the only
terminal state reachable under any of `who`'s responses.

The punishment level quantifies over *every* opponent coordination
(`punishmentLevel`'s infimum), not only the all-continue one, so this is a
one-directional bound: the true min-max value could be lower still if some
other opponent hazard law punishes `who` harder. -/
theorem punishmentLevel_quittingGame_le_max
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι)
    {C : ℝ} (hC : ∀ S, |reward S who| ≤ C) (T : ℕ) :
    (quittingGame reward).punishmentLevel none T who ≤
      max 0 (reward (quittingSingletonTerminal who) who) := by
  haveI : Nonempty ((quittingGame reward).Act who) :=
    inferInstanceAs (Nonempty Bool)
  have hCstage : ∀ s a, |(quittingGame reward).stagePayoff s a who| ≤ max 0 C := by
    intro s a
    cases s with
    | none =>
        show |(quittingGame reward).stagePayoff none a who| ≤ max 0 C
        rw [show (quittingGame reward).stagePayoff none a who = 0 from rfl, abs_zero]
        exact le_max_left 0 C
    | some S => exact (hC S).trans (le_max_right 0 C)
  have hbdd : BddBelow
      (Set.range ((quittingGame reward).bestResponseAverageAgainstProfile
        none T who)) :=
    ⟨-(max 0 C), by
      rintro _ ⟨τ, rfl⟩
      exact (abs_le.mp ((quittingGame reward).abs_bestResponseAverageAgainstProfile_le
        (le_max_left 0 C) hCstage none T τ)).1⟩
  calc (quittingGame reward).punishmentLevel none T who
      ≤ (quittingGame reward).bestResponseAverageAgainstProfile none T who
          (quittingAlwaysContinueProfile reward) := by
        unfold StochasticGame.punishmentLevel
        exact ciInf_le hbdd (quittingAlwaysContinueProfile reward)
    _ ≤ max 0 (reward (quittingSingletonTerminal who) who) := by
        unfold StochasticGame.bestResponseAverageAgainstProfile
        haveI := (quittingGame reward).nonempty_behaviorStrategy who
        exact ciSup_le fun dev =>
          finiteAveragePayoff_update_quittingAlwaysContinue_le_max reward who dev T

end GameTheory
