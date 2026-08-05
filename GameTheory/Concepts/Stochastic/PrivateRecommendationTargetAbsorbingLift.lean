/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Correlation.PrivateRecommendationTargetSeparator
import GameTheory.Concepts.Stochastic.Absorbing

/-!
# The one-decision absorbing lift of the private-recommendation separator

This file realizes the strategic-form matrix in
`PrivateRecommendationTargetSeparator.lean` as a four-state stochastic game.
The decision state moves immediately to one of three absorbing states.  The
expected absorbing payoff, conditional on every pure first action, is
exactly that action's strategic-form payoff.

More strongly, after fixing the action at every visit to the decision state,
the expected average payoff equals the same strategic-form payoff at every
positive finite horizon.  The behavior profile away from the decision state is
arbitrary, so history and memory after absorption cannot change this identity.

This is a payoff-preserving stochastic lift only.  It defines no private
recommendation device, proves no autonomous correlated equilibrium, and proves
no compiler or noncompiler theorem.
-/

noncomputable section

open scoped BigOperators

namespace GameTheory
namespace StochasticGame
namespace PrivateRecommendationTargetAbsorbingLift

open Math.Probability Math.PMFProduct

abbrev Player := Bool
abbrev Action (_ : Player) := Bool

/-- The strategic-form payoff being lifted. -/
abbrev matrixPayoff : (Player → Bool) → Player → ℝ :=
  KernelGame.PrivateRecommendationTargetSeparator.payoff

/-- One decision state and three absorbing payoff states. -/
inductive State
  | decision
  | z0
  | z1
  | z2
  deriving DecidableEq, Fintype

private theorem sum_state {M : Type} [AddCommMonoid M] (f : State → M) :
    ∑ state, f state =
      f .decision + f .z0 + f .z1 + f .z2 := by
  classical
  rw [show (Finset.univ : Finset State) =
      {.decision, .z0, .z1, .z2} by decide]
  simp [add_assoc]

/-- Payoff vector attached to an absorbing state.  The value at `.decision`
is unused by this function and set to zero. -/
def absorbingPayoff (state : State) (who : Player) : ℝ :=
  match state with
  | .decision => 0
  | .z0 => 1
  | .z1 => if who then -1 else 1
  | .z2 => if who then 1 else -1

/-- Real-valued transition weights from the decision state. -/
def decisionRealWeight (action : Player → Bool) (state : State) : ℝ :=
  match state with
  | .decision => 0
  | .z0 =>
      if action false then
        if action true then 6 / 7 else 9 / 14
      else if action true then 9 / 14 else 0
  | .z1 =>
      if action false then
        if action true then 1 / 14 else 0
      else if action true then 5 / 14 else 1 / 2
  | .z2 =>
      if action false then
        if action true then 1 / 14 else 5 / 14
      else if action true then 0 else 1 / 2

private theorem decisionRealWeight_nonneg (action : Player → Bool)
    (state : State) :
    0 ≤ decisionRealWeight action state := by
  cases state <;> cases hOne : action false <;> cases hTwo : action true <;>
    simp [decisionRealWeight, hOne, hTwo] <;> norm_num

private theorem decisionRealWeight_sum (action : Player → Bool) :
    ∑ state, decisionRealWeight action state = 1 := by
  rw [sum_state]
  cases hOne : action false <;> cases hTwo : action true <;>
    simp [decisionRealWeight, hOne, hTwo] <;> norm_num

/-- Extended-nonnegative weights used to build the transition `PMF`. -/
def decisionWeight (action : Player → Bool) (state : State) : ENNReal :=
  ENNReal.ofReal (decisionRealWeight action state)

private theorem decisionWeight_sum (action : Player → Bool) :
    ∑ state, decisionWeight action state = 1 := by
  change (∑ state, ENNReal.ofReal (decisionRealWeight action state)) = 1
  rw [← ENNReal.ofReal_sum_of_nonneg
    (fun state _ => decisionRealWeight_nonneg action state),
    decisionRealWeight_sum]
  norm_num

/-- The public absorbing-state lottery conditional on the first joint action. -/
def decisionTransition (action : Player → Bool) : PMF State :=
  PMF.ofFintype (decisionWeight action) (decisionWeight_sum action)

@[simp] theorem decisionTransition_apply (action : Player → Bool)
    (state : State) :
    decisionTransition action state = decisionWeight action state := by
  simp [decisionTransition, PMF.ofFintype_apply]

/-- Transition kernel: the decision is made once, and every other state is
absorbing. -/
def transition (state : State) (action : Player → Bool) : PMF State :=
  match state with
  | .decision => decisionTransition action
  | .z0 => PMF.pure .z0
  | .z1 => PMF.pure .z1
  | .z2 => PMF.pure .z2

/-- The decision stage uses the static separator payoff; absorbing stages use
their state payoff and ignore actions. -/
def stagePayoff (state : State) (action : Player → Bool)
    (who : Player) : ℝ :=
  match state with
  | .decision => matrixPayoff action who
  | .z0 | .z1 | .z2 => absorbingPayoff state who

/-- The four-state one-decision stochastic game. -/
abbrev game : StochasticGame Player where
  State := State
  Act := Action
  stagePayoff := stagePayoff
  transition := transition
  discount := 0
  discount_nonneg := le_rfl
  discount_lt_one := zero_lt_one

private instance : Finite game.State := inferInstanceAs (Finite State)
private instance (who : Player) : Finite (game.Act who) :=
  inferInstanceAs (Finite Bool)

@[simp] theorem transition_z0 (action : game.JointAct) :
    game.transition .z0 action = PMF.pure .z0 := rfl

@[simp] theorem transition_z1 (action : game.JointAct) :
    game.transition .z1 action = PMF.pure .z1 := rfl

@[simp] theorem transition_z2 (action : game.JointAct) :
    game.transition .z2 action = PMF.pure .z2 := rfl

theorem z0_isAbsorbing : game.IsAbsorbingState .z0 := transition_z0

theorem z1_isAbsorbing : game.IsAbsorbingState .z1 := transition_z1

theorem z2_isAbsorbing : game.IsAbsorbingState .z2 := transition_z2

/-- The absorbing lottery reproduces the static payoff of every pure action
profile exactly. -/
theorem expect_absorbingPayoff_decisionTransition
    (action : Player → Bool) (who : Player) :
    expect (decisionTransition action) (fun state => absorbingPayoff state who) =
      matrixPayoff action who := by
  rw [expect_eq_sum, sum_state]
  simp only [decisionTransition_apply, decisionWeight]
  simp_rw [ENNReal.toReal_ofReal (decisionRealWeight_nonneg action _)]
  cases hOne : action false <;> cases hTwo : action true <;> cases who <;>
    simp [decisionRealWeight, absorbingPayoff,
      matrixPayoff, KernelGame.PrivateRecommendationTargetSeparator.payoff,
      hOne, hTwo] <;> norm_num

/-! ## Exact finite-horizon transport -/

/-- The value attached to the chosen decision action: its matrix payoff at the
decision state and the realized absorbing payoff elsewhere. -/
def fixedActionValue (action : Player → Bool) (state : State)
    (who : Player) : ℝ :=
  match state with
  | .decision => matrixPayoff action who
  | .z0 | .z1 | .z2 => absorbingPayoff state who

@[simp] theorem decisionTransition_decision (action : Player → Bool) :
    decisionTransition action .decision = 0 := by
  simp [decisionTransition_apply, decisionWeight, decisionRealWeight]

/-- At the decision state, the chosen action's transition preserves its
matrix payoff as the expected fixed-action value. -/
theorem expect_fixedActionValue_decisionTransition
    (action : Player → Bool) (who : Player) :
    expect (decisionTransition action)
        (fun state => fixedActionValue action state who) =
      matrixPayoff action who := by
  rw [Math.ProbabilityMassFunction.expect_congr_on_support
    (decisionTransition action)
    (fun state => fixedActionValue action state who)
    (fun state => absorbingPayoff state who)]
  · exact expect_absorbingPayoff_decisionTransition action who
  · intro state hstate
    cases state with
    | decision =>
        exfalso
        exact hstate (by simp [decisionWeight, decisionRealWeight])
    | z0 => rfl
    | z1 => rfl
    | z2 => rfl

/-- Away from the decision state, the fixed-action value is preserved by every
action because those states are absorbing. -/
theorem expect_fixedActionValue_terminal
    (prescribed played : Player → Bool) (who : Player) {state : State}
    (hterminal : state ≠ .decision) :
    expect (game.transition state played)
        (fun next => fixedActionValue prescribed next who) =
      fixedActionValue prescribed state who := by
  cases state <;> simp_all [transition, fixedActionValue]

/-- Force `action` whenever the current state is the decision state and leave
the supplied continuation profile completely unchanged at all absorbing
states. -/
def rootForcedProfile (action : Player → Bool)
    (continuation : game.BehaviorProfile) : game.BehaviorProfile :=
  fun who time history =>
    if history.2 = .decision then PMF.pure (action who)
    else continuation who time history

theorem stageActionDist_rootForcedProfile_of_decision
    (action : Player → Bool) (continuation : game.BehaviorProfile)
    {time : ℕ} (history : game.Hist time)
    (hstate : history.2 = .decision) :
    game.stageActionDist (rootForcedProfile action continuation) history =
      PMF.pure action := by
  unfold StochasticGame.stageActionDist
  have hcoordinates :
      (fun who => rootForcedProfile action continuation who time history) =
        (fun who => PMF.pure (action who)) := by
    funext who
    simp [rootForcedProfile, hstate]
  rw [hcoordinates, pmfPi_pure]

/-- The fixed-action value is one-step harmonic under `rootForcedProfile` at
every history. -/
theorem rootForcedProfile_oneStepValue
    (action : Player → Bool) (continuation : game.BehaviorProfile)
    {time : ℕ} (history : game.Hist time) (who : Player) :
    expect (game.stageActionDist (rootForcedProfile action continuation) history)
        (fun played =>
          expect (game.transition history.2 played)
            (fun next => fixedActionValue action next who)) =
      fixedActionValue action history.2 who := by
  by_cases hstate : history.2 = .decision
  · rw [stageActionDist_rootForcedProfile_of_decision action continuation
      history hstate, expect_pure, hstate]
    exact expect_fixedActionValue_decisionTransition action who
  · have hpointwise : ∀ played : game.JointAct,
        expect (game.transition history.2 played)
            (fun next => fixedActionValue action next who) =
          fixedActionValue action history.2 who :=
      fun played => expect_fixedActionValue_terminal action played who hstate
    simp_rw [hpointwise]
    exact expect_const _ _

/-- The expected stage payoff after any history is the fixed-action value of
its current state. -/
theorem stageEUAt_rootForcedProfile
    (action : Player → Bool) (continuation : game.BehaviorProfile)
    {time : ℕ} (history : game.Hist time) (who : Player) :
    game.stageEUAt (rootForcedProfile action continuation) history who =
      fixedActionValue action history.2 who := by
  unfold StochasticGame.stageEUAt
  by_cases hstate : history.2 = .decision
  · rw [stageActionDist_rootForcedProfile_of_decision action continuation
      history hstate, expect_pure, hstate]
    rfl
  · have hpointwise : ∀ played : game.JointAct,
        game.stagePayoff history.2 played who =
          fixedActionValue action history.2 who := by
      intro played
      cases hs : history.2 <;> simp_all [stagePayoff, fixedActionValue]
    calc
      expect
          (game.stageActionDist (rootForcedProfile action continuation) history)
          (fun played => game.stagePayoff history.2 played who) =
          expect
            (game.stageActionDist (rootForcedProfile action continuation) history)
            (fun _ => fixedActionValue action history.2 who) := by
        congr 1
        funext played
        exact hpointwise played
      _ = fixedActionValue action history.2 who := expect_const _ _

/-- The expected fixed-action value is constant at every decision epoch. -/
theorem expectedStateValue_rootForcedProfile
    (action : Player → Bool) (continuation : game.BehaviorProfile)
    (time : ℕ) (who : Player) :
    game.expectedStateValue (rootForcedProfile action continuation)
        .decision time (fun state => fixedActionValue action state who) =
      matrixPayoff action who := by
  induction time with
  | zero => simp [fixedActionValue]
  | succ time ih =>
      rw [game.expectedStateValue_succ]
      simp_rw [rootForcedProfile_oneStepValue action continuation]
      exact ih

/-- Every expected stage payoff, including the first, equals the static matrix
payoff of the forced decision action. -/
theorem expectedStagePayoff_rootForcedProfile
    (action : Player → Bool) (continuation : game.BehaviorProfile)
    (time : ℕ) (who : Player) :
    game.expectedStagePayoff (rootForcedProfile action continuation)
        .decision time who = matrixPayoff action who := by
  rw [show game.expectedStagePayoff (rootForcedProfile action continuation)
        .decision time who =
      game.expectedStateValue (rootForcedProfile action continuation)
        .decision time (fun state => fixedActionValue action state who) by
      unfold expectedStagePayoff expectedStateValue
      congr 1
      funext history
      exact stageEUAt_rootForcedProfile action continuation history who]
  exact expectedStateValue_rootForcedProfile action continuation time who

/-- **Exact horizonwise lift.** Conditional on a fixed first action, every
positive-horizon average payoff is exactly its strategic-form payoff.  The
continuation may use arbitrary history-dependent private randomization because
all post-decision states are already absorbing and action-independent. -/
theorem finiteAveragePayoff_rootForcedProfile
    (action : Player → Bool) (continuation : game.BehaviorProfile)
    (horizon : ℕ) (hpositive : 1 ≤ horizon) (who : Player) :
    game.finiteAveragePayoff .decision horizon
        (rootForcedProfile action continuation) who =
      matrixPayoff action who := by
  have hne : (horizon : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [game.finiteAveragePayoff_eq_sum_expectedStagePayoff,
    Finset.sum_congr rfl fun time _ =>
      expectedStagePayoff_rootForcedProfile action continuation time who,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ hne, one_mul]

/-- At horizon zero the library's averaging convention returns zero, so the
exact transport theorem correctly starts at positive horizons. -/
theorem finiteAveragePayoff_rootForcedProfile_zero
    (action : Player → Bool) (continuation : game.BehaviorProfile)
    (who : Player) :
    game.finiteAveragePayoff .decision 0
        (rootForcedProfile action continuation) who = 0 := by
  simp

/-! ## Arbitrary mixed root laws -/

/-- The independent mixed action selected by an arbitrary behavior profile at
the unique initial decision history. -/
def rootMixedProfile (profile : game.BehaviorProfile) :
    KernelGame.PrivateRecommendationTargetSeparator.MixedProfile :=
  fun who => profile who 0 (game.emptyHist .decision)

@[simp] theorem stageActionDist_emptyHist_decision
    (profile : game.BehaviorProfile) :
    game.stageActionDist profile (game.emptyHist .decision) =
      pmfPi (rootMixedProfile profile) :=
  rfl

/-- Extracting the initial mixed action commutes with unilateral behavioral
replacement.  Only the deviator's action at the empty decision history
survives in the extracted strategic-form profile. -/
theorem rootMixedProfile_update
    (profile : game.BehaviorProfile) (who : Player)
    (deviation : game.BehaviorStrategy who) :
    rootMixedProfile (Function.update profile who deviation) =
      Function.update (rootMixedProfile profile) who
        (deviation 0 (game.emptyHist .decision)) := by
  funext other
  by_cases hother : other = who
  · subst other
    simp [rootMixedProfile]
  · simp [rootMixedProfile, Function.update_of_ne hother]

/-- Every nondecision state in the lift is absorbing. -/
theorem terminal_isAbsorbing {state : State} (hterminal : state ≠ .decision) :
    game.IsAbsorbingState state := by
  cases state with
  | decision => exact (hterminal rfl).elim
  | z0 => exact z0_isAbsorbing
  | z1 => exact z1_isAbsorbing
  | z2 => exact z2_isAbsorbing

/-- From a terminal state, arbitrary history-dependent behavior has the
constant absorbing payoff at every stage. -/
theorem expectedStagePayoff_terminal
    (profile : game.BehaviorProfile) {state : State}
    (hterminal : state ≠ .decision) (time : ℕ) (who : Player) :
    game.expectedStagePayoff profile state time who =
      absorbingPayoff state who := by
  unfold StochasticGame.expectedStagePayoff
  have heq : ∀ history ∈ (game.histDist profile state time).support,
      game.stageEUAt profile history who = absorbingPayoff state who := by
    intro history hhistory
    have hstate :
        history.2 = state :=
      game.snd_eq_of_mem_support_histDist_of_isAbsorbingState
        (terminal_isAbsorbing hterminal) profile time history hhistory
    unfold StochasticGame.stageEUAt
    rw [hstate]
    have hpointwise : ∀ action : game.JointAct,
        game.stagePayoff state action who = absorbingPayoff state who := by
      intro action
      cases state <;> simp_all [stagePayoff]
    have hfun :
        (fun action => game.stagePayoff state action who) =
          (fun _ => absorbingPayoff state who) :=
      funext hpointwise
    rw [hfun]
    exact expect_const _ _
  rw [Math.ProbabilityMassFunction.expect_congr_on_support
      (game.histDist profile state time)
      (fun history => game.stageEUAt profile history who)
      (fun _ => absorbingPayoff state who) heq,
    expect_const]

/-- At stage zero, an arbitrary behavior profile earns the static mixed payoff
of its extracted independent root law. -/
theorem expectedStagePayoff_zero_eq_mixedRoot
    (profile : game.BehaviorProfile) (who : Player) :
    game.expectedStagePayoff profile .decision 0 who =
      KernelGame.PrivateRecommendationTargetSeparator.game.mixedExtension.eu
        (rootMixedProfile profile) who := by
  unfold StochasticGame.expectedStagePayoff StochasticGame.stageEUAt
  rw [game.histDist_zero, expect_pure,
    stageActionDist_emptyHist_decision,
    KernelGame.PrivateRecommendationTargetSeparator.game.mixedExtension_eu]
  simp [StochasticGame.emptyHist, stagePayoff, matrixPayoff,
    KernelGame.eu_ofPureEU]

/-- After the first decision, every possible successor is terminal, so the
expected payoff at every later stage is still the static mixed payoff of the
initial independent root law. -/
theorem expectedStagePayoff_succ_eq_mixedRoot
    (profile : game.BehaviorProfile) (time : ℕ) (who : Player) :
    game.expectedStagePayoff profile .decision (time + 1) who =
      KernelGame.PrivateRecommendationTargetSeparator.game.mixedExtension.eu
        (rootMixedProfile profile) who := by
  unfold StochasticGame.expectedStagePayoff
  rw [game.histDist_succ_shift profile .decision time, expect_bind,
    stageActionDist_emptyHist_decision,
    KernelGame.PrivateRecommendationTargetSeparator.game.mixedExtension_eu]
  simp only [KernelGame.eu_ofPureEU]
  apply congrArg (expect (pmfPi (rootMixedProfile profile)))
  funext action
  rw [expect_bind]
  change
    expect (decisionTransition action)
        (fun state =>
          expect
            ((game.histDist
                (game.shiftProfile profile (.decision, action)) state time).map
              (game.consHist (.decision, action)))
            (fun history => game.stageEUAt profile history who)) =
      matrixPayoff action who
  simp_rw [expect_map]
  rw [Math.ProbabilityMassFunction.expect_congr_on_support
      (decisionTransition action)
      (fun state =>
        expect
          (game.histDist
            (game.shiftProfile profile (.decision, action)) state time)
          (fun history =>
            game.stageEUAt profile
              (game.consHist (.decision, action) history) who))
      (fun state => absorbingPayoff state who)]
  · exact expect_absorbingPayoff_decisionTransition action who
  · intro state hstate
    have hterminal : state ≠ .decision := by
      intro hdecision
      subst state
      exact hstate (by simp [decisionWeight, decisionRealWeight])
    have hshift :
        expect
            (game.histDist
              (game.shiftProfile profile (.decision, action)) state time)
            (fun history =>
              game.stageEUAt profile
                (game.consHist (.decision, action) history) who) =
          game.expectedStagePayoff
            (game.shiftProfile profile (.decision, action)) state time who := by
      rfl
    rw [hshift, expectedStagePayoff_terminal _ hterminal]

/-- Every stage payoff of an arbitrary profile is determined solely by its
independent mixed action at the initial decision history. -/
theorem expectedStagePayoff_eq_mixedRoot
    (profile : game.BehaviorProfile) (time : ℕ) (who : Player) :
    game.expectedStagePayoff profile .decision time who =
      KernelGame.PrivateRecommendationTargetSeparator.game.mixedExtension.eu
        (rootMixedProfile profile) who := by
  cases time with
  | zero => exact expectedStagePayoff_zero_eq_mixedRoot profile who
  | succ time => exact expectedStagePayoff_succ_eq_mixedRoot profile time who

/-- **Arbitrary-root horizonwise lift.** At every positive horizon, the
stochastic payoff of any behavior profile is exactly the strategic-form mixed
payoff of its independently randomized initial action. -/
theorem finiteAveragePayoff_eq_mixedRoot
    (profile : game.BehaviorProfile) (horizon : ℕ)
    (hpositive : 1 ≤ horizon) (who : Player) :
    game.finiteAveragePayoff .decision horizon profile who =
      KernelGame.PrivateRecommendationTargetSeparator.game.mixedExtension.eu
        (rootMixedProfile profile) who := by
  have hne : (horizon : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [game.finiteAveragePayoff_eq_sum_expectedStagePayoff,
    Finset.sum_congr rfl fun time _ =>
      expectedStagePayoff_eq_mixedRoot profile time who,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ hne, one_mul]

/-- The behavioral deviation that always chooses the separator's action `D`.
Only its value at the initial decision history matters in this lift. -/
def pureDDeviation (who : Player) : game.BehaviorStrategy who :=
  fun _ _ => PMF.pure false

@[simp] theorem rootMixedProfile_update_pureD
    (profile : game.BehaviorProfile) (who : Player) :
    rootMixedProfile
        (Function.update profile who (pureDDeviation who)) =
      Function.update (rootMixedProfile profile) who (PMF.pure false) := by
  rw [rootMixedProfile_update]
  rfl

/-- The mediated target `(5/7,5/7)` is not a uniform-equilibrium payoff of
the ordinary one-decision absorbing lift.

This is deliberately target-specific.  The game has other ordinary uniform
equilibrium payoffs, so no target-free nonexistence interface applies. -/
theorem privateRecommendationTarget_not_isUniformEquilibriumPayoff :
    ¬ game.IsUniformEquilibriumPayoff .decision (fun _ => 5 / 7) := by
  intro huniform
  let ε : ℝ :=
    KernelGame.PrivateRecommendationTargetSeparator.deltaStar / 4
  have hε : 0 < ε := by
    dsimp [ε]
    exact div_pos
      KernelGame.PrivateRecommendationTargetSeparator.deltaStar_pos
      (by norm_num)
  obtain ⟨profile, threshold, hprofile⟩ := huniform ε hε
  let horizon : ℕ := max threshold 1
  have hthreshold : threshold ≤ horizon := by
    exact Nat.le_max_left _ _
  have hpositive : 1 ≤ horizon := by
    exact Nat.le_max_right _ _
  obtain ⟨hNash, hdelivery⟩ :=
    hprofile horizon hthreshold
  have hdeliveryε : ∀ who,
      |KernelGame.PrivateRecommendationTargetSeparator.game.mixedExtension.eu
          (rootMixedProfile profile) who - 5 / 7| ≤ ε := by
    intro who
    rw [← finiteAveragePayoff_eq_mixedRoot
      profile horizon hpositive who]
    simpa using hdelivery who
  have hcapOne :
      KernelGame.PrivateRecommendationTargetSeparator.game.mixedExtension.eu
          (Function.update (rootMixedProfile profile) false (PMF.pure false))
          false ≤
        5 / 7 + 2 * ε := by
    have hdeviation := hNash false (pureDDeviation false)
    rw [finiteAveragePayoff_eq_mixedRoot
          profile horizon hpositive false,
      finiteAveragePayoff_eq_mixedRoot
        (Function.update profile false (pureDDeviation false))
        horizon hpositive false,
      rootMixedProfile_update_pureD] at hdeviation
    have hbaseUpper := (abs_le.mp (hdeliveryε false)).2
    have hbase :
        KernelGame.PrivateRecommendationTargetSeparator.game.mixedExtension.eu
            (rootMixedProfile profile) false ≤ 5 / 7 + ε :=
      by linarith
    calc
      KernelGame.PrivateRecommendationTargetSeparator.game.mixedExtension.eu
          (Function.update (rootMixedProfile profile) false (PMF.pure false))
          false ≤
          KernelGame.PrivateRecommendationTargetSeparator.game.mixedExtension.eu
              (rootMixedProfile profile) false + ε :=
        hdeviation
      _ ≤ (5 / 7 + ε) + ε := by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_right hbase ε
      _ = 5 / 7 + 2 * ε := by ring
  have hcapTwo :
      KernelGame.PrivateRecommendationTargetSeparator.game.mixedExtension.eu
          (Function.update (rootMixedProfile profile) true (PMF.pure false))
          true ≤
        5 / 7 + 2 * ε := by
    have hdeviation := hNash true (pureDDeviation true)
    rw [finiteAveragePayoff_eq_mixedRoot
          profile horizon hpositive true,
      finiteAveragePayoff_eq_mixedRoot
        (Function.update profile true (pureDDeviation true))
        horizon hpositive true,
      rootMixedProfile_update_pureD] at hdeviation
    have hbaseUpper := (abs_le.mp (hdeliveryε true)).2
    have hbase :
        KernelGame.PrivateRecommendationTargetSeparator.game.mixedExtension.eu
            (rootMixedProfile profile) true ≤ 5 / 7 + ε :=
      by linarith
    calc
      KernelGame.PrivateRecommendationTargetSeparator.game.mixedExtension.eu
          (Function.update (rootMixedProfile profile) true (PMF.pure false))
          true ≤
          KernelGame.PrivateRecommendationTargetSeparator.game.mixedExtension.eu
              (rootMixedProfile profile) true + ε :=
        hdeviation
      _ ≤ (5 / 7 + ε) + ε := by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_right hbase ε
      _ = 5 / 7 + 2 * ε := by ring
  have hdeliveryTwo : ∀ who,
      |KernelGame.PrivateRecommendationTargetSeparator.game.mixedExtension.eu
          (rootMixedProfile profile) who - 5 / 7| ≤ 2 * ε := by
    intro who
    calc
      |KernelGame.PrivateRecommendationTargetSeparator.game.mixedExtension.eu
          (rootMixedProfile profile) who - 5 / 7| ≤ ε :=
        hdeliveryε who
      _ ≤ 2 * ε := by linarith
  have hgap :=
    KernelGame.PrivateRecommendationTargetSeparator.deltaStar_le_of_mixed_delivery_and_pureDCaps
        (rootMixedProfile profile)
        (delta := 2 * ε)
        (by positivity)
        hdeliveryTwo
        hcapOne
        hcapTwo
  dsimp [ε] at hgap
  have hpositiveGap :=
    KernelGame.PrivateRecommendationTargetSeparator.deltaStar_pos
  linarith

end PrivateRecommendationTargetAbsorbingLift
end StochasticGame
end GameTheory
