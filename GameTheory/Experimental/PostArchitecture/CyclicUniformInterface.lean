/-
# EXP-114: an all-phase uniform interface for cyclic stochastic games

This is an experiment-only interface.  A phase is a canonical finite history,
and its continuation is obtained with the existing restart operation.  Thus
the definition quantifies over the canonical stochastic-game histories rather
than introducing another runner or identifying uniformity with terminal
subgame perfection.
-/

import GameTheory.Stochastic.History
import GameTheory.Experimental.PostArchitecture.StochasticInfinitePlayMeasure

noncomputable section

universe uι us ua

namespace GameTheory.Stochastic.Game

open GameTheory.Math.Probability
open GameTheory.Protocol.InformationModel
open GameTheory.Experimental.PostArchitecture.StochasticInfinitePlayMeasure.Game

variable {ι : Type uι} (G : Game.{uι, us, ua} ι)

/-- Uniformity at every canonical finite phase, using the existing restart
operation to obtain the phase continuation profile.  The initial phase is
included by the canonical initial history, so this is a bundled strengthening
of the ordinary initial-phase predicate, not a coercion from it. -/
def IsAllPhaseUniformεEquilibrium [Fintype ι] [DecidableEq ι]
    (initial : G.State) [∀ i, Nonempty (G.Action i)]
    (epsilon : ℝ) (profile : G.BehaviorProfile initial) : Prop :=
  ∀ history : CanonicalHistory G initial,
    G.IsUniformεEquilibrium history.state epsilon
      (G.afterPublicHistory (restart := history.state) profile
        (G.publicHistoryOfTrace initial history.trace))

/-- The all-phase certificate contains the initial-phase certificate at the
canonical empty history. -/
theorem IsAllPhaseUniformεEquilibrium.initial
    [Fintype ι] [DecidableEq ι] (initial : G.State)
    [∀ i, Nonempty (G.Action i)] {epsilon : ℝ}
    {profile : G.BehaviorProfile initial}
    (h : G.IsAllPhaseUniformεEquilibrium initial epsilon profile) :
    G.IsUniformεEquilibrium initial epsilon profile := by
  unfold IsAllPhaseUniformεEquilibrium at h
  have hzero := h (G.toExecution initial).initHistory
  have hzero' : G.IsUniformεEquilibrium initial epsilon
      (G.afterPublicHistory (restart := initial) profile []) := hzero
  rw [G.afterPublicHistory_nil] at hzero'
  exact hzero'

/-- A one-action cyclic game is a positive witness for the all-phase
interface: every restart has the same unique behavioral deviation. -/
private theorem behavioralPolicy_subsingleton
    (G : Game ι) (initial : G.State) [∀ i, Nonempty (G.Action i)]
    [∀ i, Subsingleton (G.Action i)] (who : ι) :
    Subsingleton ((G.perfectMonitoring initial).BehavioralPolicy who) := by
  constructor
  intro first second
  funext info
  have hchoice :
      Subsingleton ((G.perfectMonitoring initial).Choice who info) := by
    apply GameTheory.Protocol.InformationModel.subsingleton_choice_of_menu_subsingleton
    intro firstChoice hfirst secondChoice hsecond
    simp only [Game.activeMenu] at hfirst hsecond
    rcases hfirst with ⟨firstAction, hfirst⟩
    rcases hsecond with ⟨secondAction, hsecond⟩
    cases hfirst
    cases hsecond
    congr 1
    exact Subsingleton.elim _ _
  let choice : (G.perfectMonitoring initial).Choice who info :=
    ⟨some (Classical.choice (inferInstance : Nonempty (G.Action who))),
      by simp [Game.activeMenu]⟩
  rw [FinDist.eq_pure_of_subsingleton (first info) choice,
    FinDist.eq_pure_of_subsingleton (second info) choice]

private theorem unitAction_profile_update_eq
    (G : Game ι) (initial : G.State)
    [DecidableEq ι]
    [∀ i, Nonempty (G.Action i)]
    [∀ i, Subsingleton (G.Action i)]
    (profile : G.BehaviorProfile initial) (who : ι)
    (replacement : (G.perfectMonitoring initial).BehavioralPolicy who) :
    Profile.update profile who replacement = profile := by
  letI : Subsingleton ((G.perfectMonitoring initial).BehavioralPolicy who) :=
    behavioralPolicy_subsingleton G initial who
  rw [show replacement = profile who from
    Subsingleton.elim _ _]
  exact Profile.update_eq_self profile who

theorem isUniformεEquilibrium_of_unitAction
    (G : Game ι) (initial : G.State)
    [Fintype ι] [DecidableEq ι]
    [∀ i, Nonempty (G.Action i)]
    [∀ i, Subsingleton (G.Action i)]
    (profile : G.BehaviorProfile initial) {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) :
    G.IsUniformεEquilibrium initial epsilon profile := by
  unfold IsUniformεEquilibrium Math.EventuallyAtAll
  refine ⟨0, fun horizon _ => ?_⟩
  show G.IsεHorizonNash initial horizon epsilon profile
  rw [G.isεHorizonNash_iff]
  intro who replacement
  rw [unitAction_profile_update_eq G initial profile who replacement]
  linarith

/-- The cyclic unit-action game used as the positive witness. Its state loops
forever, so it is nonterminal; the certified property remains the existing
eventual finite-horizon uniformity predicate. -/
@[reducible]
def unitCycle : Game Unit where
  State := Unit
  Action := fun _ => Unit
  transition _ _ := FinDist.pure ()
  stageUtility _ _ _ := 0

local instance unitCycleActionNonempty :
    ∀ i, Nonempty ((unitCycle : Game Unit).Action i) :=
  fun _ => ⟨()⟩

theorem unitCycle_allPhase_uniform (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    (unitCycle : Game Unit).IsAllPhaseUniformεEquilibrium () epsilon
      (fun _ => fun _ => FinDist.pure ⟨some (), by simp [Game.activeMenu]⟩) := by
  unfold IsAllPhaseUniformεEquilibrium
  intro history
  apply isUniformεEquilibrium_of_unitAction
  exact hepsilon

end GameTheory.Stochastic.Game
