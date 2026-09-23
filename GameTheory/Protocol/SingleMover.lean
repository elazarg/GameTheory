/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Protocol.Information

/-! # Behavioral play with at most one active player

The canonical behavioral product assumes a finite player universe. When at
most one player is active, only that player's finite-support choice law is
needed, even for an infinite player carrier. The construction below drives the
existing randomized history runner and agrees with the canonical finite
product whenever both apply. No action carrier is required to be finite.
-/

noncomputable section

namespace GameTheory.Protocol

open GameTheory.Math.Probability ExecutionProtocol

universe uι us ua up uq uk

variable {ι : Type uι} [DecidableEq ι] {E : ExecutionProtocol.{uι, us, ua} ι}

namespace InformationModel

variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)
  (single : ∀ (state : E.State) {first second : ι},
    E.active state first → E.active state second → first = second)

open Classical in
/-- Randomize only the active coordinate. Chance steps have the unique idle
joint action and still execute the protocol's own stochastic transition. -/
def singleMoverJoint (profile : ∀ who, M.BehavioralPolicy who)
    (history : E.History) (running : ¬ E.terminal history.state) :
    FinDist {joint : ∀ who, Option (E.Action who) // E.Legal history.state joint} :=
  if active : ∃ who, E.active history.state who then
    (profile active.choose (M.infoOf active.choose history.trace)).map
      (M.jointOfChoice single history running active.choose active.choose_spec)
  else
    FinDist.pure ⟨fun _ => none, E.legal_of_legalOption running
      (fun who acts => active ⟨who, acts⟩)⟩

/-- Supply single-mover behavioral choices to the canonical randomized runner. -/
def singleMoverChooser (profile : ∀ who, M.BehavioralPolicy who) : E.RandomizedChooser :=
  fun history running => M.singleMoverJoint single profile history running

/-- Run single-mover behavioral play from a retained history for the supplied fuel. -/
def runSingleMoverBehavioralFrom (profile : ∀ who, M.BehavioralPolicy who)
    (fuel : ℕ) (history : E.History) : FinDist E.History :=
  E.runRandomizedFor (M.singleMoverChooser single profile) fuel history

/-- Each player's marginal is exactly its own information-local choice law.
The idle players' laws are point masses because their legal menu is a singleton. -/
theorem singleMoverJoint_marginal (profile : ∀ who, M.BehavioralPolicy who)
    (history : E.History) (running : ¬ E.terminal history.state) (who : ι) :
    (M.singleMoverJoint single profile history running).map (fun joint => joint.1 who) =
      (profile who (M.infoOf who history.trace)).map Subtype.val := by
  classical
  have idle (player : ι) (notActive : ¬ E.active history.state player) :
      (profile player (M.infoOf player history.trace)).map Subtype.val = FinDist.pure none := by
    calc
      _ = (profile player (M.infoOf player history.trace)).map (fun _ => none) := by
        apply FinDist.map_congr_of_eq_on_support
        intro choice _
        exact LegalOption.eq_none_of_inactive choice.1
          ((M.menu_adequate player history.trace choice.1).mp choice.2) notActive
      _ = _ := by simp [FinDist.map_eq_bind]
  by_cases active : ∃ player, E.active history.state player
  · rw [singleMoverJoint, dite_eq_left active, FinDist.map_comp]
    by_cases own : who = active.choose
    · subst who
      congr 1
      funext choice
      simp [jointOfChoice, singletonJoint]
    · have notActive : ¬ E.active history.state who :=
        fun acts => own (single history.state acts active.choose_spec)
      rw [idle who notActive]
      simp [jointOfChoice, singletonJoint, own, FinDist.map_eq_bind]
  · rw [singleMoverJoint, dite_eq_right active, FinDist.map_pure,
      idle who (fun acts => active ⟨who, acts⟩)]

/-- The single-mover construction is the canonical behavioral product when
the ambient player universe is finite. -/
theorem singleMoverJoint_eq_behavioralJoint [Fintype ι]
    (profile : ∀ who, M.BehavioralPolicy who) (history : E.History)
    (running : ¬ E.terminal history.state) :
    M.singleMoverJoint single profile history running =
      M.behavioralJoint profile history.trace running := by
  classical
  by_cases active : ∃ who, E.active history.state who
  · rw [singleMoverJoint, dite_eq_left active]
    exact (M.behavioralJoint_eq_map_of_at_most_one_active profile history.trace running
      active.choose (fun who acts => single history.state acts active.choose_spec)).symm
  · rw [singleMoverJoint, dite_eq_right active]
    exact (M.behavioralJoint_eq_pure_of_no_active profile history.trace running
      (fun who acts => active ⟨who, acts⟩)).symm

theorem runSingleMoverBehavioralFrom_eq_runBehavioralFrom [Fintype ι]
    (profile : ∀ who, M.BehavioralPolicy who) (fuel : ℕ) (history : E.History) :
    M.runSingleMoverBehavioralFrom single profile fuel history =
      M.runBehavioralFrom profile fuel history := by
  apply E.runRandomizedFor_congr
  exact fun next running => M.singleMoverJoint_eq_behavioralJoint single profile next running

/-- Pure policies embed without any finiteness premise on players. -/
theorem singleMoverJoint_toBehavioral (profile : ∀ who, M.Policy who)
    (history : E.History) (running : ¬ E.terminal history.state) :
    M.singleMoverJoint single (fun who => (profile who).toBehavioral) history running =
      FinDist.pure (M.historyChooser profile history running) := by
  classical
  have inactive (who : ι) (notActive : ¬ E.active history.state who) :
      M.jointAt profile history.trace who = none :=
    LegalOption.eq_none_of_inactive _
      (E.legalOption_of_legal (M.jointAt_legal profile history.trace running) who) notActive
  by_cases active : ∃ who, E.active history.state who
  · rw [singleMoverJoint, dite_eq_left active, Policy.toBehavioral, FinDist.map_pure]
    apply congrArg FinDist.pure
    apply Subtype.ext
    funext who
    by_cases own : who = active.choose
    · subst who
      simp [jointOfChoice, ExecutionProtocol.singletonJoint, historyChooser, jointAt, Policy.act]
    · have notActive : ¬ E.active history.state who :=
        fun acts => own (single history.state acts active.choose_spec)
      simp only [jointOfChoice, ExecutionProtocol.singletonJoint, own, dite_false, historyChooser]
      exact (inactive who notActive).symm
  · rw [singleMoverJoint, dite_eq_right active]
    apply congrArg FinDist.pure
    apply Subtype.ext
    funext who
    exact (inactive who (fun acts => active ⟨who, acts⟩)).symm

theorem runSingleMoverBehavioralFrom_toBehavioral (profile : ∀ who, M.Policy who)
    (fuel : ℕ) (history : E.History) :
    M.runSingleMoverBehavioralFrom single (fun who => (profile who).toBehavioral) fuel history =
      M.runFrom profile fuel history := by
  rw [runSingleMoverBehavioralFrom, show M.singleMoverChooser single
      (fun who => (profile who).toBehavioral) = (M.historyChooser profile).toRandomized from
    funext fun next => funext fun running =>
      M.singleMoverJoint_toBehavioral single profile next running]
  exact E.runRandomizedFor_toRandomized _ _ _

end InformationModel
end GameTheory.Protocol
