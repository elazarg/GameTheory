/-
# Zermelo decision-menu boundary

This one-step protocol has one finite decision menu and an unreachable
information value whose menu is infinite. It is the hostile witness that
backward induction needs finiteness only where a decision can actually occur;
the unavoidable total contingent plan is supplied explicitly as a fallback.
-/

import GameTheory.Protocol.Zermelo

noncomputable section

namespace GameTheory.Tests.ZermeloMenus

open GameTheory.Protocol GameTheory.Math.Probability

@[reducible] def execution : ExecutionProtocol Unit where
  State := Bool
  Action _ := Nat
  init := false
  active state _ := state = false
  available _ _ := {0}
  terminal state := state = true
  step _ _ := FinDist.pure true
  progress := by
    intro state hterm
    cases state
    · exact ⟨fun _ => some 0, fun _ => by simp⟩
    · simp at hterm

@[reducible] def signals : InfoSignals execution where
  PublicSignal := Bool
  PrivateSignal _ := Unit
  initialPublic := false
  initialPrivate _ := ()
  publicSignal event := event.target
  privateSignal _ _ := ()
  InfoState _ := Nat
  initInfo _ _ observed := if observed then 1 else 0
  pushInfo _ _ _ _ observed := if observed then 1 else 0

theorem infoOf_state : ∀ {state : Bool} (trace : execution.Trace state),
    signals.infoOf () trace = if state then 1 else 0
  | _, .start => rfl
  | _, .extend _ _ _ _ => rfl

def menu : Nat → Set (Option Nat)
  | 0 => {some 0}
  | 1 => {none}
  | _ => Set.univ

@[reducible] def information : InformationModel execution where
  toInfoSignals := signals
  menu _ := menu
  menu_adequate := by
    intro _ state trace choice
    rw [infoOf_state]
    cases state <;> cases choice <;>
      simp [menu, LegalOption, execution]

/-- The unreachable information value `2` really has infinitely many legal
local choices, so this fixture cannot satisfy the former global finiteness
premise. -/
theorem unreachable_choices_infinite :
    Infinite (information.Choice () 2) := by
  apply Infinite.of_injective
    (fun action : Nat =>
      (⟨some action, by simp [menu]⟩ :
        information.Choice () 2))
  intro first second heq
  exact Option.some.inj (congrArg Subtype.val heq)

def fallback : Profile information.strategicSignature :=
  fun _ info => match info with
    | 0 => ⟨some 0, by simp [menu]⟩
    | 1 => ⟨none, by simp [menu]⟩
    | _ + 2 => ⟨none, by simp [menu]⟩

private theorem choice_zero_subsingleton :
    Subsingleton (information.Choice () 0) :=
  information.subsingleton_choice_of_menu_subsingleton 0 (by
    intro first hfirst second hsecond
    simpa [information, menu] using hfirst.trans hsecond.symm)

/-- Only the menu at information value `0` needs to be finite. -/
theorem finiteDecisionChoices : information.HasFiniteDecisionChoices := by
  intro who info history hdecision
  cases who
  have hstate : history.state = false := by
    simpa [execution] using hdecision.2.1
  have hinfo : info = 0 := by
    rw [← hdecision.2.2, infoOf_state, hstate]
    rfl
  subst info
  letI := choice_zero_subsingleton
  exact Finite.of_surjective (fun _ : Unit => fallback () 0)
    (fun choice => ⟨(), Subsingleton.elim _ choice⟩)

theorem singleMover (state : Bool) {first second : Unit}
    (_ : execution.active state first) (_ : execution.active state second) :
    first = second := by
  cases first
  cases second
  rfl

private theorem init_not_mem_step (source : Bool)
    (joint : Unit → Option Nat) (isLegal : execution.Legal source joint) :
    false ∉ (execution.step source ⟨joint, isLegal⟩).support := by
  simp [execution]

private theorem legal_joint_eq (source : Bool) (joint : Unit → Option Nat)
    (isLegal : execution.Legal source joint) : joint () = some 0 := by
  have hsource : source = false := by
    simpa [execution] using isLegal.1
  subst source
  have hcoordinate := execution.legalOption_of_legal isLegal ()
  cases hchoice : joint () with
  | none => simp [LegalOption, hchoice] at hcoordinate
  | some action =>
      simp [LegalOption, execution, hchoice] at hcoordinate
      simp [hcoordinate]

private theorem predecessor_unique {target firstSource secondSource : Bool}
    {firstJoint secondJoint : Unit → Option Nat}
    (firstLegal : execution.Legal firstSource firstJoint)
    (secondLegal : execution.Legal secondSource secondJoint)
    (_ : target ∈ (execution.step firstSource ⟨firstJoint, firstLegal⟩).support)
    (_ : target ∈
      (execution.step secondSource ⟨secondJoint, secondLegal⟩).support) :
    firstSource = secondSource ∧ firstJoint = secondJoint := by
  have hfirst : firstSource = false := by
    simpa [execution] using firstLegal.1
  have hsecond : secondSource = false := by
    simpa [execution] using secondLegal.1
  refine ⟨hfirst.trans hsecond.symm, ?_⟩
  funext who
  cases who
  exact (legal_joint_eq firstSource firstJoint firstLegal).trans
    (legal_joint_eq secondSource secondJoint secondLegal).symm

theorem treeShaped : execution.IsTreeShaped :=
  execution.isTreeShaped_of_predecessor_unique init_not_mem_step
    predecessor_unique

theorem perfect : information.SeparatesDecisionHistories := by
  intro who first second _ hfirst _ hsecond _
  cases who
  have hfirstState : first.state = false := by
    simpa [execution] using hfirst
  have hsecondState : second.state = false := by
    simpa [execution] using hsecond
  rcases first with ⟨firstState, firstTrace⟩
  rcases second with ⟨secondState, secondTrace⟩
  dsimp at hfirstState hsecondState
  subst firstState
  subst secondState
  congr
  exact @Subsingleton.elim _ (treeShaped false) firstTrace secondTrace

def rank : Bool → Nat
  | false => 1
  | true => 0

theorem wellFoundedPlay : execution.WellFoundedPlay := by
  apply execution.wellFoundedPlay_of_rank rank
  intro source target successor
  rcases successor with ⟨joint, isLegal, realized⟩
  have hsource : source = false := by
    simpa [execution] using isLegal.1
  subst source
  have htarget : target = true := by
    simpa [execution] using realized
  subst target
  decide

def utility : execution.History → Unit → ℝ := fun _ _ => 0

/-- Backward induction constructs an SPE despite the infinite unreachable
choice carrier; only the explicit total fallback supplies its unused value. -/
theorem exists_subgamePerfect :
    ∃ profile : Profile information.strategicSignature,
      information.IsSubgamePerfect wellFoundedPlay profile utility :=
  information.exists_isSubgamePerfect singleMover fallback
    finiteDecisionChoices wellFoundedPlay perfect utility

/-- At the infinite unreachable menu, the constructed policy is exactly the
caller's fallback rather than the result of an impossible maximization. -/
theorem backwardPolicy_two_eq_fallback :
    information.backwardPolicy singleMover fallback finiteDecisionChoices
        wellFoundedPlay utility () 2 = fallback () 2 := by
  apply information.backwardPolicy_eq_fallback_of_no_decision_history
  rintro ⟨history, _, hactive, hinfo⟩
  have hstate : history.state = false := by
    simpa [execution] using hactive
  rw [infoOf_state, hstate] at hinfo
  simp at hinfo

end GameTheory.Tests.ZermeloMenus
