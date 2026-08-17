/-
# EXP-113: countability of finite protocol histories

Finite traces are countable whenever the state carrier and every action
carrier are countable and the player index is finite.  The encoding below
retains every realized transition, in reverse order, together with the final
state.  The endpoint is included so that the indexed trace can be compared
without introducing transports between state indices.
-/

import GameTheory.Protocol.History

noncomputable section

namespace GameTheory.Protocol.ExecutionProtocol

open GameTheory.Protocol
open GameTheory.Protocol.ExecutionProtocol

universe uι us ua

variable {ι : Type uι} {E : ExecutionProtocol ι}

variable (E)

/-- The realized transitions of a trace, with the most recent transition
first. -/
def Trace.reverseEvents : ∀ {state : E.State}, E.Trace state → List E.StepEvent
  | _, .start => []
  | _, .extend prior joint isLegal realized =>
      ⟨_, joint, isLegal, _, realized⟩ :: reverseEvents prior

@[simp]
theorem Trace.reverseEvents_start :
    Trace.reverseEvents E (Trace.start : E.Trace E.init) = [] := rfl

@[simp]
theorem Trace.reverseEvents_extend {source target : E.State}
    (prior : E.Trace source) (joint : ∀ i, Option (E.Action i))
    (isLegal : E.Legal source joint)
    (realized : target ∈ (E.step source ⟨joint, isLegal⟩).support) :
    Trace.reverseEvents E (Trace.extend prior joint isLegal realized) =
      ⟨source, joint, isLegal, target, realized⟩ ::
        Trace.reverseEvents E prior := rfl

private theorem stepEvent_code_injective :
    Function.Injective (fun event : E.StepEvent =>
      (event.source, event.joint, event.target)) := by
  intro first second h
  cases first with
  | mk firstSource firstJoint firstLegal firstTarget firstRealized =>
      cases second with
      | mk secondSource secondJoint secondLegal secondTarget secondRealized =>
          simp only [Prod.mk.injEq] at h
          rcases h with ⟨hsource, hjoint, htarget⟩
          cases hsource
          cases hjoint
          cases htarget
          rfl

private theorem countable_stepEvent [Fintype ι] [Countable E.State]
    [∀ i, Countable (E.Action i)] : Countable E.StepEvent := by
  apply Function.Injective.countable (@stepEvent_code_injective ι E)

private theorem countable_stepEvent_list [Fintype ι] [Countable E.State]
    [∀ i, Countable (E.Action i)] : Countable (List E.StepEvent) := by
  letI : Countable E.StepEvent := countable_stepEvent E
  infer_instance

private theorem history_code_injective [Fintype ι] [Countable E.State]
    [∀ i, Countable (E.Action i)] :
    Function.Injective (fun history : E.History =>
      (Trace.reverseEvents E history.trace, history.state)) := by
  intro first second hcode
  cases first with
  | mk firstState firstTrace =>
      cases second with
      | mk secondState secondTrace =>
          dsimp at hcode
          have hstate : firstState = secondState := congrArg Prod.snd hcode
          subst secondState
          have hevents : Trace.reverseEvents E firstTrace =
              Trace.reverseEvents E secondTrace := congrArg Prod.fst hcode
          have trace_injective : ∀ {state : E.State}
              (first second : E.Trace state),
              Trace.reverseEvents E first = Trace.reverseEvents E second →
              first = second := by
            intro state first
            induction first with
            | start =>
                intro second hevents
                cases second with
                | start => rfl
                | extend prior joint isLegal realized =>
                    simp at hevents
            | @extend source target prior joint isLegal realized ih =>
                intro second hevents
                cases second with
                | start =>
                    simp at hevents
                | @extend secondSource _ secondPrior secondJoint secondLegal
                    secondRealized =>
                    simp only [Trace.reverseEvents] at hevents
                    injection hevents with hevent hprior
                    have hsource : source = secondSource :=
                      congrArg StepEvent.source hevent
                    have hjoint : joint = secondJoint :=
                      congrArg StepEvent.joint hevent
                    cases hsource
                    cases hjoint
                    have hpriorEq := ih secondPrior hprior
                    cases hpriorEq
                    rfl
          congr
          exact trace_injective firstTrace secondTrace hevents

theorem historyCountable [Fintype ι] [Countable E.State]
    [∀ i, Countable (E.Action i)] : Countable E.History := by
  letI : Countable E.StepEvent := countable_stepEvent E
  exact Function.Injective.countable
    (f := fun history : E.History =>
      (Trace.reverseEvents E history.trace, history.state))
    (@history_code_injective ι E inferInstance inferInstance inferInstance)

private def finiteUnitOptionBool : ExecutionProtocol Unit where
  State := Option Bool
  Action := fun _ => Unit
  init := none
  active := fun _ _ => False
  available := fun _ _ => Set.univ
  terminal := fun _ => False
  step := fun state _ => GameTheory.Math.Probability.FinDist.pure state
  progress := by
    intro state hterminal
    exact ⟨fun _ => none, by simp [IsLegalJoint]⟩

/-- Concrete finite-carrier control for the countability seam. -/
theorem finiteUnitOptionBool_historyCountable :
    Countable finiteUnitOptionBool.History := by
  letI : Countable finiteUnitOptionBool.State := by
    dsimp [finiteUnitOptionBool]
    infer_instance
  letI : ∀ i, Countable (finiteUnitOptionBool.Action i) := by
    intro i
    dsimp [finiteUnitOptionBool]
    infer_instance
  exact finiteUnitOptionBool.historyCountable

end GameTheory.Protocol.ExecutionProtocol
