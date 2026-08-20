/-
# EXP-115: horizon-relative Kuhn realization

This hostile consumer has an infinite ambient information-state carrier.  Its
two-round behavioral run nevertheless has finite support and reaches two
distinct decision information states.  The stable bounded realization theorem
constructs a finite-support mixed witness without `Fintype InfoState`.
-/

import GameTheory.Protocol.Information

noncomputable section

namespace GameTheory.Experimental.KuhnFiniteSupport

open GameTheory.Math.Probability GameTheory.Protocol

/-- Two decision rounds over an infinite state and information carrier. -/
@[reducible]
def execution : ExecutionProtocol Unit where
  State := Nat
  Action _ := Bool
  init := 0
  active state _ := state < 2
  available _ _ := Set.univ
  terminal state := 2 ≤ state
  step state _ := FinDist.pure (state + 1)
  progress := by
    intro state hterm
    have hactive : state < 2 := Nat.lt_of_not_ge hterm
    exact ⟨fun _ => some false, fun _ => ⟨hactive, Set.mem_univ _⟩⟩

@[reducible]
def signals : InfoSignals execution where
  PublicSignal := Nat
  PrivateSignal _ := Unit
  initialPublic := 0
  initialPrivate _ := ()
  publicSignal event := event.target
  privateSignal _ _ := ()
  InfoState _ := Nat
  initInfo _ _ observed := observed
  pushInfo _ _ _ _ observed := observed

theorem infoOf_state : ∀ {state : Nat} (trace : execution.Trace state),
    signals.infoOf () trace = state
  | _, .start => rfl
  | _, .extend _ _ _ _ => rfl

def menuAt (info : Nat) : Set (Option Bool) :=
  if info < 2 then {some false, some true} else {none}

@[reducible]
def model : InformationModel execution where
  toInfoSignals := signals
  menu _ := menuAt
  menu_adequate := by
    rintro ⟨⟩ state trace choice
    rw [infoOf_state trace]
    by_cases hstate : state < 2
    · cases choice with
      | none => simp [menuAt, hstate, LegalOption, execution]
      | some action => cases action <;> simp [menuAt, hstate,
          LegalOption, execution]
    · cases choice with
      | none => simp [menuAt, hstate, LegalOption, execution]
      | some action => cases action <;> simp [menuAt, hstate,
          LegalOption, execution]

theorem target_eq_succ {source target : Nat}
    {joint : Unit → Option Bool} (isLegal : execution.Legal source joint)
    (realized : target ∈ (execution.step source ⟨joint, isLegal⟩).support) :
    target = source + 1 := by
  simpa [execution] using realized

theorem actedAt_eq_reverse_range : ∀ {state : Nat}
    (trace : execution.Trace state),
    signals.actedAt () trace = (List.range state).reverse
  | _, .start => rfl
  | target, .extend prior joint isLegal realized => by
      have hactive := Nat.lt_of_not_ge isLegal.1
      obtain ⟨action, haction⟩ :=
        LegalOption.exists_eq_some_of_active (joint ())
          (execution.legalOption_of_legal isLegal ()) hactive
      have htarget := target_eq_succ isLegal realized
      rw [InfoSignals.actedAt, haction,
        actedAt_eq_reverse_range prior, infoOf_state, htarget]
      simp [List.range_succ]

theorem actsOnce : model.ActsOnceWhereItMatters := by
  apply model.actsOnceWhereItMatters_of_actsOnce
  rintro ⟨⟩ state trace
  rw [actedAt_eq_reverse_range trace]
  exact List.nodup_reverse.mpr List.nodup_range

def behavioral : model.BehavioralPolicy () := fun info =>
  if hinfo : info < 2 then
    FinDist.mix (1 / 2) (by norm_num) (by norm_num)
      (FinDist.pure ⟨some false, by simp [menuAt, hinfo]⟩)
      (FinDist.pure ⟨some true, by simp [menuAt, hinfo]⟩)
  else
    FinDist.pure ⟨none, by simp [menuAt, hinfo]⟩

theorem infoState_infinite : Infinite (model.InfoState ()) := by
  infer_instance

/-- The bounded behavioral support reaches information state `1`, distinct
from the initial information state `0`. -/
theorem reaches_second_information_state :
    ∃ later ∈
        (model.runBehavioralFrom (fun _ => behavioral) 1
          execution.initHistory).support,
      model.infoOf () later.trace = 1 := by
  let profile : (i : Unit) → model.BehavioralPolicy i := fun _ => behavioral
  have hterm : ¬ execution.terminal execution.init := by simp
  obtain ⟨draw, hdraw⟩ :=
    (model.behavioralJoint profile execution.initHistory.trace hterm).support_nonempty
  obtain ⟨target, realized⟩ :=
    (execution.step execution.init draw).support_nonempty
  have htarget : target = 1 := by
    simpa [execution] using realized
  subst target
  let later := execution.initHistory.extend draw.2 realized
  refine ⟨later, ?_, ?_⟩
  · rw [model.runBehavioralFrom_succ_of_not_terminal profile 0 hterm,
      FinDist.support_bind]
    refine Set.mem_iUnion₂.mpr ⟨draw, hdraw, ?_⟩
    rw [FinDist.support_bindOnSupport]
    refine Set.mem_iUnion₂.mpr ⟨1, realized, ?_⟩
    simp [later, InformationModel.runBehavioralFrom]
  · rw [infoOf_state]
    rfl

/-- The new witness applies at two rounds although the ambient information
carrier is `Nat`, so no `Fintype (model.InfoState ())` can be supplied. -/
theorem twoRound_realization :
    ∃ mixed : (i : Unit) → model.MixedPolicy i,
      model.runMixed mixed 2 =
        model.runBehavioral (fun _ => behavioral) 2 :=
  model.exists_mixed_runMixed_eq_runBehavioral
    actsOnce (fun _ => behavioral) 2

end GameTheory.Experimental.KuhnFiniteSupport
