/-
# Sequential equilibrium over infinite carriers

One player picks `0` or `1` at the root. Actions are natural numbers, states are
optional natural numbers, and information states are real numbers, so none of
these carriers is finite. Only three legal histories exist, and that alone
supplies a consistent, sequentially rational assessment.
-/

import GameTheory.Analysis.Protocol.SequentialExistence
import GameTheory.Protocol.FiniteHorizon

noncomputable section

namespace GameTheory.Tests.InfiniteCarrierExistence

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

/-- The root is `none`; `some a` records the chosen action and ends play. -/
@[reducible] def execution : ExecutionProtocol Unit where
  State := Option ℕ
  Action _ := ℕ
  init := none
  active state _ := state = none
  available state _ := if state = none then {a | a ≤ 1} else ∅
  terminal state := ∃ a, state = some a
  step state joint :=
    match state with
    | none => PMF.pure (some ((joint.1 ()).getD 0))
    | some a => PMF.pure (some a)
  progress := by
    intro state hterm
    cases state with
    | none =>
        refine ⟨fun _ => some 0, ?_⟩
        intro who
        cases who
        exact ⟨rfl, by simp⟩
    | some a => exact (hterm ⟨a, rfl⟩).elim

/-- The information state records whether the decision has passed. -/
@[reducible] def signals : InfoSignals execution where
  PublicSignal := Unit
  PrivateSignal _ := Unit
  initialPublic := ()
  initialPrivate _ := ()
  publicSignal _ := ()
  privateSignal _ _ := ()
  InfoState _ := ℝ
  initInfo _ _ _ := 1
  pushInfo _ _ _ _ _ := 0

theorem root_not_mem_step (source : Option ℕ)
    (joint : Unit → Option ℕ) (legal : execution.Legal source joint) :
    (none : Option ℕ) ∉ (execution.step source ⟨joint, legal⟩).support := by
  cases source <;> simp [execution]

/-- The menu at the root is the two legal actions; every other real value has
the forced no-op menu. -/
@[reducible] def information : InformationModel execution where
  toInfoSignals := signals
  menu _ info := if info = 1 then {choice | ∃ a, a ≤ 1 ∧ choice = some a} else {none}
  menu_adequate := by
    intro who state trace choice
    cases trace with
    | start =>
        cases who
        cases choice with
        | none => simp [signals, execution, LegalOption]
        | some a => simp [signals, execution, LegalOption]
    | @extend source target prior joint legal realized =>
        cases who
        have hnot : state ≠ none := by
          intro hEq
          subst state
          exact root_not_mem_step source joint legal realized
        cases choice with
        | none => simp [signals, InfoSignals.infoOf, execution, LegalOption, hnot]
        | some a => simp [signals, InfoSignals.infoOf, execution, LegalOption, hnot]

/-- Choosing `a` at the root. -/
def chooseJoint (a : ℕ) : Unit → Option ℕ := fun _ => some a

theorem chooseJoint_legal {a : ℕ} (ha : a ≤ 1) :
    execution.Legal none (chooseJoint a) := by
  refine ⟨by simp, ?_⟩
  intro who
  cases who
  exact ⟨rfl, by simpa [execution] using ha⟩

theorem choose_realized {a : ℕ} (ha : a ≤ 1) :
    some a ∈ (execution.step none ⟨chooseJoint a, chooseJoint_legal ha⟩).support := by
  simp [execution, chooseJoint]

/-- The history that chose `a`. -/
def chosen {a : ℕ} (ha : a ≤ 1) : execution.History :=
  execution.initHistory.extend (chooseJoint_legal ha) (choose_realized ha)

/-- Every history is the root or one of the two choices. -/
theorem history_cases (history : execution.History) :
    history = execution.initHistory ∨ ∃ (a : ℕ) (ha : a ≤ 1), history = chosen ha := by
  rcases history with ⟨state, trace⟩
  cases trace with
  | start => exact Or.inl rfl
  | @extend source target prior joint legal realized =>
      right
      cases prior with
      | @extend before middle earlier earlierJoint earlierLegal earlierRealized =>
          exfalso
          apply legal.1
          cases before <;>
            simp only [execution, PMF.support_pure, Set.mem_singleton_iff] at earlierRealized <;>
            exact ⟨_, earlierRealized⟩
      | start =>
          obtain ⟨a, ha⟩ : ∃ a, joint () = some a := by
            cases hjoint : joint () with
            | none =>
                have hlegal := legal.2 ()
                simp [hjoint] at hlegal
            | some a => exact ⟨a, rfl⟩
          have hle : a ≤ 1 := by
            have hlegal := legal.2 ()
            simpa [ha] using hlegal
          have hjoint : joint = chooseJoint a := funext fun who => by cases who; exact ha
          subst hjoint
          have hstate : state = some a := by
            simpa [execution, chooseJoint] using realized
          subst hstate
          exact ⟨a, hle, rfl⟩

instance : Finite execution.History := by
  let code : Option (Fin 2) → execution.History
    | none => execution.initHistory
    | some k => chosen (Nat.lt_succ_iff.mp k.isLt)
  refine Finite.of_surjective code fun history => ?_
  rcases history_cases history with rfl | ⟨a, ha, rfl⟩
  · exact ⟨none, rfl⟩
  · exact ⟨some ⟨a, Nat.lt_succ_of_le ha⟩, rfl⟩

/-- None of the state, action, and information-state carriers is finite. -/
theorem carriers_infinite :
    Infinite execution.State ∧ Infinite (execution.Action ()) ∧
      Infinite (information.InfoState ()) :=
  ⟨inferInstanceAs (Infinite (Option ℕ)), inferInstanceAs (Infinite ℕ),
    inferInstanceAs (Infinite ℝ)⟩

/-- Only the root carries the information value `1`. -/
theorem eq_initHistory_of_info_one (history : execution.History)
    (hinfo : information.infoOf () history.trace = 1) :
    history = execution.initHistory := by
  rcases history_cases history with h | ⟨a, ha, rfl⟩
  · exact h
  · have hzero : information.infoOf () (chosen ha).trace = 0 := rfl
    rw [hzero] at hinfo
    norm_num at hinfo

/-- Decision recall holds: the only decision information value is the root's. -/
theorem decisionRecall : information.DecisionRecall := by
  rintro ⟨⟩ site first second
  obtain ⟨witness, hnonterminal, action, haction⟩ := site.2
  have hsite : site.1 = 1 := by
    by_contra hne
    simp [information, hne] at haction
  rw [eq_initHistory_of_info_one first.1 (first.2.trans hsite),
    eq_initHistory_of_info_one second.1 (second.2.trans hsite)]

/-- Choose `0` at the root and the forced no-op elsewhere. -/
def fallback : (i : Unit) → information.Policy i := fun _ info =>
  if h : info = 1 then ⟨some 0, by simp [h]⟩ else ⟨none, by simp [h]⟩

/-- **Sequential equilibrium exists** although the state, action, and
information-state carriers are all infinite. -/
theorem exists_sequentialEquilibrium (payoff : Unit → execution.History → ℝ) :
    ∃ assessment : information.BehavioralAssessment,
      assessment.IsSequentiallyRational
          (let _ := Fintype.ofFinite execution.History
           execution.wellFoundedHistories_of_fintype) payoff ∧
        assessment.IsSequentiallyConsistent decisionRecall.decisionInformationAntichain :=
  information.exists_sequentialEquilibrium decisionRecall fallback payoff _

end GameTheory.Tests.InfiniteCarrierExistence
