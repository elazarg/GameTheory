/-
# EXP-142: a well-founded protocol with no uniform horizon

A Boolean decision at the initial history selects a geometric countdown. Every
realized play is finite, but the possible countdown lengths are unbounded.
-/

import GameTheory.Experimental.PostArchitecture.PMFRestorationProbe
import GameTheory.Protocol.BehavioralAssessment
import GameTheory.Protocol.Backward
import Mathlib.Data.Prod.Lex

noncomputable section

namespace GameTheory.Tests.WellFoundedTerminalGate

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability GameTheory.Experimental.PMFRestoration

/-- The only strategic choice leads to a random finite countdown. -/
inductive State
  | root
  | countdown (chosen : Bool) (remaining : ℕ)
  | done (chosen : Bool)
  deriving DecidableEq

/-- The chosen Boolean is retained until the terminal state. -/
def State.reward : State → ℝ
  | .done true => 1
  | .done false => 0
  | _ => 0

/-- A Boolean action is chosen only at the initial state. -/
@[reducible] def execution : ExecutionProtocol Unit where
  State := State
  Action _ := Bool
  init := .root
  active state _ := state = .root
  available state _ := if state = .root then Set.univ else ∅
  terminal state := ∃ chosen, state = .done chosen
  step state joint :=
    match state with
    | .root => geometric.map fun n => .countdown ((joint.1 ()).getD false) n
    | .countdown chosen (n + 1) => PMF.pure (.countdown chosen n)
    | .countdown chosen 0 => PMF.pure (.done chosen)
    | .done chosen => PMF.pure (.done chosen)
  progress := by
    intro state hterm
    cases state with
    | root =>
        refine ⟨fun _ => some false, ?_⟩
        intro who
        cases who
        exact ⟨rfl, Set.mem_univ _⟩
    | countdown chosen remaining =>
        refine ⟨fun _ => none, ?_⟩
        intro who
        cases who
        simp
    | done chosen => exact (hterm ⟨chosen, rfl⟩).elim

/-- The joint action taking the initial Boolean decision. -/
def rootJoint (chosen : Bool) : Unit → Option Bool := fun _ => some chosen

/-- The initial Boolean action is legal. -/
theorem rootJoint_legal (chosen : Bool) :
    execution.Legal .root (rootJoint chosen) := by
  constructor
  · simp
  · intro who
    cases who
    exact ⟨rfl, Set.mem_univ _⟩

/-- At countdown states only the no-op action is legal. -/
theorem countdownNoop_legal (chosen : Bool) (remaining : ℕ) :
    execution.Legal (.countdown chosen remaining) execution.noop := by
  constructor
  · simp
  · intro who
    cases who
    simp [ExecutionProtocol.noop]

/-- The geometric draw realizes every finite countdown. -/
theorem rootCountdown_realized (chosen : Bool) (remaining : ℕ) :
    .countdown chosen remaining ∈
      (execution.step .root ⟨rootJoint chosen, rootJoint_legal chosen⟩).support := by
  rw [PMF.support_map]
  exact ⟨remaining, by
    exact (geometric_positive remaining).ne', rfl⟩

/-- A countdown transition decreases its remaining duration by one. -/
theorem countdownNext_realized (chosen : Bool) (remaining : ℕ) :
    .countdown chosen remaining ∈
      (execution.step (.countdown chosen (remaining + 1))
        ⟨execution.noop, countdownNoop_legal chosen (remaining + 1)⟩).support := by
  simp [execution]

/-- The initial realized history after choosing and drawing a countdown. -/
def rootDecisionTrace (chosen : Bool) (remaining : ℕ) :
    Trace execution (.countdown chosen remaining) :=
  .extend Trace.start (rootJoint chosen) (rootJoint_legal chosen)
    (rootCountdown_realized chosen remaining)

/-- A history can spend any specified number of transitions descending the
countdown, leaving any smaller duration still to go. -/
def countdownTrace (chosen : Bool) : (elapsed remaining : ℕ) →
    Trace execution (.countdown chosen remaining)
  | 0, remaining => rootDecisionTrace chosen remaining
  | elapsed + 1, remaining =>
      .extend (countdownTrace chosen elapsed (remaining + 1)) execution.noop
        (countdownNoop_legal chosen (remaining + 1))
        (countdownNext_realized chosen remaining)

theorem countdownTrace_length (chosen : Bool) (elapsed remaining : ℕ) :
    (countdownTrace chosen elapsed remaining).length = elapsed + 1 := by
  induction elapsed generalizing remaining with
  | zero => rfl
  | succ elapsed ih => simp [countdownTrace, Trace.length, ih]

/-- There is no single finite bound for all realized histories. -/
theorem no_boundedHorizon : ¬ ∃ horizon, execution.BoundedHorizon horizon := by
  rintro ⟨horizon, bounded⟩
  have hlong : horizon ≤ (countdownTrace false horizon 0).length := by
    rw [countdownTrace_length]
    omega
  have hterminal := bounded (.countdown false 0) (countdownTrace false horizon 0) hlong
  obtain ⟨chosen, hEq⟩ := hterminal
  cases hEq

/-- The lexicographic rank puts the root above every countdown, then counts
remaining transitions; terminal outcomes sit below countdown zero. -/
def rank : State → ℕ ×ₗ ℕ
  | .root => toLex (1, 0)
  | .countdown _ remaining => toLex (0, remaining + 1)
  | .done _ => toLex (0, 0)

/-- Every realized transition strictly decreases the lexicographic rank. -/
theorem rank_decreases {source target : State}
    (hsuccessor : execution.Successor target source) : rank target < rank source := by
  obtain ⟨joint, legal, hrealized⟩ := hsuccessor
  cases source with
  | root =>
      obtain ⟨chosen, hchosen⟩ :=
        LegalOption.exists_eq_some_of_active (joint ())
          (execution.legalOption_of_legal legal ()) rfl
      have hjoint : joint = rootJoint chosen := funext (fun _ => hchosen)
      have hmem : target ∈ (geometric.map fun n => State.countdown chosen n).support := by
        simpa [execution, hjoint, rootJoint] using hrealized
      rw [PMF.mem_support_map_iff] at hmem
      obtain ⟨remaining, _, rfl⟩ := hmem
      simp [rank, Prod.Lex.toLex_lt_toLex]
  | countdown chosen remaining =>
      cases remaining with
      | zero =>
          have htarget : target = State.done chosen := by
            simpa [execution] using hrealized
          subst target
          simp [rank, Prod.Lex.toLex_lt_toLex]
      | succ remaining =>
          have htarget : target = State.countdown chosen remaining := by
            simpa [execution] using hrealized
          subst target
          simp [rank, Prod.Lex.toLex_lt_toLex]
  | done chosen =>
      exact (execution.terminal_no_legal (by exact ⟨chosen, rfl⟩) joint legal).elim

/-- Every realized play is well-founded, despite the lack of a uniform bound. -/
theorem wellFounded : execution.WellFoundedPlay :=
  Subrelation.wf rank_decreases (InvImage.wf rank WellFoundedRelation.wf)

/-- No legal transition returns to the initial decision state. -/
theorem root_not_mem_step (source : State)
    (joint : Unit → Option Bool) (legal : execution.Legal source joint) :
    State.root ∉ (execution.step source ⟨joint, legal⟩).support := by
  cases source with
  | root =>
      intro hroot
      have hmap : State.root ∈
          (geometric.map fun n => State.countdown ((joint ()).getD false) n).support :=
        hroot
      rw [PMF.mem_support_map_iff] at hmap
      obtain ⟨n, _, hEq⟩ := hmap
      cases hEq
  | countdown chosen remaining =>
      cases remaining <;> simp [execution]
  | done chosen =>
      exact (execution.terminal_no_legal (by exact ⟨chosen, rfl⟩)
        joint legal).elim

/-- The information state records whether the initial decision has passed.
Unused real values remain in the raw information carrier. -/
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

@[simp] theorem signals_infoOf_start :
    signals.infoOf () (Trace.start : Trace execution .root) = 1 := rfl

@[simp] theorem signals_infoOf_extend {source target : State}
    (prior : Trace execution source) (joint : Unit → Option Bool)
    (legal : execution.Legal source joint)
    (realized : target ∈ (execution.step source ⟨joint, legal⟩).support) :
    signals.infoOf () (.extend prior joint legal realized) = 0 := rfl

/-- The model uses the exact legal menu at both reachable information values;
other real values have the forced no-op menu. -/
@[reducible] def information : InformationModel execution where
  toInfoSignals := signals
  menu _ info := if info = 1 then {choice | ∃ action : Bool, choice = some action} else {none}
  menu_adequate := by
    intro who state trace choice
    cases trace with
    | start =>
        cases who
        cases choice with
        | none => simp [signals, execution, LegalOption]
        | some action => cases action <;> simp [signals, execution, LegalOption]
    | @extend source target prior joint legal realized =>
        cases who
        have hnot : state ≠ .root := by
          intro hEq
          subst state
          exact root_not_mem_step source joint legal realized
        cases choice with
        | none => simp [signals, InfoSignals.infoOf, execution, LegalOption, hnot]
        | some action =>
            simp [signals, InfoSignals.infoOf, execution, LegalOption, hnot]

/-- The only history at which the player can act is the initial history. -/
theorem active_history_eq_initHistory (history : execution.History)
    (hactive : execution.active history.state ()) :
    history = execution.initHistory := by
  rcases history with ⟨state, trace⟩
  cases trace with
  | start => rfl
  | @extend source target prior joint legal realized =>
      have hstate : state = State.root := hactive
      have hroot : State.root ∈
          (execution.step source ⟨joint, legal⟩).support := by
        simpa only [hstate] using realized
      exact False.elim (root_not_mem_step source joint legal hroot)

/-- The initial Boolean menu is the only decision information site. -/
def rootSite : information.InformationSite () :=
  ⟨1, ⟨⟨execution.initHistory, rfl⟩, by simp [execution], true,
    by simp⟩⟩

theorem informationSite_eq_rootSite
    (site : information.InformationSite ()) : site = rootSite := by
  apply Subtype.ext
  obtain ⟨_history, _hterm, action, hmenu⟩ := site.2
  by_contra hne
  have hwrong : some action ∈ (information.menu () site.1) := hmenu
  have hne' : site.1 ≠ (1 : ℝ) := by
    simpa only [rootSite] using hne
  simp [information, hne'] at hwrong

/-- Every decision-site belief fiber consists of the initial history alone. -/
theorem informationHistory_eq_initHistory
    (site : information.InformationSite ())
    (history : information.InformationHistory () site.1) :
    history.1 = execution.initHistory := by
  exact active_history_eq_initHistory history.1
    (GameTheory.Protocol.InformationModel.InformationSite.active
      information site history)

/-- The sole decision site's histories form an antichain. -/
theorem decisionInformationAntichain :
    information.DecisionInformationAntichain := by
  intro who site first second joint legal reached realized fuel hreach
  cases who
  have hfirst : first.1.trace.length = 0 := by
    rw [informationHistory_eq_initHistory site first]
    rfl
  have hsecond : second.1.trace.length = 0 := by
    rw [informationHistory_eq_initHistory site second]
    rfl
  have hlength := hreach.trace_length_le
  have hstep : (first.1.extend legal realized).trace.length =
      first.1.trace.length + 1 := rfl
  omega

end GameTheory.Tests.WellFoundedTerminalGate
