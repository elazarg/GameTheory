/-
# Chance-rooted Zermelo integration witness

Nature first selects a live branch or a terminal branch with equal positive
probability. On the live branch, immediate exit pays `5`, while continuing
reaches a second decision where reward pays `1` and punishment pays `0`.
Backward induction must therefore prescribe exit on path and reward at the
consequential off-path decision. The test exercises chance, global contingent
plans, perfect-information separation, and the public EFG existence theorem.
-/

import GameTheory.Languages.EFG.Zermelo

noncomputable section

namespace GameTheory.Tests.EFGZermelo

open GameTheory.Languages GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Protocol.ExecutionProtocol

set_option backward.isDefEq.respectTransparency false in
inductive State
  | chance | left | second | right | exited | lnone | lpunish | lreward
  | punished | rewarded | snone | sexit | scontinue
  deriving DecidableEq, Fintype

set_option backward.isDefEq.respectTransparency false in
inductive Action | exit | continue | punish | reward deriving DecidableEq, Fintype

def fairCoin : PMF State := mix (1 / 2) (by norm_num) (by norm_num)
  (PMF.pure .left) (PMF.pure .right)

theorem fairCoin_support (s : State) : s ∈ fairCoin.support ↔
    s = .left ∨ s = .right := by
  cases s <;> simp [fairCoin, PMF.mem_support_iff, mix_apply, PMF.pure_apply]
  all_goals norm_num

def next : State → Option Action → State
  | .left, none => .lnone
  | .left, some .exit => .exited
  | .left, some .continue => .second
  | .left, some .punish => .lpunish
  | .left, some .reward => .lreward
  | .second, none => .snone
  | .second, some .exit => .sexit
  | .second, some .continue => .scontinue
  | .second, some .punish => .punished
  | .second, some .reward => .rewarded
  | state, _ => state

@[reducible] def execution : ExecutionProtocol Unit where
  State := State
  Action _ := Action
  init := .chance
  active s _ := s = .left ∨ s = .second
  available s _ := match s with
    | .left => {Action.exit, .continue}
    | .second => {Action.punish, .reward}
    | _ => Set.univ
  terminal
    | .chance | .left | .second => False
    | _ => True
  step s joint := match s with
    | .chance => fairCoin
    | state => PMF.pure (next state (joint.1 ()))
  progress := by
    intro s ht
    cases s <;> simp_all
    · exact ⟨fun _ => none, fun _ => by simp⟩
    · exact ⟨fun _ => some .exit, fun _ => by simp⟩
    · exact ⟨fun _ => some .punish, fun _ => by simp⟩

theorem chance_not_terminal : ¬ execution.terminal .chance := by simp

theorem init_not_mem_step (s : State) (j : Unit → Option Action)
    (hj : execution.Legal s j) : State.chance ∉ (execution.step s ⟨j, hj⟩).support := by
  cases s with
  | chance =>
      intro hmem
      exact (fairCoin_support .chance).mp hmem |>.elim (by simp) (by simp)
  | left =>
      cases hc : j () with
      | none => simp [execution, next, hc]
      | some action => cases action <;> simp [execution, next, hc]
  | second =>
      cases hc : j () with
      | none => simp [execution, next, hc]
      | some action => cases action <;> simp [execution, next, hc]
  | right | exited | lnone | lpunish | lreward | punished | rewarded |
      snone | sexit | scontinue => exact False.elim (hj.1 True.intro)

def sourceOf : State → Option State
  | .chance => none
  | .left | .right => some .chance
  | .second | .exited | .lnone | .lpunish | .lreward => some .left
  | .punished | .rewarded | .snone | .sexit | .scontinue => some .second

theorem sourceOf_mem_step {t s : State} {j : Unit → Option Action}
    (hj : execution.Legal s j)
    (hr : t ∈ (execution.step s ⟨j, hj⟩).support) :
    sourceOf t = some s := by
  cases s with
  | chance =>
      rw [fairCoin_support] at hr
      rcases hr with rfl | rfl <;> rfl
  | left =>
      have ht : t = next .left (j ()) := by
        simpa [execution] using hr
      subst t
      cases hc : j () with
      | none => simp [next, sourceOf]
      | some action => cases action <;> simp [next, sourceOf]
  | second =>
      have ht : t = next .second (j ()) := by
        simpa [execution] using hr
      subst t
      cases hc : j () with
      | none => simp [next, sourceOf]
      | some action => cases action <;> simp [next, sourceOf]
  | right | exited | lnone | lpunish | lreward | punished | rewarded |
      snone | sexit | scontinue => exact False.elim (hj.1 True.intro)

theorem next_left_injective : Function.Injective (next .left) := by
  intro first second heq
  cases first with
  | none =>
      cases second with
      | none => rfl
      | some second => cases second <;> simp [next] at heq
  | some first =>
      cases second with
      | none => cases first <;> simp [next] at heq
      | some second =>
          cases first <;> cases second <;> simp [next] at heq ⊢

theorem next_second_injective : Function.Injective (next .second) := by
  intro first second heq
  cases first with
  | none =>
      cases second with
      | none => rfl
      | some second => cases second <;> simp [next] at heq
  | some first =>
      cases second with
      | none => cases first <;> simp [next] at heq
      | some second =>
          cases first <;> cases second <;> simp [next] at heq ⊢

theorem predecessor_unique {t s₁ s₂ : State} {j₁ j₂ : Unit → Option Action}
    (h₁ : execution.Legal s₁ j₁) (h₂ : execution.Legal s₂ j₂)
    (r₁ : t ∈ (execution.step s₁ ⟨j₁, h₁⟩).support)
    (r₂ : t ∈ (execution.step s₂ ⟨j₂, h₂⟩).support) : s₁ = s₂ ∧ j₁ = j₂ := by
  have hs : s₁ = s₂ := Option.some.inj
    ((sourceOf_mem_step h₁ r₁).symm.trans (sourceOf_mem_step h₂ r₂))
  subst s₂
  refine ⟨rfl, ?_⟩
  cases s₁ with
  | chance =>
      have firstNoop := execution.eq_noop_of_legal_of_inactive h₁ (by simp)
      have secondNoop := execution.eq_noop_of_legal_of_inactive h₂ (by simp)
      exact firstNoop.trans secondNoop.symm
  | left =>
      have hr₁ : t = next .left (j₁ ()) := by
        simpa [execution] using r₁
      have hr₂ : t = next .left (j₂ ()) := by
        simpa [execution] using r₂
      have hjoint := next_left_injective (hr₁.symm.trans hr₂)
      funext who
      cases who
      exact hjoint
  | second =>
      have hr₁ : t = next .second (j₁ ()) := by
        simpa [execution] using r₁
      have hr₂ : t = next .second (j₂ ()) := by
        simpa [execution] using r₂
      have hjoint := next_second_injective (hr₁.symm.trans hr₂)
      funext who
      cases who
      exact hjoint
  | right | exited | lnone | lpunish | lreward | punished | rewarded |
      snone | sexit | scontinue => exact False.elim (h₁.1 True.intro)

theorem treeShaped : execution.IsTreeShaped :=
  execution.isTreeShaped_of_predecessor_unique init_not_mem_step predecessor_unique

theorem singleMover (s : State) {a b : Unit} (_ : execution.active s a)
    (_ : execution.active s b) : a = b := by cases a; cases b; rfl

@[reducible] def signals : InfoSignals execution where
  PublicSignal := State
  PrivateSignal _ := Unit
  initialPublic := .chance
  initialPrivate _ := ()
  publicSignal e := e.target
  privateSignal _ _ := ()
  InfoState _ := State
  initInfo _ _ x := x
  pushInfo _ _ _ _ x := x

theorem infoOf_state : ∀ {s : State} (tr : execution.Trace s), signals.infoOf () tr = s
  | _, .start => rfl
  | _, .extend _ _ _ _ => rfl

def menu : State → Set (Option Action)
  | .left => {some .exit, some .continue}
  | .second => {some .punish, some .reward}
  | _ => {none}

@[reducible] def information : InformationModel execution where
  toInfoSignals := signals
  menu _ := menu
  menu_adequate := by
    intro _ s tr c
    rw [infoOf_state]
    cases s <;> cases c <;> simp [menu, LegalOption]

@[reducible] def game : Languages.EFG.Game Unit where
  execution := execution
  information := information
  treeShaped := treeShaped
  singleMover := singleMover

instance (i : information.InfoState ()) : Finite (information.Choice () i) := by
  dsimp [InformationModel.Choice]; infer_instance

instance (i : information.InfoState ()) : Nonempty (information.Choice () i) := by
  cases i with
  | left => exact ⟨⟨some .exit, by simp [menu]⟩⟩
  | second => exact ⟨⟨some .punish, by simp [menu]⟩⟩
  | chance | right | exited | lnone | lpunish | lreward | punished | rewarded |
      snone | sexit | scontinue => exact ⟨⟨none, by simp [menu]⟩⟩

/-- A total plan is required because contingent plans are total, even though
backward maximization only inspects genuine decision histories. -/
def fallbackProfile : Profile game.strategicSignature :=
  fun _ _ => Classical.choice inferInstance

theorem finiteDecisionChoices : information.HasFiniteDecisionChoices := by
  intro _ info _ _
  exact inferInstance

def rank : State → ℕ
  | .chance => 3 | .left => 2 | .second => 1 | _ => 0

theorem rank_decreases (s t : State) (h : execution.Successor t s) : rank t < rank s := by
  rcases h with ⟨j, hj, hr⟩
  cases s with
  | chance =>
      rw [fairCoin_support] at hr
      rcases hr with rfl | rfl <;> decide
  | left =>
      have ht : t = next .left (j ()) := by
        simpa [execution] using hr
      subst t
      cases hc : j () with
      | none => simp [next, rank]
      | some action => cases action <;> simp [next, rank]
  | second =>
      have ht : t = next .second (j ()) := by
        simpa [execution] using hr
      subst t
      cases hc : j () with
      | none => simp [next, rank]
      | some action => cases action <;> simp [next, rank]
  | right | exited | lnone | lpunish | lreward | punished | rewarded |
      snone | sexit | scontinue => exact False.elim (hj.1 True.intro)

theorem wellFoundedPlay : execution.WellFoundedPlay :=
  wellFoundedPlay_of_rank rank rank_decreases

theorem perfect : game.HasPerfectInformation := by
  intro who first second _ _ _ _ hi
  cases who
  have hs : first.state = second.state := by simpa [infoOf_state] using hi
  cases first with
  | mk s tr =>
    cases second with
    | mk t tr' =>
      dsimp at hs
      subst t
      exact congrArg (fun trace => ExecutionProtocol.History.mk s trace)
        ((treeShaped s).elim tr tr')

/-- Nonconstant terminal utility makes exit optimal at the first decision and
reward strictly better than punishment at the resulting off-path decision. -/
def utility (h : game.History) (_ : Unit) : ℝ := match h.state with
  | .exited => 5 | .rewarded => 1 | _ => 0

theorem finiteStepSupport : ∀ (history : execution.History)
    (_hterm : ¬ execution.terminal history.state)
    (chosen : {joint : Unit → Option Action //
      execution.Legal history.state joint}),
    (execution.step history.state chosen).support.Finite := by
  intro history hterm chosen
  exact Set.toFinite _

theorem backwardIntegrable (chooser : execution.HistoryChooser)
    (history : execution.History) (who : Unit) :
    PayoffIntegrable (execution.historyBackwardLaw wellFoundedPlay chooser history)
      (fun outcome => utility outcome who) :=
  execution.payoffIntegrable_historyBackwardLaw_of_finite_step_support
    (certificate := wellFoundedPlay) finiteStepSupport chooser
    (fun outcome => utility outcome who) history

theorem chance_inactive : ¬ execution.active .chance () := by simp

theorem chanceLegal : execution.Legal .chance execution.noop :=
  execution.noop_isLegal chance_not_terminal (fun _ => chance_inactive)

theorem left_mem_chance_step :
    State.left ∈
      (execution.step .chance ⟨execution.noop, chanceLegal⟩).support := by
  exact (fairCoin_support .left).mpr (Or.inl rfl)

@[reducible]
def leftTrace : execution.Trace .left :=
  .extend .start execution.noop chanceLegal left_mem_chance_step

@[reducible]
def leftHistory : execution.History := ⟨.left, leftTrace⟩

theorem left_not_terminal : ¬ execution.terminal leftHistory.state := by simp

theorem left_active : execution.active leftHistory.state () := by simp

def continueJoint : Unit → Option Action := fun _ => some .continue

theorem continueLegal : execution.Legal leftHistory.state continueJoint := by
  apply execution.legal_of_legalOption left_not_terminal
  intro who
  cases who
  exact ⟨left_active, by simp [execution]⟩

theorem second_mem_continue_step :
    State.second ∈
      (execution.step leftHistory.state ⟨continueJoint, continueLegal⟩).support := by
  simp [continueJoint, execution, next]

@[reducible]
def secondHistory : execution.History :=
  leftHistory.extend continueLegal second_mem_continue_step

@[simp]
theorem secondHistory_state : secondHistory.state = .second := rfl

@[simp]
theorem execution_step_second
    (joint : Unit → Option Action) (hlegal : execution.Legal .second joint) :
    execution.step .second ⟨joint, hlegal⟩ =
      PMF.pure (next .second (joint ())) := rfl

theorem second_not_terminal : ¬ execution.terminal secondHistory.state := by
  simp [secondHistory]

theorem second_active : execution.active secondHistory.state () := by
  simp [secondHistory]

def exitChoice : information.Choice () (information.infoOf () leftHistory.trace) :=
  ⟨some .exit, by rw [infoOf_state]; simp [menu]⟩

def continueChoice : information.Choice () (information.infoOf () leftHistory.trace) :=
  ⟨some .continue, by rw [infoOf_state]; simp [menu]⟩

def punishChoice : information.Choice () (information.infoOf () secondHistory.trace) :=
  ⟨some .punish, by rw [infoOf_state]; simp [menu, secondHistory]⟩

def rewardChoice : information.Choice () (information.infoOf () secondHistory.trace) :=
  ⟨some .reward, by rw [infoOf_state]; simp [menu, secondHistory]⟩

/-- The particular contingent plan constructed by the public existence
theorem's Bellman engine. -/
def bellmanProfile : Profile game.strategicSignature :=
  information.backwardProfile singleMover fallbackProfile finiteDecisionChoices
    wellFoundedPlay utility backwardIntegrable

private def recurseValue (later : execution.History)
    (_ : execution.HistorySuccessor later secondHistory) : execution.HistoryChooser :=
  information.backwardChooserBundle singleMover fallbackProfile finiteDecisionChoices
    wellFoundedPlay utility backwardIntegrable later

private theorem historyChoiceLaw_of_pure_step
    (history : execution.History) (hterm : ¬ execution.terminal history.state)
    (who : Unit) (hactive : execution.active history.state who)
    (choice : information.Choice who (information.infoOf who history.trace))
    (recurse : ∀ later : execution.History,
      execution.HistorySuccessor later history → execution.HistoryChooser)
    (target : State)
    (hstep : execution.step history.state
      (information.jointOfChoice singleMover history hterm who hactive choice) =
        PMF.pure target)
    (hunique : ∀ next ∈ (execution.step history.state
      (information.jointOfChoice singleMover history hterm who hactive choice)).support,
      next = target)
    (realized : target ∈ (execution.step history.state
      (information.jointOfChoice singleMover history hterm who hactive choice)).support) :
    execution.historyBackwardLaw wellFoundedPlay
      (information.historyChoiceChooser singleMover
        (information.historyChooser fallbackProfile) history hterm recurse
        who hactive choice) history =
      execution.historyBackwardLaw wellFoundedPlay
        (recurse
          (history.extend
            (information.jointOfChoice singleMover history hterm who hactive choice).2
            realized)
          ⟨(information.jointOfChoice singleMover history hterm who hactive choice).1,
            (information.jointOfChoice singleMover history hterm who hactive choice).2,
            realized⟩)
        (history.extend
          (information.jointOfChoice singleMover history hterm who hactive choice).2
          realized) := by
  let chosen := information.jointOfChoice singleMover history hterm who hactive choice
  have hstep' : execution.step history.state chosen = PMF.pure target := by
    simpa [chosen] using hstep
  have hchooser :
      information.historyChoiceChooser singleMover
        (information.historyChooser fallbackProfile) history hterm recurse
        who hactive choice =
      execution.graftHistoryChooser (information.historyChooser fallbackProfile)
        history chosen (fun target realized =>
          recurse (history.extend chosen.2 realized)
            ⟨chosen.1, chosen.2, realized⟩) := rfl
  calc
    execution.historyBackwardLaw wellFoundedPlay
        (information.historyChoiceChooser singleMover
          (information.historyChooser fallbackProfile) history hterm recurse
          who hactive choice) history =
      (execution.step history.state chosen).bindOnSupport
        (fun _target realized =>
          execution.historyBackwardLaw wellFoundedPlay
            (recurse (history.extend chosen.2 realized)
              ⟨chosen.1, chosen.2, realized⟩)
            (history.extend chosen.2 realized)) := by
      rw [hchooser]
      exact execution.historyBackwardLaw_graft wellFoundedPlay
        (information.historyChooser fallbackProfile) history hterm chosen
        (fun _target realized =>
          recurse (history.extend chosen.2 realized)
            ⟨chosen.1, chosen.2, realized⟩)
    _ = execution.historyBackwardLaw wellFoundedPlay
          (recurse (history.extend chosen.2 realized)
            ⟨chosen.1, chosen.2, realized⟩)
          (history.extend chosen.2 realized) := by
      have hfg : ∀ (next : State)
          (hnext : next ∈ (execution.step history.state chosen).support),
          execution.historyBackwardLaw wellFoundedPlay
              (recurse (history.extend chosen.2 hnext)
                ⟨chosen.1, chosen.2, hnext⟩)
              (history.extend chosen.2 hnext) =
            execution.historyBackwardLaw wellFoundedPlay
              (recurse (history.extend chosen.2 realized)
                ⟨chosen.1, chosen.2, realized⟩)
              (history.extend chosen.2 realized) := by
        intro next hnext
        have hnextTarget := hunique next (by simpa [chosen] using hnext)
        subst next
        rfl
      calc
        _ = (execution.step history.state chosen).bind
            (fun _ => execution.historyBackwardLaw wellFoundedPlay
              (recurse (history.extend chosen.2 realized)
                ⟨chosen.1, chosen.2, realized⟩)
              (history.extend chosen.2 realized)) :=
          GameTheory.Math.Probability.bindOnSupport_eq_bind_of_eq_on_support
            (μ := execution.step history.state chosen)
            (f := fun next hnext =>
              execution.historyBackwardLaw wellFoundedPlay
                (recurse (history.extend chosen.2 hnext)
                  ⟨chosen.1, chosen.2, hnext⟩)
                (history.extend chosen.2 hnext))
            (g := fun _ => execution.historyBackwardLaw wellFoundedPlay
              (recurse (history.extend chosen.2 realized)
                ⟨chosen.1, chosen.2, realized⟩)
              (history.extend chosen.2 realized)) hfg
        _ = _ := PMF.bind_const _ _

private theorem historyChoiceLaw_of_pure_terminal_step
    (history : execution.History) (hterm : ¬ execution.terminal history.state)
    (who : Unit) (hactive : execution.active history.state who)
    (choice : information.Choice who (information.infoOf who history.trace))
    (recurse : ∀ later : execution.History,
      execution.HistorySuccessor later history → execution.HistoryChooser)
    (target : State)
    (hstep : execution.step history.state
      (information.jointOfChoice singleMover history hterm who hactive choice) =
        PMF.pure target)
    (hunique : ∀ next ∈ (execution.step history.state
      (information.jointOfChoice singleMover history hterm who hactive choice)).support,
      next = target)
    (realized : target ∈ (execution.step history.state
      (information.jointOfChoice singleMover history hterm who hactive choice)).support)
    (htarget : execution.terminal target) :
    execution.historyBackwardLaw wellFoundedPlay
      (information.historyChoiceChooser singleMover
        (information.historyChooser fallbackProfile) history hterm recurse
        who hactive choice) history =
      PMF.pure (history.extend
        (information.jointOfChoice singleMover history hterm who hactive choice).2
        realized) := by
  calc
    _ = execution.historyBackwardLaw wellFoundedPlay
          (recurse (history.extend
            (information.jointOfChoice singleMover history hterm who hactive choice).2
            realized)
            ⟨(information.jointOfChoice singleMover history hterm who hactive choice).1,
              (information.jointOfChoice singleMover history hterm who hactive choice).2,
              realized⟩)
          (history.extend
            (information.jointOfChoice singleMover history hterm who hactive choice).2
            realized) :=
      historyChoiceLaw_of_pure_step history hterm who hactive choice recurse target
        hstep hunique realized
    _ = _ := execution.historyBackwardLaw_of_terminal (by
      simpa [ExecutionProtocol.History.extend] using htarget)

private theorem backwardOutcome_terminal_apply (history : execution.History)
    (hterm : execution.terminal history.state) :
    information.backwardOutcome singleMover fallbackProfile finiteDecisionChoices
      wellFoundedPlay utility backwardIntegrable history () =
      utility history () := by
  exact information.backwardOutcome_of_terminal singleMover fallbackProfile
    finiteDecisionChoices backwardIntegrable hterm ()

theorem rewardChoice_value :
    information.historyChoiceValue singleMover
      (information.historyChooser fallbackProfile) wellFoundedPlay utility
      backwardIntegrable secondHistory second_not_terminal
      recurseValue () second_active rewardChoice = 1 := by
  have hstep : execution.step secondHistory.state
      (information.jointOfChoice singleMover secondHistory second_not_terminal
        () second_active rewardChoice) = PMF.pure .rewarded := by
    let chosen := information.jointOfChoice singleMover secondHistory
      second_not_terminal () second_active rewardChoice
    have haction : chosen.1 () = some Action.reward := by
      simp [chosen, InformationModel.jointOfChoice, rewardChoice]
    show PMF.pure (next .second
      (chosen.1 ())) = PMF.pure State.rewarded
    rw [haction]
    rfl
  have hrealized : State.rewarded ∈
      (execution.step secondHistory.state
        (information.jointOfChoice singleMover secondHistory second_not_terminal
          () second_active rewardChoice)).support := by
    rw [hstep]
    exact (PMF.mem_support_pure_iff State.rewarded State.rewarded).mpr rfl
  have hunique : ∀ next ∈ (execution.step secondHistory.state
      (information.jointOfChoice singleMover secondHistory second_not_terminal
        () second_active rewardChoice)).support,
      next = State.rewarded := by
    intro next hnext
    rw [hstep] at hnext
    exact (PMF.mem_support_pure_iff State.rewarded next).mp hnext
  have hlaw := historyChoiceLaw_of_pure_terminal_step
    secondHistory second_not_terminal () second_active rewardChoice recurseValue
    .rewarded hstep hunique hrealized (by simp)
  dsimp only [InformationModel.historyChoiceValue]
  simp only [hlaw, expect_pure]
  simp [utility, secondHistory, ExecutionProtocol.History.extend]

theorem punishChoice_value :
    information.historyChoiceValue singleMover
      (information.historyChooser fallbackProfile) wellFoundedPlay utility
      backwardIntegrable secondHistory second_not_terminal
      recurseValue () second_active punishChoice = 0 := by
  have hstep : execution.step secondHistory.state
      (information.jointOfChoice singleMover secondHistory second_not_terminal
        () second_active punishChoice) = PMF.pure .punished := by
    let chosen := information.jointOfChoice singleMover secondHistory
      second_not_terminal () second_active punishChoice
    have haction : chosen.1 () = some Action.punish := by
      simp [chosen, InformationModel.jointOfChoice, punishChoice]
    show PMF.pure (next .second
      (chosen.1 ())) = PMF.pure State.punished
    rw [haction]
    rfl
  have hrealized : State.punished ∈
      (execution.step secondHistory.state
        (information.jointOfChoice singleMover secondHistory second_not_terminal
          () second_active punishChoice)).support := by
    rw [hstep]
    exact (PMF.mem_support_pure_iff State.punished State.punished).mpr rfl
  have hunique : ∀ next ∈ (execution.step secondHistory.state
      (information.jointOfChoice singleMover secondHistory second_not_terminal
        () second_active punishChoice)).support,
      next = State.punished := by
    intro next hnext
    rw [hstep] at hnext
    exact (PMF.mem_support_pure_iff State.punished next).mp hnext
  have hlaw := historyChoiceLaw_of_pure_terminal_step
    secondHistory second_not_terminal () second_active punishChoice recurseValue
    .punished hstep hunique hrealized (by simp)
  dsimp only [InformationModel.historyChoiceValue]
  simp only [hlaw, expect_pure]
  simp [utility, secondHistory, ExecutionProtocol.History.extend]

private def secondBestChoice :
    information.Choice () (information.infoOf () secondHistory.trace) :=
  information.bestHistoryChoice singleMover
    (information.historyChooser fallbackProfile) wellFoundedPlay utility
    backwardIntegrable secondHistory second_not_terminal
    recurseValue () second_active

private theorem rewardChoice_step :
    execution.step secondHistory.state
      (information.jointOfChoice singleMover secondHistory second_not_terminal
        () second_active rewardChoice) = PMF.pure State.rewarded := by
  let chosen := information.jointOfChoice singleMover secondHistory
    second_not_terminal () second_active rewardChoice
  have haction : chosen.1 () = some Action.reward := by
    simp [chosen, InformationModel.jointOfChoice, rewardChoice]
  show PMF.pure (next .second (chosen.1 ())) = PMF.pure State.rewarded
  rw [haction]
  rfl

private theorem rewardChoice_step_mem : State.rewarded ∈
    (execution.step secondHistory.state
      (information.jointOfChoice singleMover secondHistory second_not_terminal
        () second_active rewardChoice)).support := by
  rw [rewardChoice_step]
  exact (PMF.mem_support_pure_iff State.rewarded State.rewarded).mpr rfl

private def rewardedHistory : execution.History :=
  secondHistory.extend
    (information.jointOfChoice singleMover secondHistory second_not_terminal
      () second_active rewardChoice).2
    rewardChoice_step_mem

theorem secondBestChoice_eq_rewardChoice : secondBestChoice = rewardChoice := by
  have hchoices :
      secondBestChoice.1 = some .punish ∨
        secondBestChoice.1 = some .reward := by
    have hmenu := secondBestChoice.2
    have hmenu' :
        secondBestChoice.1 ∈
          menu (information.infoOf () secondHistory.trace) := hmenu
    have hmenuEq :
        menu (information.infoOf () secondHistory.trace) =
          {some Action.punish, some Action.reward} := by
      rw [infoOf_state]
      rfl
    have hconcrete :
        secondBestChoice.1 ∈
          ({some Action.punish, some Action.reward} : Set (Option Action)) := by
      rw [← hmenuEq]
      exact hmenu'
    exact (Set.mem_insert_iff.mp hconcrete).imp id Set.mem_singleton_iff.mp
  rcases hchoices with hpunish | hreward
  · have hbest : secondBestChoice = punishChoice := Subtype.ext hpunish
    have hmax := information.historyChoiceValue_le_bestHistoryChoice
      singleMover (information.historyChooser fallbackProfile)
      wellFoundedPlay utility backwardIntegrable secondHistory second_not_terminal
      recurseValue () second_active
      rewardChoice
    have hmax' :
        information.historyChoiceValue singleMover
          (information.historyChooser fallbackProfile) wellFoundedPlay utility
          backwardIntegrable secondHistory second_not_terminal
          recurseValue () second_active rewardChoice ≤
        information.historyChoiceValue singleMover
          (information.historyChooser fallbackProfile) wellFoundedPlay utility
          backwardIntegrable secondHistory second_not_terminal
          recurseValue () second_active secondBestChoice := hmax
    rw [rewardChoice_value, hbest, punishChoice_value] at hmax'
    norm_num at hmax'
  · exact Subtype.ext hreward

private theorem backwardBundleLaw_second :
    execution.historyBackwardLaw wellFoundedPlay
      (information.backwardChooserBundle singleMover fallbackProfile
        finiteDecisionChoices wellFoundedPlay utility backwardIntegrable
        secondHistory)
      secondHistory = PMF.pure rewardedHistory := by
  let recurse : ∀ later : execution.History,
      execution.HistorySuccessor later secondHistory → execution.HistoryChooser :=
    fun later _ => information.backwardChooserBundle singleMover fallbackProfile
      finiteDecisionChoices wellFoundedPlay utility backwardIntegrable later
  have hjoint := information.backwardJoint_of_active singleMover fallbackProfile
    finiteDecisionChoices wellFoundedPlay utility backwardIntegrable secondHistory
    second_not_terminal recurse () second_active
  have hchooser :
      information.backwardChooserBundle singleMover fallbackProfile
        finiteDecisionChoices wellFoundedPlay utility backwardIntegrable
        secondHistory =
      information.historyChoiceChooser singleMover
        (information.historyChooser fallbackProfile) secondHistory
        second_not_terminal recurse () second_active secondBestChoice := by
    rw [information.backwardChooserBundle_of_not_terminal singleMover
      fallbackProfile finiteDecisionChoices backwardIntegrable second_not_terminal]
    dsimp only
    rw [hjoint]
    rfl
  have hstep : execution.step secondHistory.state
      (information.jointOfChoice singleMover secondHistory second_not_terminal
        () second_active secondBestChoice) = PMF.pure .rewarded := by
    rw [secondBestChoice_eq_rewardChoice]
    simp [InformationModel.jointOfChoice, rewardChoice, next, secondHistory]
  have hunique : ∀ next ∈ (execution.step secondHistory.state
      (information.jointOfChoice singleMover secondHistory second_not_terminal
        () second_active secondBestChoice)).support,
      next = State.rewarded := by
    intro next hnext
    rw [hstep] at hnext
    exact (PMF.mem_support_pure_iff State.rewarded next).mp hnext
  have hrealized : State.rewarded ∈
      (execution.step secondHistory.state
        (information.jointOfChoice singleMover secondHistory second_not_terminal
      () second_active secondBestChoice)).support := by
    rw [hstep]
    exact (PMF.mem_support_pure_iff State.rewarded State.rewarded).mpr rfl
  have hlaw := historyChoiceLaw_of_pure_terminal_step secondHistory
    second_not_terminal () second_active secondBestChoice recurse .rewarded
    hstep hunique hrealized (by simp)
  rw [hchooser]
  simpa only [InformationModel.historyChoiceChooser, secondBestChoice_eq_rewardChoice,
    rewardedHistory] using hlaw

theorem backwardChooser_second_action :
    (information.backwardChooser singleMover fallbackProfile finiteDecisionChoices
      wellFoundedPlay utility backwardIntegrable
      secondHistory second_not_terminal).1 () = some .reward := by
  have hjoint := information.backwardJoint_of_active singleMover fallbackProfile
    finiteDecisionChoices wellFoundedPlay utility backwardIntegrable secondHistory
    second_not_terminal
    (fun later _ => information.backwardChooserBundle singleMover fallbackProfile
      finiteDecisionChoices wellFoundedPlay utility backwardIntegrable later)
    () second_active
  have hbest :
      information.bestHistoryChoice singleMover
        (information.historyChooser fallbackProfile) wellFoundedPlay utility
        backwardIntegrable secondHistory second_not_terminal
        (fun later _ => information.backwardChooserBundle singleMover fallbackProfile
          finiteDecisionChoices wellFoundedPlay utility backwardIntegrable later)
        () second_active = secondBestChoice := rfl
  rw [information.backwardChooser_eq_joint singleMover fallbackProfile
    finiteDecisionChoices backwardIntegrable secondHistory second_not_terminal]
  rw [hjoint, hbest, secondBestChoice_eq_rewardChoice]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Backward induction prescribes reward at the consequential off-path
decision, rather than merely returning an opaque equilibrium witness. -/
theorem bellmanProfile_chooses_reward :
    (bellmanProfile ()).act .second = some .reward := by
  show
    (information.backwardPolicy singleMover fallbackProfile finiteDecisionChoices
      wellFoundedPlay utility backwardIntegrable ()).act
      .second = some .reward
  calc
    _ = (information.backwardPolicy singleMover fallbackProfile
        finiteDecisionChoices wellFoundedPlay utility backwardIntegrable ()).act
        (information.infoOf () secondHistory.trace) := by
          simp [infoOf_state, secondHistory]
    _ = (information.backwardChooser singleMover fallbackProfile
        finiteDecisionChoices wellFoundedPlay utility backwardIntegrable
        secondHistory second_not_terminal).1 () :=
          information.backwardPolicy_act_at_decision singleMover fallbackProfile
            finiteDecisionChoices backwardIntegrable perfect secondHistory
            second_not_terminal ()
              second_active
    _ = some .reward := backwardChooser_second_action

private theorem histories_eq_of_state_eq
    (first second : execution.History) (hstate : first.state = second.state) :
    first = second := by
  cases first with
  | mk state trace =>
    cases second with
    | mk otherState otherTrace =>
      dsimp at hstate
      subst otherState
      exact congrArg (fun current => ExecutionProtocol.History.mk state current)
        ((treeShaped state).elim trace otherTrace)

theorem history_eq_secondHistory_of_state (history : execution.History)
    (hstate : history.state = .second) : history = secondHistory :=
  histories_eq_of_state_eq history secondHistory
    (hstate.trans secondHistory_state.symm)

theorem backwardOutcome_second :
    information.backwardOutcome singleMover fallbackProfile finiteDecisionChoices
      wellFoundedPlay utility backwardIntegrable
      secondHistory () = 1 := by
  dsimp only [InformationModel.backwardOutcome]
  calc
    expect (execution.historyBackwardLaw wellFoundedPlay
        (information.backwardChooserBundle singleMover fallbackProfile
          finiteDecisionChoices wellFoundedPlay utility backwardIntegrable
          secondHistory) secondHistory)
        (fun outcome => utility outcome ()) _ =
      expect (PMF.pure rewardedHistory) (fun outcome => utility outcome ())
        (payoffIntegrable_pure _ _) :=
      expect_congr_law backwardBundleLaw_second _ _ _
    _ = utility rewardedHistory () := expect_pure _ _ _
    _ = 1 := by
      simp [utility, rewardedHistory, ExecutionProtocol.History.extend]

private theorem backwardOutcome_eq_one_of_state_second
    (history : execution.History) (hstate : history.state = .second) :
    information.backwardOutcome singleMover fallbackProfile finiteDecisionChoices
      wellFoundedPlay utility backwardIntegrable history () = 1 := by
  rw [history_eq_secondHistory_of_state history hstate]
  exact backwardOutcome_second

private def leftRecurseValue (later : execution.History)
    (_ : execution.HistorySuccessor later leftHistory) : execution.HistoryChooser :=
  information.backwardChooserBundle singleMover fallbackProfile finiteDecisionChoices
    wellFoundedPlay utility backwardIntegrable later

theorem exitChoice_value :
    information.historyChoiceValue singleMover
      (information.historyChooser fallbackProfile) wellFoundedPlay utility
      backwardIntegrable leftHistory left_not_terminal
      leftRecurseValue () left_active exitChoice = 5 := by
  let chosen := information.jointOfChoice singleMover leftHistory
    left_not_terminal () left_active exitChoice
  have hstep : execution.step leftHistory.state chosen = PMF.pure .exited := by
    have haction : chosen.1 () = some Action.exit := by
      simp [chosen, InformationModel.jointOfChoice, exitChoice]
    show PMF.pure (next .left (chosen.1 ())) = PMF.pure State.exited
    rw [haction]
    rfl
  have hunique : ∀ next ∈ (execution.step leftHistory.state chosen).support,
      next = State.exited := by
    intro next hnext
    rw [hstep] at hnext
    exact (PMF.mem_support_pure_iff State.exited next).mp hnext
  have hrealized : State.exited ∈
      (execution.step leftHistory.state chosen).support := by
    rw [hstep]
    exact (PMF.mem_support_pure_iff State.exited State.exited).mpr rfl
  have hlaw := historyChoiceLaw_of_pure_terminal_step leftHistory
    left_not_terminal () left_active exitChoice leftRecurseValue .exited
    hstep hunique hrealized (by simp)
  dsimp only [InformationModel.historyChoiceValue]
  calc
    expect (execution.historyBackwardLaw wellFoundedPlay
        (information.historyChoiceChooser singleMover
          (information.historyChooser fallbackProfile) leftHistory
          left_not_terminal leftRecurseValue () left_active exitChoice)
        leftHistory) (fun outcome => utility outcome ()) _ =
      expect (PMF.pure (leftHistory.extend chosen.2 hrealized))
        (fun outcome => utility outcome ()) (payoffIntegrable_pure _ _) :=
      expect_congr_law hlaw _ _ _
    _ = utility (leftHistory.extend chosen.2 hrealized) () := expect_pure _ _ _
    _ = 5 := by simp [utility, ExecutionProtocol.History.extend]

theorem continueChoice_value :
    information.historyChoiceValue singleMover
      (information.historyChooser fallbackProfile) wellFoundedPlay utility
      backwardIntegrable leftHistory left_not_terminal
      leftRecurseValue () left_active continueChoice = 1 := by
  let chosen := information.jointOfChoice singleMover leftHistory
    left_not_terminal () left_active continueChoice
  have hstep : execution.step leftHistory.state chosen = PMF.pure .second := by
    have haction : chosen.1 () = some Action.continue := by
      simp [chosen, InformationModel.jointOfChoice, continueChoice]
    show PMF.pure (next .left (chosen.1 ())) = PMF.pure State.second
    rw [haction]
    rfl
  have hunique : ∀ next ∈ (execution.step leftHistory.state chosen).support,
      next = State.second := by
    intro next hnext
    rw [hstep] at hnext
    exact (PMF.mem_support_pure_iff State.second next).mp hnext
  have hrealized : State.second ∈
      (execution.step leftHistory.state chosen).support := by
    rw [hstep]
    exact (PMF.mem_support_pure_iff State.second State.second).mpr rfl
  have hchild : leftHistory.extend chosen.2 hrealized = secondHistory :=
    history_eq_secondHistory_of_state _ rfl
  have hlaw := historyChoiceLaw_of_pure_step leftHistory left_not_terminal
    () left_active continueChoice leftRecurseValue .second hstep hunique hrealized
  have hlaw' : execution.historyBackwardLaw wellFoundedPlay
      (information.historyChoiceChooser singleMover
        (information.historyChooser fallbackProfile) leftHistory left_not_terminal
        leftRecurseValue () left_active continueChoice) leftHistory =
      PMF.pure rewardedHistory := by
    calc
      _ = execution.historyBackwardLaw wellFoundedPlay
            (information.backwardChooserBundle singleMover fallbackProfile
              finiteDecisionChoices wellFoundedPlay utility backwardIntegrable
              secondHistory) secondHistory := by
        simpa only [leftRecurseValue, hchild] using hlaw
      _ = PMF.pure rewardedHistory := backwardBundleLaw_second
  dsimp only [InformationModel.historyChoiceValue]
  calc
    expect (execution.historyBackwardLaw wellFoundedPlay
        (information.historyChoiceChooser singleMover
          (information.historyChooser fallbackProfile) leftHistory
          left_not_terminal leftRecurseValue () left_active continueChoice)
        leftHistory) (fun outcome => utility outcome ()) _ =
      expect (PMF.pure rewardedHistory) (fun outcome => utility outcome ())
        (payoffIntegrable_pure _ _) :=
      expect_congr_law hlaw' _ _ _
    _ = utility rewardedHistory () := expect_pure _ _ _
    _ = 1 := by simp [utility, rewardedHistory, ExecutionProtocol.History.extend]

private def leftBestChoice :
    information.Choice () (information.infoOf () leftHistory.trace) :=
  information.bestHistoryChoice singleMover
    (information.historyChooser fallbackProfile) wellFoundedPlay utility
    backwardIntegrable leftHistory left_not_terminal
    leftRecurseValue () left_active

theorem leftBestChoice_eq_exitChoice : leftBestChoice = exitChoice := by
  have hchoices :
      leftBestChoice.1 = some .exit ∨
        leftBestChoice.1 = some .continue := by
    have hmenu := leftBestChoice.2
    have hmenu' :
        leftBestChoice.1 ∈
          menu (information.infoOf () leftHistory.trace) := hmenu
    have hmenuEq :
        menu (information.infoOf () leftHistory.trace) =
          {some Action.exit, some Action.continue} := by
      rw [infoOf_state]
      rfl
    have hconcrete :
        leftBestChoice.1 ∈
          ({some Action.exit, some Action.continue} : Set (Option Action)) := by
      rw [← hmenuEq]
      exact hmenu'
    exact (Set.mem_insert_iff.mp hconcrete).imp id Set.mem_singleton_iff.mp
  rcases hchoices with hexit | hcontinue
  · exact Subtype.ext hexit
  · have hbest : leftBestChoice = continueChoice := Subtype.ext hcontinue
    have hmax := information.historyChoiceValue_le_bestHistoryChoice
      singleMover (information.historyChooser fallbackProfile)
      wellFoundedPlay utility backwardIntegrable leftHistory left_not_terminal
      leftRecurseValue () left_active
      exitChoice
    have hmax' :
        information.historyChoiceValue singleMover
          (information.historyChooser fallbackProfile) wellFoundedPlay utility
          backwardIntegrable leftHistory left_not_terminal
          leftRecurseValue () left_active exitChoice ≤
        information.historyChoiceValue singleMover
          (information.historyChooser fallbackProfile) wellFoundedPlay utility
          backwardIntegrable leftHistory left_not_terminal
          leftRecurseValue () left_active leftBestChoice := hmax
    rw [exitChoice_value, hbest, continueChoice_value] at hmax'
    norm_num at hmax'

theorem backwardChooser_left_action :
    (information.backwardChooser singleMover fallbackProfile finiteDecisionChoices
      wellFoundedPlay utility backwardIntegrable
      leftHistory left_not_terminal).1 () = some .exit := by
  have hjoint := information.backwardJoint_of_active singleMover fallbackProfile
    finiteDecisionChoices wellFoundedPlay utility backwardIntegrable leftHistory
    left_not_terminal
    (fun later _ => information.backwardChooserBundle singleMover fallbackProfile
      finiteDecisionChoices wellFoundedPlay utility backwardIntegrable later)
    () left_active
  have hbest :
      information.bestHistoryChoice singleMover
        (information.historyChooser fallbackProfile) wellFoundedPlay utility
        backwardIntegrable leftHistory left_not_terminal
        (fun later _ => information.backwardChooserBundle singleMover fallbackProfile
          finiteDecisionChoices wellFoundedPlay utility backwardIntegrable later)
        () left_active = leftBestChoice := rfl
  rw [information.backwardChooser_eq_joint singleMover fallbackProfile
    finiteDecisionChoices backwardIntegrable leftHistory left_not_terminal]
  rw [hjoint, hbest]
  rw [leftBestChoice_eq_exitChoice]
  rfl

/-- At the first decision, backward induction takes the strict payoff-five
exit instead of continuing to the payoff-one subgame. -/
theorem bellmanProfile_chooses_exit :
    (bellmanProfile ()).act .left = some .exit := by
  show
    (information.backwardPolicy singleMover fallbackProfile finiteDecisionChoices
      wellFoundedPlay utility backwardIntegrable ()).act
      .left = some .exit
  calc
    _ = (information.backwardPolicy singleMover fallbackProfile
        finiteDecisionChoices wellFoundedPlay utility backwardIntegrable ()).act
        (information.infoOf () leftHistory.trace) := by
          simp [leftHistory]
    _ = (information.backwardChooser singleMover fallbackProfile
        finiteDecisionChoices wellFoundedPlay utility backwardIntegrable
        leftHistory left_not_terminal).1 () :=
          information.backwardPolicy_act_at_decision singleMover fallbackProfile
            finiteDecisionChoices backwardIntegrable perfect leftHistory
            left_not_terminal ()
              left_active
    _ = some .exit := backwardChooser_left_action

/-- The total construction preserves the supplied plan at the chance
information state, where the player never makes a decision. -/
theorem backwardPolicy_chance_eq_fallback :
    information.backwardPolicy singleMover fallbackProfile
        finiteDecisionChoices wellFoundedPlay utility backwardIntegrable () .chance =
      fallbackProfile () .chance := by
  apply information.backwardPolicy_eq_fallback_of_no_decision_history
    singleMover fallbackProfile finiteDecisionChoices backwardIntegrable () .chance
  rintro ⟨history, _, hactive, hinfo⟩
  rw [infoOf_state] at hinfo
  simp [execution, hinfo] at hactive

/-- The public EFG surface constructs a pure SPE on the hostile witness. -/
theorem exists_subgamePerfect : ∃ p : Profile game.strategicSignature,
    game.IsSubgamePerfect wellFoundedPlay p utility :=
  game.exists_isSubgamePerfect fallbackProfile finiteDecisionChoices
    wellFoundedPlay perfect utility backwardIntegrable

end GameTheory.Tests.EFGZermelo
