/-
# Constructive backward induction for perfect information

`Backward` evaluates a fixed chooser and `SubgamePerfect` proves the one-shot
deviation principle.  This module supplies the missing construction: at each
nonterminal history, choose a finite maximizing action for the unique mover,
evaluate its continuation recursively, and assemble those history choices into
one information-local pure profile.

The construction uses the conventional strong perfect-information premise: an
information state at which a player moves identifies the complete history.
This replaces the predecessor's syntax-specific sibling-subtree disjointness
proofs; it does not introduce a second tree or evaluator. A weaker theorem
could exempt information states whose legal choice carrier is a subsingleton,
but that extra generality is not needed for perfect-information existence.
-/

import GameTheory.Protocol.SubgamePerfect

noncomputable section

namespace GameTheory.Protocol

open Probability

universe uι us ua up uq uk

variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}

namespace InformationModel

variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)

/-- Strong perfect-information separation in the accepted history
representation: if player `who` genuinely moves at two nonterminal histories
and sees the same information state, those histories are equal. -/
def SeparatesDecisionHistories : Prop :=
  ∀ (who : ι) (first second : E.History),
    ¬ E.terminal first.state → E.active first.state who →
    ¬ E.terminal second.state → E.active second.state who →
    M.infoOf who first.trace = M.infoOf who second.trace →
    first = second

/-- A complete history realizes `info` as a genuine decision point for `who`.
Terminal histories are excluded explicitly because activity is intentionally
unconstrained after a protocol has stopped. -/
def IsDecisionHistory (who : ι) (info : M.InfoState who)
    (history : E.History) : Prop :=
  ¬ E.terminal history.state ∧ E.active history.state who ∧
    M.infoOf who history.trace = info

/-- Turn one information-local choice by the unique mover into a legal joint
action.  Every other coordinate is inactive and therefore contributes `none`.
-/
def jointOfChoice [DecidableEq ι]
    (singleMover : ∀ (state : E.State) {first second : ι},
      E.active state first → E.active state second → first = second)
    (history : E.History) (hterm : ¬ E.terminal history.state)
    (who : ι) (hactive : E.active history.state who)
    (choice : M.Choice who (M.infoOf who history.trace)) :
    {joint : ∀ i, Option (E.Action i) // E.Legal history.state joint} := by
  let joint := E.singletonJoint who choice.1
  refine ⟨joint, ExecutionProtocol.legal_of_legalOption hterm fun i => ?_⟩
  by_cases hi : i = who
  · subst i
    simpa [joint] using
      (M.menu_adequate who history.trace choice.1).mp choice.2
  · have hinactive : ¬ E.active history.state i := fun hactive' =>
      hi (singleMover history.state hactive' hactive)
    simpa [joint, hi, LegalOption] using hinactive

/-- The mover's continuation value from one current choice, using already
computed values at every realized successor history. -/
def historyChoiceValue [DecidableEq ι]
    (singleMover : ∀ (state : E.State) {first second : ι},
      E.active state first → E.active state second → first = second)
    (history : E.History) (hterm : ¬ E.terminal history.state)
    (recurse : ∀ later : E.History,
      E.HistorySuccessor later history → ι → ℝ)
    (who : ι) (hactive : E.active history.state who)
    (choice : M.Choice who (M.infoOf who history.trace)) : ℝ :=
  let chosen := M.jointOfChoice singleMover history hterm who hactive choice
  E.historyStepValue history chosen fun _target realized =>
    recurse (history.extend chosen.2 realized)
      ⟨chosen.1, chosen.2, realized⟩ who

/-- A maximizing current choice. Finiteness and nonemptiness are capabilities
of this construction, not fields stored in the information model. -/
def bestHistoryChoice [DecidableEq ι]
    (singleMover : ∀ (state : E.State) {first second : ι},
      E.active state first → E.active state second → first = second)
    (history : E.History) (hterm : ¬ E.terminal history.state)
    (recurse : ∀ later : E.History,
      E.HistorySuccessor later history → ι → ℝ)
    (who : ι) (hactive : E.active history.state who)
    [Finite (M.Choice who (M.infoOf who history.trace))]
    [Nonempty (M.Choice who (M.infoOf who history.trace))] :
    M.Choice who (M.infoOf who history.trace) :=
  Classical.choose (Finite.exists_max
    (M.historyChoiceValue singleMover history hterm recurse who hactive))

/-- The selected current choice really maximizes the mover's recursively
computed continuation value. -/
theorem historyChoiceValue_le_bestHistoryChoice [DecidableEq ι]
    (singleMover : ∀ (state : E.State) {first second : ι},
      E.active state first → E.active state second → first = second)
    (history : E.History) (hterm : ¬ E.terminal history.state)
    (recurse : ∀ later : E.History,
      E.HistorySuccessor later history → ι → ℝ)
    (who : ι) (hactive : E.active history.state who)
    [Finite (M.Choice who (M.infoOf who history.trace))]
    [Nonempty (M.Choice who (M.infoOf who history.trace))]
    (choice : M.Choice who (M.infoOf who history.trace)) :
    M.historyChoiceValue singleMover history hterm recurse who hactive choice ≤
      M.historyChoiceValue singleMover history hterm recurse who hactive
        (M.bestHistoryChoice singleMover history hterm recurse who hactive) :=
  Classical.choose_spec (Finite.exists_max
    (M.historyChoiceValue singleMover history hterm recurse who hactive)) choice

/-- The Bellman joint action: maximize for the unique mover, or use the unique
no-op at a chance/administrative state. -/
def backwardJoint [DecidableEq ι]
    (singleMover : ∀ (state : E.State) {first second : ι},
      E.active state first → E.active state second → first = second)
    [∀ who info, Finite (M.Choice who info)]
    [∀ who info, Nonempty (M.Choice who info)]
    (history : E.History) (hterm : ¬ E.terminal history.state)
    (recurse : ∀ later : E.History,
      E.HistorySuccessor later history → ι → ℝ) :
    {joint : ∀ i, Option (E.Action i) // E.Legal history.state joint} := by
  classical
  exact if hactive : ∃ who, E.active history.state who then
      let who := Classical.choose hactive
      let whoActive := Classical.choose_spec hactive
      M.jointOfChoice singleMover history hterm who whoActive
        (M.bestHistoryChoice singleMover history hterm recurse who whoActive)
    else
      ⟨E.noop, E.noop_isLegal hterm fun who active => hactive ⟨who, active⟩⟩

private theorem jointOfBest_eq_of_player_eq [DecidableEq ι]
    (singleMover : ∀ (state : E.State) {first second : ι},
      E.active state first → E.active state second → first = second)
    [∀ player info, Finite (M.Choice player info)]
    [∀ player info, Nonempty (M.Choice player info)]
    (history : E.History) (hterm : ¬ E.terminal history.state)
    (recurse : ∀ later : E.History,
      E.HistorySuccessor later history → ι → ℝ)
    {first second : ι} (heq : first = second)
    (hfirst : E.active history.state first)
    (hsecond : E.active history.state second) :
    M.jointOfChoice singleMover history hterm first hfirst
        (M.bestHistoryChoice singleMover history hterm recurse first hfirst) =
      M.jointOfChoice singleMover history hterm second hsecond
        (M.bestHistoryChoice singleMover history hterm recurse second hsecond) := by
  subst second
  rfl

/-- At a decision history, the Bellman joint is precisely the joint generated
by a maximizing choice of the unique active player. -/
theorem backwardJoint_of_active [DecidableEq ι]
    (singleMover : ∀ (state : E.State) {first second : ι},
      E.active state first → E.active state second → first = second)
    [∀ player info, Finite (M.Choice player info)]
    [∀ player info, Nonempty (M.Choice player info)]
    (history : E.History) (hterm : ¬ E.terminal history.state)
    (recurse : ∀ later : E.History,
      E.HistorySuccessor later history → ι → ℝ)
    (who : ι) (hactive : E.active history.state who) :
    M.backwardJoint singleMover history hterm recurse =
      M.jointOfChoice singleMover history hterm who hactive
        (M.bestHistoryChoice singleMover history hterm recurse who hactive) := by
  classical
  let hexists : ∃ player, E.active history.state player := ⟨who, hactive⟩
  simp only [backwardJoint, dif_pos hexists]
  let selected := Classical.choose hexists
  have hselected := Classical.choose_spec hexists
  have heq : selected = who := singleMover history.state hselected hactive
  exact M.jointOfBest_eq_of_player_eq singleMover history hterm recurse
    heq hselected hactive

/-- Backward-induction continuation payoffs for every player. -/
def backwardOutcome [DecidableEq ι]
    (singleMover : ∀ (state : E.State) {first second : ι},
      E.active state first → E.active state second → first = second)
    [∀ who info, Finite (M.Choice who info)]
    [∀ who info, Nonempty (M.Choice who info)]
    (certificate : E.WellFoundedPlay)
    (utility : E.History → ι → ℝ) : E.History → ι → ℝ := by
  classical
  exact E.historyBackwardRec certificate fun history recurse =>
      if hterm : E.terminal history.state then utility history
      else
        let chosen := M.backwardJoint singleMover history hterm recurse
        fun who => E.historyStepValue history chosen fun _target realized =>
          recurse (history.extend chosen.2 realized)
            ⟨chosen.1, chosen.2, realized⟩ who

/-- The history chooser selected by the Bellman recursion. -/
def backwardChooser [DecidableEq ι]
    (singleMover : ∀ (state : E.State) {first second : ι},
      E.active state first → E.active state second → first = second)
    [∀ who info, Finite (M.Choice who info)]
    [∀ who info, Nonempty (M.Choice who info)]
    (certificate : E.WellFoundedPlay)
    (utility : E.History → ι → ℝ) : E.HistoryChooser :=
  fun history hterm =>
    M.backwardJoint singleMover history hterm fun later _ =>
      M.backwardOutcome singleMover certificate utility later

theorem backwardOutcome_of_terminal [DecidableEq ι]
    (singleMover : ∀ (state : E.State) {first second : ι},
      E.active state first → E.active state second → first = second)
    [∀ who info, Finite (M.Choice who info)]
    [∀ who info, Nonempty (M.Choice who info)]
    {certificate : E.WellFoundedPlay} {utility : E.History → ι → ℝ}
    {history : E.History} (hterm : E.terminal history.state) :
    M.backwardOutcome singleMover certificate utility history = utility history := by
  rw [backwardOutcome, E.historyBackwardRec_eq, dif_pos hterm]

theorem backwardOutcome_of_not_terminal [DecidableEq ι]
    (singleMover : ∀ (state : E.State) {first second : ι},
      E.active state first → E.active state second → first = second)
    [∀ who info, Finite (M.Choice who info)]
    [∀ who info, Nonempty (M.Choice who info)]
    {certificate : E.WellFoundedPlay} {utility : E.History → ι → ℝ}
    {history : E.History} (hterm : ¬ E.terminal history.state) :
    M.backwardOutcome singleMover certificate utility history =
      fun who =>
        let chosen := M.backwardChooser singleMover certificate utility history hterm
        E.historyStepValue history chosen fun _target realized =>
          M.backwardOutcome singleMover certificate utility
            (history.extend chosen.2 realized) who := by
  rw [backwardOutcome, E.historyBackwardRec_eq, dif_neg hterm]
  rfl

/-- The pure policy assembled from the Bellman chooser. At a realized decision
information state it reads the chooser at the unique corresponding history;
elsewhere it uses the caller-supplied nonempty menu. -/
def backwardPolicy [DecidableEq ι]
    (singleMover : ∀ (state : E.State) {first second : ι},
      E.active state first → E.active state second → first = second)
    [∀ who info, Finite (M.Choice who info)]
    [∀ who info, Nonempty (M.Choice who info)]
    (certificate : E.WellFoundedPlay)
    (utility : E.History → ι → ℝ) (who : ι) : M.Policy who :=
  fun info => by
    classical
    by_cases hreached : ∃ history, M.IsDecisionHistory who info history
    · let history := Classical.choose hreached
      have hh := Classical.choose_spec hreached
      have hterm : ¬ E.terminal history.state := hh.1
      have hinfo : M.infoOf who history.trace = info := hh.2.2
      let chosen := M.backwardChooser singleMover certificate utility history hterm
      refine ⟨chosen.1 who, ?_⟩
      rw [← hinfo]
      exact (M.menu_adequate who history.trace (chosen.1 who)).mpr
        (ExecutionProtocol.legalOption_of_legal chosen.2 who)
    · exact Classical.choice inferInstance

/-- The information-local profile assembled from backward induction. -/
def backwardProfile [DecidableEq ι]
    (singleMover : ∀ (state : E.State) {first second : ι},
      E.active state first → E.active state second → first = second)
    [∀ who info, Finite (M.Choice who info)]
    [∀ who info, Nonempty (M.Choice who info)]
    (certificate : E.WellFoundedPlay)
    (utility : E.History → ι → ℝ) : Profile M.strategicSignature :=
  fun who => M.backwardPolicy singleMover certificate utility who

private theorem backwardChooser_action_eq_of_history_eq [DecidableEq ι]
    (singleMover : ∀ (state : E.State) {first second : ι},
      E.active state first → E.active state second → first = second)
    [∀ who info, Finite (M.Choice who info)]
    [∀ who info, Nonempty (M.Choice who info)]
    {certificate : E.WellFoundedPlay}
    {utility : E.History → ι → ℝ}
    {first second : E.History} (heq : first = second)
    (hfirst : ¬ E.terminal first.state)
    (hsecond : ¬ E.terminal second.state) (who : ι) :
    (M.backwardChooser singleMover certificate utility first hfirst).1 who =
      (M.backwardChooser singleMover certificate utility second hsecond).1 who := by
  subst second
  rfl

/-- At a genuine decision history, the assembled policy reproduces the
Bellman chooser's coordinate. Perfect-information separation removes the
arbitrary representative chosen while assembling the total policy. -/
theorem backwardPolicy_act_at_decision [DecidableEq ι]
    (singleMover : ∀ (state : E.State) {first second : ι},
      E.active state first → E.active state second → first = second)
    [∀ who info, Finite (M.Choice who info)]
    [∀ who info, Nonempty (M.Choice who info)]
    {certificate : E.WellFoundedPlay}
    {utility : E.History → ι → ℝ}
    (hperfect : M.SeparatesDecisionHistories)
    (history : E.History) (hterm : ¬ E.terminal history.state)
    (who : ι) (hactive : E.active history.state who) :
    (M.backwardPolicy singleMover certificate utility who).act
        (M.infoOf who history.trace) =
      (M.backwardChooser singleMover certificate utility history hterm).1 who := by
  classical
  let hreached : ∃ prior,
      M.IsDecisionHistory who (M.infoOf who history.trace) prior :=
    ⟨history, hterm, hactive, rfl⟩
  simp only [backwardPolicy, dif_pos hreached, Policy.act]
  let prior := Classical.choose hreached
  have hprior := Classical.choose_spec hreached
  have heq : prior = history :=
    hperfect who prior history hprior.1 hprior.2.1 hterm hactive hprior.2.2
  exact M.backwardChooser_action_eq_of_history_eq singleMover heq
    hprior.1 hterm who

/-- The assembled information-local profile and the Bellman history chooser
select the same legal joint action after every nonterminal history, including
off-path histories. -/
theorem historyChooser_backwardProfile [DecidableEq ι]
    (singleMover : ∀ (state : E.State) {first second : ι},
      E.active state first → E.active state second → first = second)
    [∀ who info, Finite (M.Choice who info)]
    [∀ who info, Nonempty (M.Choice who info)]
    {certificate : E.WellFoundedPlay}
    {utility : E.History → ι → ℝ}
    (hperfect : M.SeparatesDecisionHistories)
    (history : E.History) (hterm : ¬ E.terminal history.state) :
    M.historyChooser
        (M.backwardProfile singleMover certificate utility) history hterm =
      M.backwardChooser singleMover certificate utility history hterm := by
  apply Subtype.ext
  funext who
  by_cases hactive : E.active history.state who
  · simpa [backwardProfile, InformationModel.historyChooser,
      InformationModel.jointAt] using
      M.backwardPolicy_act_at_decision singleMover hperfect
        history hterm who hactive
  · have hprofile := LegalOption.eq_none_of_inactive
      ((M.historyChooser
        (M.backwardProfile singleMover certificate utility) history hterm).1 who)
      (ExecutionProtocol.legalOption_of_legal
        (M.historyChooser
          (M.backwardProfile singleMover certificate utility) history hterm).2 who)
      hactive
    have hbackward := LegalOption.eq_none_of_inactive
      ((M.backwardChooser singleMover certificate utility history hterm).1 who)
      (ExecutionProtocol.legalOption_of_legal
        (M.backwardChooser singleMover certificate utility history hterm).2 who)
      hactive
    exact hprofile.trans hbackward.symm

/-- Evaluation of the assembled profile agrees with the Bellman values at
every history and for every player. -/
theorem historyBackwardValue_backwardProfile [DecidableEq ι]
    (singleMover : ∀ (state : E.State) {first second : ι},
      E.active state first → E.active state second → first = second)
    [∀ player info, Finite (M.Choice player info)]
    [∀ player info, Nonempty (M.Choice player info)]
    {certificate : E.WellFoundedPlay}
    {utility : E.History → ι → ℝ}
    (hperfect : M.SeparatesDecisionHistories) (who : ι) :
    ∀ history : E.History,
      E.historyBackwardValue certificate
          (M.historyChooser
            (M.backwardProfile singleMover certificate utility))
          (fun outcome => utility outcome who) history =
        M.backwardOutcome singleMover certificate utility history who := by
  intro history
  induction history using
      (E.wellFounded_historySuccessor certificate).induction with
  | _ history ih =>
      by_cases hterm : E.terminal history.state
      · rw [E.historyBackwardValue_of_terminal hterm,
          M.backwardOutcome_of_terminal singleMover hterm]
      · rw [E.historyBackwardValue_of_not_terminal hterm,
          M.backwardOutcome_of_not_terminal singleMover hterm,
          M.historyChooser_backwardProfile singleMover hperfect history hterm]
        apply ExecutionProtocol.historyStepValue_congr
        intro target realized
        exact ih (history.extend
            (M.backwardChooser singleMover certificate utility history hterm).2
            realized)
          ⟨(M.backwardChooser singleMover certificate utility history hterm).1,
            (M.backwardChooser singleMover certificate utility history hterm).2,
            realized⟩

/-- Replacing the assembled profile's current choice produces exactly the
legal joint built from that alternative. -/
theorem historyChooser_oneShot_backwardProfile [DecidableEq ι]
    [∀ player, DecidableEq (M.InfoState player)]
    (singleMover : ∀ (state : E.State) {first second : ι},
      E.active state first → E.active state second → first = second)
    [∀ player info, Finite (M.Choice player info)]
    [∀ player info, Nonempty (M.Choice player info)]
    {certificate : E.WellFoundedPlay}
    {utility : E.History → ι → ℝ}
    (history : E.History) (hterm : ¬ E.terminal history.state)
    (who : ι) (hactive : E.active history.state who)
    (choice : M.Choice who (M.infoOf who history.trace)) :
    M.historyChooser
        (M.oneShotProfile
          (M.backwardProfile singleMover certificate utility)
          history who choice) history hterm =
      M.jointOfChoice singleMover history hterm who hactive choice := by
  apply Subtype.ext
  funext other
  by_cases heq : other = who
  · subst other
    simp [InformationModel.historyChooser, InformationModel.jointAt,
      InformationModel.oneShotProfile, Policy.act, jointOfChoice]
  · have hinactive : ¬ E.active history.state other := fun hother =>
      heq (singleMover history.state hother hactive)
    have hchanged := LegalOption.eq_none_of_inactive
      ((M.historyChooser
        (M.oneShotProfile
          (M.backwardProfile singleMover certificate utility)
          history who choice) history hterm).1 other)
      (ExecutionProtocol.legalOption_of_legal
        (M.historyChooser
          (M.oneShotProfile
            (M.backwardProfile singleMover certificate utility)
            history who choice) history hterm).2 other)
      hinactive
    have halternative := LegalOption.eq_none_of_inactive
      ((M.jointOfChoice singleMover history hterm who hactive choice).1 other)
      (ExecutionProtocol.legalOption_of_legal
        (M.jointOfChoice singleMover history hterm who hactive choice).2 other)
      hinactive
    exact hchanged.trans halternative.symm

private theorem historyStepValue_history_congr_of_chosen_eq
    (history : E.History)
    {first second :
      {joint : ∀ player, Option (E.Action player) //
        E.Legal history.state joint}}
    (hchosen : first = second)
    (firstValue secondValue : E.History → ℝ)
    (hvalue : ∀ later, firstValue later = secondValue later) :
    E.historyStepValue history first (fun _target realized =>
        firstValue (history.extend first.2 realized)) =
      E.historyStepValue history second (fun _target realized =>
        secondValue (history.extend second.2 realized)) := by
  subst second
  apply ExecutionProtocol.historyStepValue_congr
  intro target realized
  exact hvalue _

/-- Constructive backward induction produces a pure profile with no profitable
one-shot deviation after any complete history. -/
theorem backwardProfile_hasNoProfitableOneShotDeviation [DecidableEq ι]
    [∀ player, DecidableEq (M.InfoState player)]
    (singleMover : ∀ (state : E.State) {first second : ι},
      E.active state first → E.active state second → first = second)
    [∀ player info, Finite (M.Choice player info)]
    [∀ player info, Nonempty (M.Choice player info)]
    {certificate : E.WellFoundedPlay}
    {utility : E.History → ι → ℝ}
    (hperfect : M.SeparatesDecisionHistories) :
    M.HasNoProfitableOneShotDeviation certificate
      (M.backwardProfile singleMover certificate utility) utility := by
  intro who history hterm choice
  by_cases hactive : E.active history.state who
  · let recurse : ∀ later : E.History,
        E.HistorySuccessor later history → ι → ℝ :=
      fun later _ => M.backwardOutcome singleMover certificate utility later
    calc
      M.oneShotHistoryValue certificate
          (M.backwardProfile singleMover certificate utility)
          (fun outcome => utility outcome who)
          who history hterm choice =
        M.historyChoiceValue singleMover history hterm recurse
          who hactive choice := by
            dsimp only [oneShotHistoryValue, historyChoiceValue]
            exact historyStepValue_history_congr_of_chosen_eq history
              (M.historyChooser_oneShot_backwardProfile
                singleMover history hterm who hactive choice)
              (fun later => E.historyBackwardValue certificate
                (M.historyChooser
                  (M.backwardProfile singleMover certificate utility))
                (fun outcome => utility outcome who) later)
              (fun later =>
                M.backwardOutcome singleMover certificate utility later who)
              (M.historyBackwardValue_backwardProfile
                singleMover hperfect who)
      _ ≤ M.historyChoiceValue singleMover history hterm recurse who hactive
          (M.bestHistoryChoice singleMover history hterm recurse who hactive) :=
        M.historyChoiceValue_le_bestHistoryChoice
          singleMover history hterm recurse who hactive choice
      _ = M.backwardOutcome singleMover certificate utility history who := by
        rw [M.backwardOutcome_of_not_terminal singleMover hterm]
        unfold backwardChooser
        rw [M.backwardJoint_of_active singleMover history hterm recurse who hactive]
        rfl
      _ = E.historyBackwardValue certificate
          (M.historyChooser
            (M.backwardProfile singleMover certificate utility))
          (fun outcome => utility outcome who) history :=
        (M.historyBackwardValue_backwardProfile
          singleMover hperfect who history).symm
  · have hchoice : choice =
        M.backwardProfile singleMover certificate utility who
          (M.infoOf who history.trace) :=
      (M.subsingleton_choice_of_not_active history.trace hactive).elim _ _
    subst choice
    let profile := M.backwardProfile singleMover certificate utility
    let chosen := M.historyChooser
      (M.oneShotProfile profile history who
        (profile who (M.infoOf who history.trace))) history hterm
    have hchosen : chosen = M.historyChooser profile history hterm := by
      dsimp only [chosen]
      rw [M.oneShotProfile_eq_self]
    rw [E.historyBackwardValue_of_not_terminal hterm]
    dsimp only [oneShotHistoryValue]
    exact le_of_eq (historyStepValue_history_congr_of_chosen_eq history
      hchosen
      (fun later => E.historyBackwardValue certificate
        (M.historyChooser profile) (fun outcome => utility outcome who) later)
      (fun later => E.historyBackwardValue certificate
        (M.historyChooser profile) (fun outcome => utility outcome who) later)
      (fun _ => rfl))

/-- Every finite-choice, well-founded, perfect-information protocol with a
single mover at each decision history has a pure subgame-perfect equilibrium.
No finiteness of states, histories, players, or outcomes—and no boundedness of
utility—is required. -/
theorem exists_isSubgamePerfect [DecidableEq ι]
    [∀ player, DecidableEq (M.InfoState player)]
    (singleMover : ∀ (state : E.State) {first second : ι},
      E.active state first → E.active state second → first = second)
    [∀ player info, Finite (M.Choice player info)]
    [∀ player info, Nonempty (M.Choice player info)]
    (certificate : E.WellFoundedPlay)
    (hperfect : M.SeparatesDecisionHistories)
    (utility : E.History → ι → ℝ) :
    ∃ profile : Profile M.strategicSignature,
      M.IsSubgamePerfect certificate profile utility := by
  refine ⟨M.backwardProfile singleMover certificate utility, ?_⟩
  apply M.isSubgamePerfect_of_hasNoProfitableOneShotDeviation
  exact M.backwardProfile_hasNoProfitableOneShotDeviation
    singleMover hperfect

end InformationModel

end GameTheory.Protocol
