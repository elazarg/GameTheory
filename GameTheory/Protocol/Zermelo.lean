/-
# Constructive backward induction for perfect information

`Backward` evaluates a fixed chooser and `SubgamePerfect` proves the one-shot
deviation principle.  This module supplies the missing construction: at each
nonterminal history, choose a finite maximizing action for the unique mover,
evaluate its continuation recursively, and assemble those history choices into
one information-local pure profile.

The construction uses the conventional strong perfect-information premise: an
information state at which a player moves identifies the complete history. It
does not introduce a second tree or evaluator. Finiteness is required only at
information states realized by genuine decision histories. Because a
contingent plan is total, the caller separately supplies a total fallback plan;
the construction preserves it at information states with no decision history.

The `Zermelo` module name follows the backward-induction tradition; no
two-player win/lose determinacy theorem is claimed by this file.
-/

import GameTheory.Protocol.HistoryChooserComposition

noncomputable section

namespace GameTheory.Protocol

open GameTheory.Math.Probability

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

/-- Under perfect information every history starts a subgame, because a
decision information set contains at most that history. -/
theorem isSubgameRoot_of_separatesDecisionHistories
    (hperfect : M.SeparatesDecisionHistories)
    (root : E.History) : M.IsSubgameRoot root := by
  intro who inside outside hinside hinsTerm hinsActive houtTerm houtActive hinfo
  have hequal := hperfect who inside outside hinsTerm hinsActive
    houtTerm houtActive hinfo
  simpa [hequal] using hinside

/-- A complete history realizes `info` as a genuine decision point for `who`.
Terminal histories are excluded explicitly because activity is intentionally
unconstrained by execution after a protocol has stopped.  An attached
information model may still constrain terminal activity through
`menu_adequate`; terminal histories are never decision sites either way. -/
def IsDecisionHistory (who : ι) (info : M.InfoState who)
    (history : E.History) : Prop :=
  ¬ E.terminal history.state ∧ E.active history.state who ∧
    M.infoOf who history.trace = info

/-- Only genuine decision information states need finite menus for backward
maximization. A total fallback policy separately supplies values at information
states that no decision history realizes. -/
def HasFiniteDecisionChoices : Prop :=
  ∀ (who : ι) (info : M.InfoState who) (history : E.History),
    M.IsDecisionHistory who info history → Finite (M.Choice who info)

/-- One current choice followed by independently optimized continuations at
every realized child. The fallback makes the resulting chooser total away
from those child cones. -/
def historyChoiceChooser [DecidableEq ι]
    (singleMover : ∀ (state : E.State) {first second : ι},
      E.active state first → E.active state second → first = second)
    (fallback : E.HistoryChooser)
    (history : E.History) (hterm : ¬ E.terminal history.state)
    (recurse : ∀ later : E.History,
      E.HistorySuccessor later history → E.HistoryChooser)
    (who : ι) (hactive : E.active history.state who)
    (choice : M.Choice who (M.infoOf who history.trace)) : E.HistoryChooser :=
  let chosen := M.jointOfChoice singleMover history hterm who hactive choice
  E.graftHistoryChooser fallback history chosen fun _target realized =>
    recurse (history.extend chosen.2 realized)
      ⟨chosen.1, chosen.2, realized⟩

/-- The score of one legal current choice is the expected payoff of its
actual terminal law. The all-chooser hypothesis certifies this particular
grafted chooser without assigning values to divergent laws. -/
def historyChoiceValue [DecidableEq ι]
    (singleMover : ∀ (state : E.State) {first second : ι},
      E.active state first → E.active state second → first = second)
    (fallback : E.HistoryChooser)
    (certificate : E.WellFoundedPlay)
    (utility : E.History → ι → ℝ)
    (hglobal : ∀ chooser history who,
      PayoffIntegrable (E.historyBackwardLaw certificate chooser history)
        (fun outcome => utility outcome who))
    (history : E.History) (hterm : ¬ E.terminal history.state)
    (recurse : ∀ later : E.History,
      E.HistorySuccessor later history → E.HistoryChooser)
    (who : ι) (hactive : E.active history.state who)
    (choice : M.Choice who (M.infoOf who history.trace)) : ℝ :=
  let chooser := M.historyChoiceChooser singleMover fallback history hterm
    recurse who hactive choice
  expect (E.historyBackwardLaw certificate chooser history)
    (fun outcome => utility outcome who) (hglobal chooser history who)

/-- Maximize the guarded expected payoff over the mover's finite menu. -/
def bestHistoryChoice [DecidableEq ι]
    (singleMover : ∀ (state : E.State) {first second : ι},
      E.active state first → E.active state second → first = second)
    (fallback : E.HistoryChooser)
    (certificate : E.WellFoundedPlay)
    (utility : E.History → ι → ℝ)
    (hglobal : ∀ chooser history who,
      PayoffIntegrable (E.historyBackwardLaw certificate chooser history)
        (fun outcome => utility outcome who))
    (history : E.History) (hterm : ¬ E.terminal history.state)
    (recurse : ∀ later : E.History,
      E.HistorySuccessor later history → E.HistoryChooser)
    (who : ι) (hactive : E.active history.state who)
    [Finite (M.Choice who (M.infoOf who history.trace))]
    [Nonempty (M.Choice who (M.infoOf who history.trace))] :
    M.Choice who (M.infoOf who history.trace) :=
  Classical.choose (Finite.exists_max
    (M.historyChoiceValue singleMover fallback certificate utility hglobal
      history hterm recurse who hactive))

theorem historyChoiceValue_le_bestHistoryChoice [DecidableEq ι]
    (singleMover : ∀ (state : E.State) {first second : ι},
      E.active state first → E.active state second → first = second)
    (fallback : E.HistoryChooser)
    (certificate : E.WellFoundedPlay)
    (utility : E.History → ι → ℝ)
    (hglobal : ∀ chooser history who,
      PayoffIntegrable (E.historyBackwardLaw certificate chooser history)
        (fun outcome => utility outcome who))
    (history : E.History) (hterm : ¬ E.terminal history.state)
    (recurse : ∀ later : E.History,
      E.HistorySuccessor later history → E.HistoryChooser)
    (who : ι) (hactive : E.active history.state who)
    [Finite (M.Choice who (M.infoOf who history.trace))]
    [Nonempty (M.Choice who (M.infoOf who history.trace))]
    (choice : M.Choice who (M.infoOf who history.trace)) :
    M.historyChoiceValue singleMover fallback certificate utility hglobal
      history hterm recurse who hactive choice ≤
      M.historyChoiceValue singleMover fallback certificate utility hglobal
        history hterm recurse who hactive
        (M.bestHistoryChoice singleMover fallback certificate utility hglobal
          history hterm recurse who hactive) :=
  Classical.choose_spec (Finite.exists_max
    (M.historyChoiceValue singleMover fallback certificate utility hglobal
      history hterm recurse who hactive)) choice

/-- The Bellman joint is chosen by guarded maximization when someone moves;
otherwise it is the unique legal no-op. -/
def backwardJoint [DecidableEq ι]
    (singleMover : ∀ (state : E.State) {first second : ι},
      E.active state first → E.active state second → first = second)
    (fallback : Profile M.strategicSignature)
    (finiteChoices : M.HasFiniteDecisionChoices)
    (certificate : E.WellFoundedPlay)
    (utility : E.History → ι → ℝ)
    (hglobal : ∀ chooser history who,
      PayoffIntegrable (E.historyBackwardLaw certificate chooser history)
        (fun outcome => utility outcome who))
    (history : E.History) (hterm : ¬ E.terminal history.state)
    (recurse : ∀ later : E.History,
      E.HistorySuccessor later history → E.HistoryChooser) :
    {joint : ∀ i, Option (E.Action i) // E.Legal history.state joint} := by
  classical
  exact if hactive : ∃ who, E.active history.state who then
      let who := Classical.choose hactive
      let whoActive := Classical.choose_spec hactive
      letI : Finite (M.Choice who (M.infoOf who history.trace)) :=
        finiteChoices who (M.infoOf who history.trace) history
          ⟨hterm, whoActive, rfl⟩
      letI : Nonempty (M.Choice who (M.infoOf who history.trace)) :=
        ⟨fallback who (M.infoOf who history.trace)⟩
      M.jointOfChoice singleMover history hterm who whoActive
        (M.bestHistoryChoice singleMover (M.historyChooser fallback)
          certificate utility hglobal history hterm recurse who whoActive)
    else
      ⟨E.noop, E.noop_isLegal hterm fun who active => hactive ⟨who, active⟩⟩

theorem backwardJoint_of_active [DecidableEq ι]
    (singleMover : ∀ (state : E.State) {first second : ι},
      E.active state first → E.active state second → first = second)
    (fallback : Profile M.strategicSignature)
    (finiteChoices : M.HasFiniteDecisionChoices)
    (certificate : E.WellFoundedPlay)
    (utility : E.History → ι → ℝ)
    (hglobal : ∀ chooser history who,
      PayoffIntegrable (E.historyBackwardLaw certificate chooser history)
        (fun outcome => utility outcome who))
    (history : E.History) (hterm : ¬ E.terminal history.state)
    (recurse : ∀ later : E.History,
      E.HistorySuccessor later history → E.HistoryChooser)
    (who : ι) (hactive : E.active history.state who) :
    M.backwardJoint singleMover fallback finiteChoices certificate utility
        hglobal history hterm recurse =
      M.jointOfChoice singleMover history hterm who hactive
        (by
          letI : Finite (M.Choice who (M.infoOf who history.trace)) :=
            finiteChoices who (M.infoOf who history.trace) history
              ⟨hterm, hactive, rfl⟩
          letI : Nonempty (M.Choice who (M.infoOf who history.trace)) :=
            ⟨fallback who (M.infoOf who history.trace)⟩
          exact M.bestHistoryChoice singleMover (M.historyChooser fallback)
            certificate utility hglobal history hterm recurse who hactive) := by
  classical
  let hexists : ∃ player, E.active history.state player := ⟨who, hactive⟩
  simp only [backwardJoint, dite_eq_left hexists]
  let selected := Classical.choose hexists
  have hselected := Classical.choose_spec hexists
  have heq : selected = who := singleMover history.state hselected hactive
  subst selected
  congr <;> apply proof_irrel_heq

/-- A total chooser for the recursively solved subtree at each history. -/
def backwardChooserBundle [DecidableEq ι]
    (singleMover : ∀ (state : E.State) {first second : ι},
      E.active state first → E.active state second → first = second)
    (fallback : Profile M.strategicSignature)
    (finiteChoices : M.HasFiniteDecisionChoices)
    (certificate : E.WellFoundedPlay)
    (utility : E.History → ι → ℝ)
    (hglobal : ∀ chooser history who,
      PayoffIntegrable (E.historyBackwardLaw certificate chooser history)
        (fun outcome => utility outcome who)) :
    E.History → E.HistoryChooser := by
  classical
  exact E.historyBackwardRec certificate fun history recurse =>
    if hterm : E.terminal history.state then M.historyChooser fallback
    else
      let chosen := M.backwardJoint singleMover fallback finiteChoices
        certificate utility hglobal history hterm recurse
      E.graftHistoryChooser (M.historyChooser fallback) history chosen
        fun _target realized =>
          recurse (history.extend chosen.2 realized)
            ⟨chosen.1, chosen.2, realized⟩

theorem backwardChooserBundle_of_not_terminal [DecidableEq ι]
    (singleMover : ∀ (state : E.State) {first second : ι},
      E.active state first → E.active state second → first = second)
    (fallback : Profile M.strategicSignature)
    (finiteChoices : M.HasFiniteDecisionChoices)
    {certificate : E.WellFoundedPlay}
    {utility : E.History → ι → ℝ}
    (hglobal : ∀ chooser history who,
      PayoffIntegrable (E.historyBackwardLaw certificate chooser history)
        (fun outcome => utility outcome who))
    {history : E.History} (hterm : ¬ E.terminal history.state) :
    M.backwardChooserBundle singleMover fallback finiteChoices certificate
        utility hglobal history =
      let recurse : ∀ later : E.History,
          E.HistorySuccessor later history → E.HistoryChooser :=
        fun later _ => M.backwardChooserBundle singleMover fallback
          finiteChoices certificate utility hglobal later
      let chosen := M.backwardJoint singleMover fallback finiteChoices
        certificate utility hglobal history hterm recurse
      E.graftHistoryChooser (M.historyChooser fallback) history chosen
        fun _target realized =>
          M.backwardChooserBundle singleMover fallback finiteChoices
            certificate utility hglobal (history.extend chosen.2 realized) := by
  rw [backwardChooserBundle, E.historyBackwardRec_eq, dite_eq_right hterm]

/-- The selected legal action at each complete history. -/
def backwardChooser [DecidableEq ι]
    (singleMover : ∀ (state : E.State) {first second : ι},
      E.active state first → E.active state second → first = second)
    (fallback : Profile M.strategicSignature)
    (finiteChoices : M.HasFiniteDecisionChoices)
    (certificate : E.WellFoundedPlay)
    (utility : E.History → ι → ℝ)
    (hglobal : ∀ chooser history who,
      PayoffIntegrable (E.historyBackwardLaw certificate chooser history)
        (fun outcome => utility outcome who)) : E.HistoryChooser :=
  fun history hterm =>
    (M.backwardChooserBundle singleMover fallback finiteChoices certificate
      utility hglobal history) history hterm

theorem backwardChooser_eq_joint [DecidableEq ι]
    (singleMover : ∀ (state : E.State) {first second : ι},
      E.active state first → E.active state second → first = second)
    (fallback : Profile M.strategicSignature)
    (finiteChoices : M.HasFiniteDecisionChoices)
    {certificate : E.WellFoundedPlay}
    {utility : E.History → ι → ℝ}
    (hglobal : ∀ chooser history who,
      PayoffIntegrable (E.historyBackwardLaw certificate chooser history)
        (fun outcome => utility outcome who))
    (history : E.History) (hterm : ¬ E.terminal history.state) :
    M.backwardChooser singleMover fallback finiteChoices certificate utility
        hglobal history hterm =
      M.backwardJoint singleMover fallback finiteChoices certificate utility
        hglobal history hterm
        (fun later _ => M.backwardChooserBundle singleMover fallback
          finiteChoices certificate utility hglobal later) := by
  rw [backwardChooser, M.backwardChooserBundle_of_not_terminal
    singleMover fallback finiteChoices hglobal hterm,
    E.graftHistoryChooser_at_parent]

/-- At a genuine decision information state, select the unique corresponding
history's Bellman action; elsewhere preserve the fallback plan. -/
def backwardPolicy [DecidableEq ι]
    (singleMover : ∀ (state : E.State) {first second : ι},
      E.active state first → E.active state second → first = second)
    (fallback : Profile M.strategicSignature)
    (finiteChoices : M.HasFiniteDecisionChoices)
    (certificate : E.WellFoundedPlay)
    (utility : E.History → ι → ℝ)
    (hglobal : ∀ chooser history who,
      PayoffIntegrable (E.historyBackwardLaw certificate chooser history)
        (fun outcome => utility outcome who))
    (who : ι) : M.Policy who :=
  fun info => by
    classical
    by_cases hreached : ∃ history, M.IsDecisionHistory who info history
    · let history := Classical.choose hreached
      have hh := Classical.choose_spec hreached
      have hterm : ¬ E.terminal history.state := hh.1
      have hinfo : M.infoOf who history.trace = info := hh.2.2
      let chosen := M.backwardChooser singleMover fallback finiteChoices
        certificate utility hglobal history hterm
      refine ⟨chosen.1 who, ?_⟩
      rw [← hinfo]
      exact (M.menu_adequate who history.trace (chosen.1 who)).mpr
        (ExecutionProtocol.legalOption_of_legal chosen.2 who)
    · exact fallback who info

theorem backwardPolicy_eq_fallback_of_no_decision_history [DecidableEq ι]
    (singleMover : ∀ (state : E.State) {first second : ι},
      E.active state first → E.active state second → first = second)
    (fallback : Profile M.strategicSignature)
    (finiteChoices : M.HasFiniteDecisionChoices)
    {certificate : E.WellFoundedPlay}
    {utility : E.History → ι → ℝ}
    (hglobal : ∀ chooser history who,
      PayoffIntegrable (E.historyBackwardLaw certificate chooser history)
        (fun outcome => utility outcome who))
    (who : ι) (info : M.InfoState who)
    (hunreachable : ¬ ∃ history, M.IsDecisionHistory who info history) :
    M.backwardPolicy singleMover fallback finiteChoices certificate utility
        hglobal who info = fallback who info := by
  simp [backwardPolicy, hunreachable]

/-- The information-local pure profile assembled from backward induction. -/
def backwardProfile [DecidableEq ι]
    (singleMover : ∀ (state : E.State) {first second : ι},
      E.active state first → E.active state second → first = second)
    (fallback : Profile M.strategicSignature)
    (finiteChoices : M.HasFiniteDecisionChoices)
    (certificate : E.WellFoundedPlay)
    (utility : E.History → ι → ℝ)
    (hglobal : ∀ chooser history who,
      PayoffIntegrable (E.historyBackwardLaw certificate chooser history)
        (fun outcome => utility outcome who)) : Profile M.strategicSignature :=
  fun who => M.backwardPolicy singleMover fallback finiteChoices certificate
    utility hglobal who

private theorem backwardChooser_action_eq_of_history_eq [DecidableEq ι]
    (singleMover : ∀ (state : E.State) {first second : ι},
      E.active state first → E.active state second → first = second)
    (fallback : Profile M.strategicSignature)
    (finiteChoices : M.HasFiniteDecisionChoices)
    {certificate : E.WellFoundedPlay}
    {utility : E.History → ι → ℝ}
    (hglobal : ∀ chooser history who,
      PayoffIntegrable (E.historyBackwardLaw certificate chooser history)
        (fun outcome => utility outcome who))
    {first second : E.History} (heq : first = second)
    (hfirst : ¬ E.terminal first.state)
    (hsecond : ¬ E.terminal second.state) (who : ι) :
    (M.backwardChooser singleMover fallback finiteChoices certificate utility
        hglobal first hfirst).1 who =
      (M.backwardChooser singleMover fallback finiteChoices certificate utility
        hglobal second hsecond).1 who := by
  subst second
  rfl

theorem backwardPolicy_act_at_decision [DecidableEq ι]
    (singleMover : ∀ (state : E.State) {first second : ι},
      E.active state first → E.active state second → first = second)
    (fallback : Profile M.strategicSignature)
    (finiteChoices : M.HasFiniteDecisionChoices)
    {certificate : E.WellFoundedPlay}
    {utility : E.History → ι → ℝ}
    (hglobal : ∀ chooser history who,
      PayoffIntegrable (E.historyBackwardLaw certificate chooser history)
        (fun outcome => utility outcome who))
    (hperfect : M.SeparatesDecisionHistories)
    (history : E.History) (hterm : ¬ E.terminal history.state)
    (who : ι) (hactive : E.active history.state who) :
    (M.backwardPolicy singleMover fallback finiteChoices certificate utility
        hglobal who).act (M.infoOf who history.trace) =
      (M.backwardChooser singleMover fallback finiteChoices certificate utility
        hglobal history hterm).1 who := by
  classical
  let hreached : ∃ prior,
      M.IsDecisionHistory who (M.infoOf who history.trace) prior :=
    ⟨history, hterm, hactive, rfl⟩
  simp only [backwardPolicy, dite_eq_left hreached, Policy.act]
  let prior := Classical.choose hreached
  have hprior := Classical.choose_spec hreached
  have heq : prior = history :=
    hperfect who prior history hprior.1 hprior.2.1 hterm hactive hprior.2.2
  exact M.backwardChooser_action_eq_of_history_eq singleMover fallback
    finiteChoices hglobal heq hprior.1 hterm who

theorem historyChooser_backwardProfile [DecidableEq ι]
    (singleMover : ∀ (state : E.State) {first second : ι},
      E.active state first → E.active state second → first = second)
    (fallback : Profile M.strategicSignature)
    (finiteChoices : M.HasFiniteDecisionChoices)
    {certificate : E.WellFoundedPlay}
    {utility : E.History → ι → ℝ}
    (hglobal : ∀ chooser history who,
      PayoffIntegrable (E.historyBackwardLaw certificate chooser history)
        (fun outcome => utility outcome who))
    (hperfect : M.SeparatesDecisionHistories)
    (history : E.History) (hterm : ¬ E.terminal history.state) :
    M.historyChooser
        (M.backwardProfile singleMover fallback finiteChoices certificate
          utility hglobal) history hterm =
      M.backwardChooser singleMover fallback finiteChoices certificate utility
        hglobal history hterm := by
  apply Subtype.ext
  funext who
  by_cases hactive : E.active history.state who
  · simpa [backwardProfile, InformationModel.historyChooser,
      InformationModel.jointAt] using
      M.backwardPolicy_act_at_decision singleMover fallback finiteChoices
        hglobal hperfect history hterm who hactive
  · have hprofile := LegalOption.eq_none_of_inactive
      ((M.historyChooser
        (M.backwardProfile singleMover fallback finiteChoices certificate
          utility hglobal) history hterm).1 who)
      (ExecutionProtocol.legalOption_of_legal
        (M.historyChooser
          (M.backwardProfile singleMover fallback finiteChoices certificate
            utility hglobal) history hterm).2 who)
      hactive
    have hbackward := LegalOption.eq_none_of_inactive
      ((M.backwardChooser singleMover fallback finiteChoices certificate
        utility hglobal history hterm).1 who)
      (ExecutionProtocol.legalOption_of_legal
        (M.backwardChooser singleMover fallback finiteChoices certificate
          utility hglobal history hterm).2 who)
      hactive
    exact hprofile.trans hbackward.symm

/-- At every history, the assembled information-local profile has exactly the
terminal law of that history's recursively selected chooser. -/
theorem historyBackwardLaw_backwardProfile [DecidableEq ι]
    (singleMover : ∀ (state : E.State) {first second : ι},
      E.active state first → E.active state second → first = second)
    (fallback : Profile M.strategicSignature)
    (finiteChoices : M.HasFiniteDecisionChoices)
    {certificate : E.WellFoundedPlay}
    {utility : E.History → ι → ℝ}
    (hglobal : ∀ chooser history who,
      PayoffIntegrable (E.historyBackwardLaw certificate chooser history)
        (fun outcome => utility outcome who))
    (hperfect : M.SeparatesDecisionHistories) :
    ∀ history : E.History,
      E.historyBackwardLaw certificate
          (M.historyChooser (M.backwardProfile singleMover fallback
            finiteChoices certificate utility hglobal)) history =
        E.historyBackwardLaw certificate
          (M.backwardChooserBundle singleMover fallback finiteChoices
            certificate utility hglobal history) history := by
  intro history
  induction history using
      (E.wellFounded_historySuccessor certificate).induction with
  | _ current ih =>
      by_cases hterm : E.terminal current.state
      · rw [E.historyBackwardLaw_of_terminal hterm,
          E.historyBackwardLaw_of_terminal hterm]
      · let recurse : ∀ later : E.History,
            E.HistorySuccessor later current → E.HistoryChooser :=
          fun later _ => M.backwardChooserBundle singleMover fallback
            finiteChoices certificate utility hglobal later
        let chosen := M.backwardJoint singleMover fallback finiteChoices
          certificate utility hglobal current hterm recurse
        have hchosen : M.historyChooser
              (M.backwardProfile singleMover fallback finiteChoices
                certificate utility hglobal) current hterm = chosen := by
          calc
            _ = M.backwardChooser singleMover fallback finiteChoices
                certificate utility hglobal current hterm :=
              M.historyChooser_backwardProfile singleMover fallback
                finiteChoices hglobal hperfect current hterm
            _ = chosen := M.backwardChooser_eq_joint singleMover fallback
              finiteChoices hglobal current hterm
        have hbundle :
            M.backwardChooserBundle singleMover fallback finiteChoices
                certificate utility hglobal current =
              E.graftHistoryChooser (M.historyChooser fallback) current chosen
                (fun _target realized =>
                  M.backwardChooserBundle singleMover fallback finiteChoices
                    certificate utility hglobal
                    (current.extend chosen.2 realized)) :=
          M.backwardChooserBundle_of_not_terminal singleMover fallback
            finiteChoices hglobal hterm
        calc
          E.historyBackwardLaw certificate
              (M.historyChooser (M.backwardProfile singleMover fallback
                finiteChoices certificate utility hglobal)) current =
            (E.step current.state chosen).bindOnSupport fun _target realized =>
              E.historyBackwardLaw certificate
                (M.historyChooser (M.backwardProfile singleMover fallback
                  finiteChoices certificate utility hglobal))
                (current.extend chosen.2 realized) :=
            E.historyBackwardLaw_of_not_terminal_of_chooser_eq hterm chosen hchosen
          _ = (E.step current.state chosen).bindOnSupport
              (fun _target realized =>
                E.historyBackwardLaw certificate
                  (M.backwardChooserBundle singleMover fallback finiteChoices
                    certificate utility hglobal
                    (current.extend chosen.2 realized))
                  (current.extend chosen.2 realized)) := by
            apply bindOnSupport_congr
            intro target realized
            exact ih (current.extend chosen.2 realized)
              ⟨chosen.1, chosen.2, realized⟩
          _ = E.historyBackwardLaw certificate
              (M.backwardChooserBundle singleMover fallback finiteChoices
                certificate utility hglobal current) current := by
            rw [hbundle]
            exact (E.historyBackwardLaw_graft certificate
              (M.historyChooser fallback) current hterm chosen
              (fun _target realized =>
                M.backwardChooserBundle singleMover fallback finiteChoices
                  certificate utility hglobal
                  (current.extend chosen.2 realized))).symm

/-- The guarded real value of the recursively selected terminal law. -/
def backwardOutcome [DecidableEq ι]
    (singleMover : ∀ (state : E.State) {first second : ι},
      E.active state first → E.active state second → first = second)
    (fallback : Profile M.strategicSignature)
    (finiteChoices : M.HasFiniteDecisionChoices)
    (certificate : E.WellFoundedPlay)
    (utility : E.History → ι → ℝ)
    (hglobal : ∀ chooser history who,
      PayoffIntegrable (E.historyBackwardLaw certificate chooser history)
        (fun outcome => utility outcome who))
    (history : E.History) (who : ι) : ℝ :=
  let chooser := M.backwardChooserBundle singleMover fallback finiteChoices
    certificate utility hglobal history
  expect (E.historyBackwardLaw certificate chooser history)
    (fun outcome => utility outcome who) (hglobal chooser history who)

theorem backwardOutcome_of_terminal [DecidableEq ι]
    (singleMover : ∀ (state : E.State) {first second : ι},
      E.active state first → E.active state second → first = second)
    (fallback : Profile M.strategicSignature)
    (finiteChoices : M.HasFiniteDecisionChoices)
    {certificate : E.WellFoundedPlay}
    {utility : E.History → ι → ℝ}
    (hglobal : ∀ chooser history who,
      PayoffIntegrable (E.historyBackwardLaw certificate chooser history)
        (fun outcome => utility outcome who))
    {history : E.History} (hterm : E.terminal history.state) (who : ι) :
    M.backwardOutcome singleMover fallback finiteChoices certificate utility
      hglobal history who = utility history who := by
  dsimp only [backwardOutcome]
  simp only [E.historyBackwardLaw_of_terminal hterm, expect_pure]

/-- Numerical Bellman equation for the selected joint. Only values at
supported successors must agree with the recursively selected continuation;
the outer integrability witness follows from the actual terminal law. -/
theorem backwardOutcome_of_not_terminal [DecidableEq ι]
    (singleMover : ∀ (state : E.State) {first second : ι},
      E.active state first → E.active state second → first = second)
    (fallback : Profile M.strategicSignature)
    (finiteChoices : M.HasFiniteDecisionChoices)
    {certificate : E.WellFoundedPlay}
    {utility : E.History → ι → ℝ}
    (hglobal : ∀ chooser history who,
      PayoffIntegrable (E.historyBackwardLaw certificate chooser history)
        (fun outcome => utility outcome who))
    (history : E.History) (hterm : ¬ E.terminal history.state)
    (who : ι)
    (successorValue : E.State → ℝ)
    (hagree : ∀ target,
      ∀ realized : target ∈
        (E.step history.state
          (M.backwardJoint singleMover fallback finiteChoices certificate
            utility hglobal history hterm
            (fun later _ => M.backwardChooserBundle singleMover fallback
              finiteChoices certificate utility hglobal later))).support,
      successorValue target =
        M.backwardOutcome singleMover fallback finiteChoices certificate
          utility hglobal
          (history.extend
            (M.backwardJoint singleMover fallback finiteChoices certificate
              utility hglobal history hterm
              (fun later _ => M.backwardChooserBundle singleMover fallback
                finiteChoices certificate utility hglobal later)).2 realized)
          who) :
    let chosen := M.backwardJoint singleMover fallback finiteChoices
      certificate utility hglobal history hterm
      (fun later _ => M.backwardChooserBundle singleMover fallback
        finiteChoices certificate utility hglobal later)
    ∃ houter : PayoffIntegrable
        (E.step history.state chosen) successorValue,
      M.backwardOutcome singleMover fallback finiteChoices certificate utility
          hglobal history who =
        expect (E.step history.state chosen) successorValue houter := by
  let bundle := M.backwardChooserBundle singleMover fallback finiteChoices
    certificate utility hglobal history
  let chosen := M.backwardJoint singleMover fallback finiteChoices
    certificate utility hglobal history hterm
    (fun later _ => M.backwardChooserBundle singleMover fallback finiteChoices
      certificate utility hglobal later)
  let p := E.step history.state chosen
  let q : ∀ target, target ∈ p.support → PMF E.History :=
    fun _target realized =>
      E.historyBackwardLaw certificate
        (M.backwardChooserBundle singleMover fallback finiteChoices
          certificate utility hglobal (history.extend chosen.2 realized))
        (history.extend chosen.2 realized)
  let f : E.History → ℝ := fun outcome => utility outcome who
  have hbundle : bundle = E.graftHistoryChooser
      (M.historyChooser fallback) history chosen
      (fun _target realized =>
        M.backwardChooserBundle singleMover fallback finiteChoices
          certificate utility hglobal (history.extend chosen.2 realized)) :=
    M.backwardChooserBundle_of_not_terminal singleMover fallback
      finiteChoices hglobal hterm
  have hlaw : E.historyBackwardLaw certificate bundle history =
      p.bindOnSupport q := by
    rw [hbundle]
    exact E.historyBackwardLaw_graft certificate (M.historyChooser fallback)
      history hterm chosen
      (fun _target realized =>
        M.backwardChooserBundle singleMover fallback finiteChoices
          certificate utility hglobal (history.extend chosen.2 realized))
  have hbind : PayoffIntegrable (p.bindOnSupport q) f := by
    rw [← hlaw]
    exact hglobal bundle history who
  have hcond : ∀ target, ∀ realized : target ∈ p.support,
      successorValue target = expect (q target realized) f
        (payoffIntegrable_bindOnSupport_conditional_on_support
          p q f hbind target realized) := by
    intro target realized
    rw [hagree target realized]
    dsimp only [backwardOutcome, q, f]
  refine ⟨payoffIntegrable_bindOnSupport_conditionalValue_on_support
    p q f hbind successorValue hcond, ?_⟩
  calc
    M.backwardOutcome singleMover fallback finiteChoices certificate utility
        hglobal history who = expect (p.bindOnSupport q) f hbind :=
      expectedUtility_congr_law utility who hlaw (hglobal bundle history who) hbind
    _ = expect p successorValue
          (payoffIntegrable_bindOnSupport_conditionalValue_on_support
            p q f hbind successorValue hcond) :=
      expect_bindOnSupport_tower_on_support p q f hbind successorValue hcond

theorem historyBackwardValue_backwardProfile [DecidableEq ι]
    (singleMover : ∀ (state : E.State) {first second : ι},
      E.active state first → E.active state second → first = second)
    (fallback : Profile M.strategicSignature)
    (finiteChoices : M.HasFiniteDecisionChoices)
    {certificate : E.WellFoundedPlay}
    {utility : E.History → ι → ℝ}
    (hglobal : ∀ chooser history who,
      PayoffIntegrable (E.historyBackwardLaw certificate chooser history)
        (fun outcome => utility outcome who))
    (hperfect : M.SeparatesDecisionHistories)
    (history : E.History) (who : ι) :
    E.historyBackwardValue certificate
        (M.historyChooser (M.backwardProfile singleMover fallback finiteChoices
          certificate utility hglobal))
        (fun outcome => utility outcome who) history
        (hglobal (M.historyChooser (M.backwardProfile singleMover fallback
          finiteChoices certificate utility hglobal)) history who) =
      M.backwardOutcome singleMover fallback finiteChoices certificate utility
        hglobal history who := by
  simp only [ExecutionProtocol.historyBackwardValue, backwardOutcome]
  simp only [M.historyBackwardLaw_backwardProfile singleMover fallback
    finiteChoices hglobal hperfect history]

/-- One-shot replacement at the current history gives exactly the legal
joint constructed from the replacement choice. -/
theorem historyChooser_oneShot_backwardProfile [DecidableEq ι]
    [∀ player, DecidableEq (M.InfoState player)]
    (singleMover : ∀ (state : E.State) {first second : ι},
      E.active state first → E.active state second → first = second)
    (fallback : Profile M.strategicSignature)
    (finiteChoices : M.HasFiniteDecisionChoices)
    {certificate : E.WellFoundedPlay}
    {utility : E.History → ι → ℝ}
    (hglobal : ∀ chooser history who,
      PayoffIntegrable (E.historyBackwardLaw certificate chooser history)
        (fun outcome => utility outcome who))
    (history : E.History) (hterm : ¬ E.terminal history.state)
    (who : ι) (hactive : E.active history.state who)
    (choice : M.Choice who (M.infoOf who history.trace)) :
    M.historyChooser
        (M.oneShotProfile
          (M.backwardProfile singleMover fallback finiteChoices certificate
            utility hglobal) history who choice) history hterm =
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
          (M.backwardProfile singleMover fallback finiteChoices certificate
            utility hglobal) history who choice) history hterm).1 other)
      (ExecutionProtocol.legalOption_of_legal
        (M.historyChooser
          (M.oneShotProfile
            (M.backwardProfile singleMover fallback finiteChoices certificate
              utility hglobal) history who choice) history hterm).2 other)
      hinactive
    have halternative := LegalOption.eq_none_of_inactive
      ((M.jointOfChoice singleMover history hterm who hactive choice).1 other)
      (ExecutionProtocol.legalOption_of_legal
        (M.jointOfChoice singleMover history hterm who hactive choice).2 other)
      hinactive
    exact hchanged.trans halternative.symm

/-- A current replacement under the assembled profile has the same terminal
law as the corresponding graft of recursively optimized child choosers. -/
theorem oneShotHistoryLaw_backwardProfile [DecidableEq ι]
    [∀ player, DecidableEq (M.InfoState player)]
    (singleMover : ∀ (state : E.State) {first second : ι},
      E.active state first → E.active state second → first = second)
    (fallback : Profile M.strategicSignature)
    (finiteChoices : M.HasFiniteDecisionChoices)
    {certificate : E.WellFoundedPlay}
    {utility : E.History → ι → ℝ}
    (hglobal : ∀ chooser history who,
      PayoffIntegrable (E.historyBackwardLaw certificate chooser history)
        (fun outcome => utility outcome who))
    (hperfect : M.SeparatesDecisionHistories)
    (history : E.History) (hterm : ¬ E.terminal history.state)
    (who : ι) (hactive : E.active history.state who)
    (choice : M.Choice who (M.infoOf who history.trace)) :
    M.oneShotHistoryLaw certificate
        (M.backwardProfile singleMover fallback finiteChoices certificate
          utility hglobal) who history hterm choice =
      E.historyBackwardLaw certificate
        (M.historyChoiceChooser singleMover (M.historyChooser fallback)
          history hterm
          (fun later _ => M.backwardChooserBundle singleMover fallback
            finiteChoices certificate utility hglobal later)
          who hactive choice) history := by
  let chosen := M.jointOfChoice singleMover history hterm who hactive choice
  have hchanged : M.historyChooser
      (M.oneShotProfile
        (M.backwardProfile singleMover fallback finiteChoices certificate
          utility hglobal) history who choice) history hterm = chosen :=
    M.historyChooser_oneShot_backwardProfile singleMover fallback
      finiteChoices hglobal history hterm who hactive choice
  have hchoice : M.historyChoiceChooser singleMover (M.historyChooser fallback)
      history hterm
      (fun later _ => M.backwardChooserBundle singleMover fallback
        finiteChoices certificate utility hglobal later)
      who hactive choice =
      E.graftHistoryChooser (M.historyChooser fallback) history chosen
        (fun _target realized => M.backwardChooserBundle singleMover fallback
          finiteChoices certificate utility hglobal
          (history.extend chosen.2 realized)) := rfl
  calc
    M.oneShotHistoryLaw certificate
        (M.backwardProfile singleMover fallback finiteChoices certificate
          utility hglobal) who history hterm choice =
      (E.step history.state chosen).bindOnSupport fun _target realized =>
        E.historyBackwardLaw certificate
          (M.historyChooser (M.backwardProfile singleMover fallback
            finiteChoices certificate utility hglobal))
          (history.extend chosen.2 realized) :=
      congrArg (fun selected : {joint : ∀ i, Option (E.Action i) //
        E.Legal history.state joint} =>
        (E.step history.state selected).bindOnSupport fun _target realized =>
          E.historyBackwardLaw certificate
            (M.historyChooser (M.backwardProfile singleMover fallback
              finiteChoices certificate utility hglobal))
            (history.extend selected.2 realized)) hchanged
    _ = (E.step history.state chosen).bindOnSupport
          (fun _target realized =>
            E.historyBackwardLaw certificate
              (M.backwardChooserBundle singleMover fallback finiteChoices
                certificate utility hglobal
                (history.extend chosen.2 realized))
              (history.extend chosen.2 realized)) := by
      apply bindOnSupport_congr
      intro target realized
      exact M.historyBackwardLaw_backwardProfile singleMover fallback
        finiteChoices hglobal hperfect (history.extend chosen.2 realized)
    _ = E.historyBackwardLaw certificate
          (M.historyChoiceChooser singleMover (M.historyChooser fallback)
            history hterm
            (fun later _ => M.backwardChooserBundle singleMover fallback
              finiteChoices certificate utility hglobal later)
            who hactive choice) history := by
      rw [hchoice]
      exact (E.historyBackwardLaw_graft certificate
        (M.historyChooser fallback) history hterm chosen
        (fun _target realized => M.backwardChooserBundle singleMover fallback
          finiteChoices certificate utility hglobal
          (history.extend chosen.2 realized))).symm

/-- At a decision history the recursively selected value is exactly the
guarded score of the maximizing current choice. -/
theorem backwardOutcome_eq_bestHistoryChoiceValue [DecidableEq ι]
    (singleMover : ∀ (state : E.State) {first second : ι},
      E.active state first → E.active state second → first = second)
    (fallback : Profile M.strategicSignature)
    (finiteChoices : M.HasFiniteDecisionChoices)
    {certificate : E.WellFoundedPlay}
    {utility : E.History → ι → ℝ}
    (hglobal : ∀ chooser history who,
      PayoffIntegrable (E.historyBackwardLaw certificate chooser history)
        (fun outcome => utility outcome who))
    (history : E.History) (hterm : ¬ E.terminal history.state)
    (who : ι) (hactive : E.active history.state who) :
    letI : Finite (M.Choice who (M.infoOf who history.trace)) :=
      finiteChoices who (M.infoOf who history.trace) history
        ⟨hterm, hactive, rfl⟩
    letI : Nonempty (M.Choice who (M.infoOf who history.trace)) :=
      ⟨fallback who (M.infoOf who history.trace)⟩
    M.backwardOutcome singleMover fallback finiteChoices certificate utility
        hglobal history who =
      M.historyChoiceValue singleMover (M.historyChooser fallback)
        certificate utility hglobal history hterm
        (fun later _ => M.backwardChooserBundle singleMover fallback
          finiteChoices certificate utility hglobal later)
        who hactive
        (M.bestHistoryChoice singleMover (M.historyChooser fallback)
          certificate utility hglobal history hterm
          (fun later _ => M.backwardChooserBundle singleMover fallback
            finiteChoices certificate utility hglobal later)
          who hactive) := by
  classical
  have : Finite (M.Choice who (M.infoOf who history.trace)) :=
    finiteChoices who (M.infoOf who history.trace) history
      ⟨hterm, hactive, rfl⟩
  have : Nonempty (M.Choice who (M.infoOf who history.trace)) :=
    ⟨fallback who (M.infoOf who history.trace)⟩
  let best := M.bestHistoryChoice singleMover (M.historyChooser fallback)
    certificate utility hglobal history hterm
    (fun later _ => M.backwardChooserBundle singleMover fallback finiteChoices
      certificate utility hglobal later) who hactive
  have hchooser : M.backwardChooserBundle singleMover fallback finiteChoices
        certificate utility hglobal history =
      M.historyChoiceChooser singleMover (M.historyChooser fallback)
        history hterm
        (fun later _ => M.backwardChooserBundle singleMover fallback
          finiteChoices certificate utility hglobal later)
        who hactive best := by
    rw [M.backwardChooserBundle_of_not_terminal singleMover fallback
      finiteChoices hglobal hterm]
    dsimp only
    rw [M.backwardJoint_of_active singleMover fallback finiteChoices
      certificate utility hglobal history hterm
      (fun later _ => M.backwardChooserBundle singleMover fallback
        finiteChoices certificate utility hglobal later) who hactive]
    rfl
  exact congrArg (fun chooser =>
    expect (E.historyBackwardLaw certificate chooser history)
      (fun outcome => utility outcome who) (hglobal chooser history who)) hchooser

/-- Exact all-chooser integrability makes every local candidate value
well-defined, and finite-menu Bellman maximization prevents a profitable
one-shot deviation at any history. -/
theorem backwardProfile_hasNoProfitableOneShotDeviation [DecidableEq ι]
    [∀ player, DecidableEq (M.InfoState player)]
    (singleMover : ∀ (state : E.State) {first second : ι},
      E.active state first → E.active state second → first = second)
    (fallback : Profile M.strategicSignature)
    (finiteChoices : M.HasFiniteDecisionChoices)
    {certificate : E.WellFoundedPlay}
    {utility : E.History → ι → ℝ}
    (hglobal : ∀ chooser history who,
      PayoffIntegrable (E.historyBackwardLaw certificate chooser history)
        (fun outcome => utility outcome who))
    (hperfect : M.SeparatesDecisionHistories) :
    M.HasNoProfitableOneShotDeviation certificate
      (M.backwardProfile singleMover fallback finiteChoices certificate
        utility hglobal) utility := by
  intro who history hterm
  let profile := M.backwardProfile singleMover fallback finiteChoices
    certificate utility hglobal
  let ctx := M.oneShotHistoryContext certificate profile utility who history hterm
  have hinc : ctx.IntegrableAt
      (profile who (M.infoOf who history.trace)) := by
    dsimp only [ctx, Context.IntegrableAt, oneShotHistoryContext]
    rw [M.oneShotHistoryLaw_self certificate profile who history hterm]
    exact hglobal (M.historyChooser profile) history who
  refine ⟨hinc, ?_, ?_⟩
  · intro choice _
    by_cases hactive : E.active history.state who
    · let candidate := M.historyChoiceChooser singleMover
        (M.historyChooser fallback) history hterm
        (fun later _ => M.backwardChooserBundle singleMover fallback
          finiteChoices certificate utility hglobal later)
        who hactive choice
      have hlaw : M.oneShotHistoryLaw certificate profile who history hterm
          choice = E.historyBackwardLaw certificate candidate history :=
        M.oneShotHistoryLaw_backwardProfile singleMover fallback
          finiteChoices hglobal hperfect history hterm who hactive choice
      dsimp only [ctx, Context.IntegrableAt, oneShotHistoryContext]
      rw [hlaw]
      exact hglobal candidate history who
    · have hchoice : choice =
          profile who (M.infoOf who history.trace) :=
        (M.subsingleton_choice_of_not_active history.trace hactive).elim _ _
      subst choice
      exact hinc
  · intro choice _ hinc' halt
    by_cases hactive : E.active history.state who
    · have hfinite : Finite (M.Choice who (M.infoOf who history.trace)) :=
        finiteChoices who (M.infoOf who history.trace) history
          ⟨hterm, hactive, rfl⟩
      have hnonempty : Nonempty (M.Choice who
          (M.infoOf who history.trace)) :=
        ⟨fallback who (M.infoOf who history.trace)⟩
      let recurse : ∀ later : E.History,
          E.HistorySuccessor later history → E.HistoryChooser :=
        fun later _ => M.backwardChooserBundle singleMover fallback
          finiteChoices certificate utility hglobal later
      let candidate := M.historyChoiceChooser singleMover
        (M.historyChooser fallback) history hterm recurse who hactive choice
      have hlaw : M.oneShotHistoryLaw certificate profile who history hterm
          choice = E.historyBackwardLaw certificate candidate history :=
        M.oneShotHistoryLaw_backwardProfile singleMover fallback
          finiteChoices hglobal hperfect history hterm who hactive choice
      have hleft : ctx.value choice halt =
          M.historyChoiceValue singleMover (M.historyChooser fallback)
            certificate utility hglobal history hterm recurse who hactive
            choice := by
        simp only [ctx, Context.value, oneShotHistoryContext,
          historyChoiceValue, hlaw]
        dsimp only [candidate, recurse]
      have hright : ctx.value
          (profile who (M.infoOf who history.trace)) hinc' =
          M.backwardOutcome singleMover fallback finiteChoices certificate
            utility hglobal history who := by
        have hlaw : ctx.outcome
            (profile who (M.infoOf who history.trace)) =
            E.historyBackwardLaw certificate
              (M.backwardChooserBundle singleMover fallback finiteChoices
                certificate utility hglobal history) history := by
          exact (M.oneShotHistoryLaw_self certificate profile who history hterm).trans
            (M.historyBackwardLaw_backwardProfile singleMover fallback
              finiteChoices hglobal hperfect history)
        exact expectedUtility_congr_law utility who hlaw hinc'
          (hglobal (M.backwardChooserBundle singleMover fallback finiteChoices
            certificate utility hglobal history) history who)
      calc
        ctx.value choice halt =
            M.historyChoiceValue singleMover (M.historyChooser fallback)
              certificate utility hglobal history hterm recurse who hactive
              choice := hleft
        _ ≤ M.historyChoiceValue singleMover (M.historyChooser fallback)
              certificate utility hglobal history hterm recurse who hactive
              (M.bestHistoryChoice singleMover (M.historyChooser fallback)
                certificate utility hglobal history hterm recurse who hactive) :=
          M.historyChoiceValue_le_bestHistoryChoice singleMover
            (M.historyChooser fallback) certificate utility hglobal history
            hterm recurse who hactive choice
        _ = M.backwardOutcome singleMover fallback finiteChoices certificate
              utility hglobal history who :=
          (M.backwardOutcome_eq_bestHistoryChoiceValue singleMover
            fallback finiteChoices hglobal history hterm who hactive).symm
        _ = ctx.value (profile who (M.infoOf who history.trace)) hinc' :=
          hright.symm
    · have hchoice : choice =
          profile who (M.infoOf who history.trace) :=
        (M.subsingleton_choice_of_not_active history.trace hactive).elim _ _
      subst choice
      exact le_of_eq (expect_proof_irrel _ _ _ _)

/-- Well-founded perfect-information backward induction yields a pure
subgame-perfect profile when every actual history-chooser terminal law has a
finite real payoff for every player. This exact family includes every
counterfactual chooser assembled during finite-menu maximization. -/
theorem exists_isSubgamePerfect [DecidableEq ι]
    [∀ player, DecidableEq (M.InfoState player)]
    (singleMover : ∀ (state : E.State) {first second : ι},
      E.active state first → E.active state second → first = second)
    (fallback : Profile M.strategicSignature)
    (finiteChoices : M.HasFiniteDecisionChoices)
    (certificate : E.WellFoundedPlay)
    (hperfect : M.SeparatesDecisionHistories)
    (utility : E.History → ι → ℝ)
    (hglobal : ∀ chooser history who,
      PayoffIntegrable (E.historyBackwardLaw certificate chooser history)
        (fun outcome => utility outcome who)) :
    ∃ profile : Profile M.strategicSignature,
      M.IsSubgamePerfect certificate profile utility := by
  let profile := M.backwardProfile singleMover fallback finiteChoices
    certificate utility hglobal
  refine ⟨profile, ?_⟩
  apply IsHistorywiseOptimal.isSubgamePerfect
  apply M.isHistorywiseOptimal_of_hasNoProfitableOneShotDeviation
  · exact M.backwardProfile_hasNoProfitableOneShotDeviation singleMover
      fallback finiteChoices hglobal hperfect
  · intro who alternative history
    exact hglobal (M.historyChooser (Profile.update profile who alternative))
      history who

/-- The finite-transition domain recovers the constructor for arbitrary real
terminal payoffs, with no global payoff bound or finite history carrier. -/
theorem exists_isSubgamePerfect_of_finite_step_support [DecidableEq ι]
    [∀ player, DecidableEq (M.InfoState player)]
    (singleMover : ∀ (state : E.State) {first second : ι},
      E.active state first → E.active state second → first = second)
    (fallback : Profile M.strategicSignature)
    (finiteChoices : M.HasFiniteDecisionChoices)
    (certificate : E.WellFoundedPlay)
    (hperfect : M.SeparatesDecisionHistories)
    (utility : E.History → ι → ℝ)
    (hfinite : ∀ (history : E.History)
      (_hterm : ¬ E.terminal history.state)
      (chosen : {joint : ∀ i, Option (E.Action i) //
        E.Legal history.state joint}),
      (E.step history.state chosen).support.Finite) :
    ∃ profile : Profile M.strategicSignature,
      M.IsSubgamePerfect certificate profile utility := by
  apply M.exists_isSubgamePerfect singleMover fallback finiteChoices
    certificate hperfect utility
  intro chooser history who
  exact E.payoffIntegrable_historyBackwardLaw_of_finite_step_support
    hfinite chooser (fun outcome => utility outcome who) history

/-- Bounded terminal payoffs are another sufficient local theorem premise;
no bound is stored in the protocol or information model. -/
theorem exists_isSubgamePerfect_of_bounded_terminal [DecidableEq ι]
    [∀ player, DecidableEq (M.InfoState player)]
    (singleMover : ∀ (state : E.State) {first second : ι},
      E.active state first → E.active state second → first = second)
    (fallback : Profile M.strategicSignature)
    (finiteChoices : M.HasFiniteDecisionChoices)
    (certificate : E.WellFoundedPlay)
    (hperfect : M.SeparatesDecisionHistories)
    (utility : E.History → ι → ℝ)
    (hbounded : ∀ who, ∃ C : ℝ,
      ∀ final, E.terminal final.state → |utility final who| ≤ C) :
    ∃ profile : Profile M.strategicSignature,
      M.IsSubgamePerfect certificate profile utility := by
  apply M.exists_isSubgamePerfect singleMover fallback finiteChoices
    certificate hperfect utility
  intro chooser history who
  obtain ⟨C, hC⟩ := hbounded who
  exact E.payoffIntegrable_historyBackwardLaw_of_bounded_terminal
    (chooser := chooser) (C := C) (hC) history

end InformationModel

end GameTheory.Protocol
