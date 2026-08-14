/-
# EXP-095: history-dependent sequential client adequacy

The execution and perfect-recall EFG are existing hostile fixtures.  This file
adds only a theorem author's contingent plans and payoff: match the remembered
first vote on the second move.  It tests whether canonical history values and
the historywise/SPE surface suffice without a second evaluator.
-/

import GameTheory.Tests.EFGSubgamePerfect

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.SequentialClientAdequacy

open GameTheory Languages Protocol Probability
open Protocol.ExecutionProtocol
open GameTheory.Tests.Randomized
open GameTheory.Tests.EFGKuhn
open GameTheory.Tests.EFGSubgamePerfect

/-! ## Client plans and terminal utility -/

/-- Start with `up`; thereafter match the first vote remembered by the
perfect-recall information state. -/
def matchingPolicy : recallModel.Policy ()
  | .fresh => ⟨some .up, by simp [recallMenuAt]⟩
  | .one first => ⟨some first, by cases first <;> simp [recallMenuAt]⟩
  | .both first second => ⟨none, by simp [recallMenuAt]⟩

/-- The negative-control plan starts `up` and then deliberately chooses
`down`, producing a mismatch on its realized path. -/
def mismatchingPolicy : recallModel.Policy ()
  | .fresh => ⟨some .up, by simp [recallMenuAt]⟩
  | .one _ => ⟨some .down, by simp [recallMenuAt]⟩
  | .both first second => ⟨none, by simp [recallMenuAt]⟩

def matchingProfile : Profile recallGame.strategicSignature :=
  fun _ => matchingPolicy

def mismatchingProfile : Profile recallGame.strategicSignature :=
  fun _ => mismatchingPolicy

/-- Only terminal histories matter; matching the two remembered votes pays
one and a mismatch pays zero. -/
def matchUtility (history : recallGame.History) (_who : Unit) : ℝ :=
  match history.state with
  | .done first second => if first = second then 1 else 0
  | _ => 0

theorem matchingPolicy_is_history_dependent :
    matchingPolicy.act (.one .up) ≠ matchingPolicy.act (.one .down) := by
  decide

/-! ## A reusable terminal-payoff bound -/

/-- Backward value cannot exceed a bound that holds at every terminal history.
The proof uses the canonical history recursion and finite-law monotonicity. -/
theorem historyBackwardValue_le_of_terminal_le
    {E : ExecutionProtocol Unit} {certificate : E.WellFoundedPlay}
    {chooser : E.HistoryChooser} {payoff : E.History → ℝ} {bound : ℝ}
    (hbound : ∀ history, E.terminal history.state → payoff history ≤ bound) :
    ∀ history,
      E.historyBackwardValue certificate chooser payoff history ≤ bound := by
  intro history
  induction history using
      (E.wellFounded_historySuccessor certificate).induction with
  | _ current ih =>
      by_cases hterm : E.terminal current.state
      · rw [E.historyBackwardValue_of_terminal hterm]
        exact hbound current hterm
      · rw [E.historyBackwardValue_of_not_terminal hterm]
        let chosen := chooser current hterm
        show E.historyStepValue current chosen
            (fun _target realized =>
              E.historyBackwardValue certificate chooser payoff
                (current.extend chosen.2 realized)) ≤ bound
        calc
          E.historyStepValue current chosen
              (fun _target realized =>
                E.historyBackwardValue certificate chooser payoff
                  (current.extend chosen.2 realized)) ≤
              E.historyStepValue current chosen (fun _ _ => bound) := by
            apply E.historyStepValue_mono
            intro target realized
            exact ih (current.extend chosen.2 realized)
              ⟨chosen.1, chosen.2, realized⟩
          _ = bound := by
            unfold ExecutionProtocol.historyStepValue
            rw [FinDist.bindOnSupport_eq_bind_of_eq_on_support
                (g := fun _ => FinDist.pure bound) (by intro _ _; rfl),
              FinDist.bind_const, FinDist.expect_pure]
            rfl

/-! ## Exact incumbent continuation values -/

abbrev matchingChooser : twice.HistoryChooser :=
  recallModel.historyChooser matchingProfile

abbrev mismatchingChooser : twice.HistoryChooser :=
  recallModel.historyChooser mismatchingProfile

def matchingValue (history : twice.History) : ℝ :=
  twice.historyBackwardValue twice_wellFoundedPlay matchingChooser
    (fun outcome => matchUtility outcome ()) history

def mismatchingValue (history : twice.History) : ℝ :=
  twice.historyBackwardValue twice_wellFoundedPlay mismatchingChooser
    (fun outcome => matchUtility outcome ()) history

theorem matching_step_start (trace : twice.Trace .start)
    (hterm : ¬ twice.terminal (.start : Round)) :
    twice.step .start
        (matchingChooser (⟨.start, trace⟩ : twice.History) hterm) =
      FinDist.pure (.after .up) := by
  have hchoice :
      (matchingChooser (⟨.start, trace⟩ : twice.History) hterm).1 () =
        some .up := by
    simp only [matchingChooser, InformationModel.historyChooser,
      InformationModel.jointAt, matchingProfile, InformationModel.Policy.act]
    rw [show recallModel.infoOf () trace = Memory.fresh from
      recallInfoOf_eq_memory trace]
    rfl
  show (match (matchingChooser (⟨.start, trace⟩ : twice.History) hterm).1 () with
    | some vote => FinDist.pure (Round.after vote)
    | none => FinDist.pure (Round.after .up)) = FinDist.pure (Round.after .up)
  rw [hchoice]

theorem matching_step_after (first : Vote) (trace : twice.Trace (Round.after first))
    (hterm : ¬ twice.terminal (Round.after first)) :
    twice.step (Round.after first)
        (matchingChooser (⟨Round.after first, trace⟩ : twice.History) hterm) =
      FinDist.pure (Round.done first first) := by
  have hchoice :
      (matchingChooser (⟨Round.after first, trace⟩ : twice.History) hterm).1 () =
        some first := by
    simp only [matchingChooser, InformationModel.historyChooser,
      InformationModel.jointAt, matchingProfile, InformationModel.Policy.act]
    rw [show recallModel.infoOf () trace = Memory.one first from
      recallInfoOf_eq_memory trace]
    rfl
  show (match
      (matchingChooser (⟨Round.after first, trace⟩ : twice.History) hterm).1 () with
    | some vote => FinDist.pure (Round.done first vote)
    | none => FinDist.pure (Round.done first .up)) = FinDist.pure (Round.done first first)
  rw [hchoice]

theorem mismatching_step_after_up (trace : twice.Trace (Round.after .up))
    (hterm : ¬ twice.terminal (Round.after .up)) :
    twice.step (Round.after .up)
        (mismatchingChooser (⟨Round.after .up, trace⟩ : twice.History) hterm) =
      FinDist.pure (Round.done .up .down) := by
  have hchoice :
      (mismatchingChooser (⟨Round.after .up, trace⟩ : twice.History) hterm).1 () =
        some .down := by
    simp only [mismatchingChooser, InformationModel.historyChooser,
      InformationModel.jointAt, mismatchingProfile, InformationModel.Policy.act]
    rw [show recallModel.infoOf () trace = Memory.one .up from
      recallInfoOf_eq_memory trace]
    rfl
  show (match
      (mismatchingChooser (⟨Round.after .up, trace⟩ : twice.History) hterm).1 () with
    | some vote => FinDist.pure (Round.done .up vote)
    | none => FinDist.pure (Round.done .up .up)) = FinDist.pure (Round.done .up .down)
  rw [hchoice]

theorem matchingValue_after (first : Vote) (trace : twice.Trace (Round.after first)) :
    matchingValue (⟨Round.after first, trace⟩ : twice.History) = 1 := by
  have hterm : ¬ twice.terminal (Round.after first) := by
    simp [Round.stopped]
  rw [matchingValue, twice.historyBackwardValue_of_not_terminal hterm]
  dsimp only
  let chosen := matchingChooser (⟨Round.after first, trace⟩ : twice.History) hterm
  have hstep : twice.step (Round.after first) chosen =
      FinDist.pure (Round.done first first) :=
    matching_step_after first trace hterm
  rw [twice.historyStepValue_of_step_eq_pure hstep _,
    twice.historyBackwardValue_of_terminal (by simp [Round.stopped])]
  simp [matchUtility]

theorem matchingValue_start (trace : twice.Trace .start) :
    matchingValue (⟨.start, trace⟩ : twice.History) = 1 := by
  have hterm : ¬ twice.terminal (.start : Round) := by
    simp [Round.stopped]
  rw [matchingValue, twice.historyBackwardValue_of_not_terminal hterm]
  dsimp only
  let chosen := matchingChooser (⟨.start, trace⟩ : twice.History) hterm
  have hstep : twice.step .start chosen = FinDist.pure (Round.after .up) :=
    matching_step_start trace hterm
  rw [twice.historyStepValue_of_step_eq_pure hstep _]
  exact matchingValue_after .up _

theorem mismatchingValue_after_up (trace : twice.Trace (Round.after .up)) :
    mismatchingValue (⟨Round.after .up, trace⟩ : twice.History) = 0 := by
  have hterm : ¬ twice.terminal (Round.after .up) := by
    simp [Round.stopped]
  rw [mismatchingValue, twice.historyBackwardValue_of_not_terminal hterm]
  dsimp only
  let chosen := mismatchingChooser (⟨Round.after .up, trace⟩ : twice.History) hterm
  have hstep : twice.step (Round.after .up) chosen =
      FinDist.pure (Round.done .up .down) :=
    mismatching_step_after_up trace hterm
  rw [twice.historyStepValue_of_step_eq_pure hstep _,
    twice.historyBackwardValue_of_terminal (by simp [Round.stopped])]
  simp [matchUtility]

theorem matchingValue_of_not_terminal (history : twice.History)
    (hterm : ¬ twice.terminal history.state) :
    matchingValue history = 1 := by
  rcases history with ⟨state, trace⟩
  cases state with
  | start => exact matchingValue_start trace
  | after first => exact matchingValue_after first trace
  | done first second => exact False.elim (hterm (by simp [Round.stopped]))

theorem everyValue_le_one (chooser : twice.HistoryChooser) (history : twice.History) :
    twice.historyBackwardValue twice_wellFoundedPlay chooser
        (fun outcome => matchUtility outcome ()) history ≤ 1 := by
  apply historyBackwardValue_le_of_terminal_le
  rintro ⟨state, trace⟩ _
  cases state with
  | start => norm_num [matchUtility]
  | after first => norm_num [matchUtility]
  | done first second =>
      by_cases hmatch : first = second <;> simp [matchUtility, hmatch]

/-! ## Canonical historywise optimality and subgame perfection -/

theorem matching_isHistorywiseOptimal :
    recallGame.IsHistorywiseOptimal twice_wellFoundedPlay matchingProfile matchUtility := by
  intro who alternative history
  rcases who with ⟨⟩
  by_cases hterm : twice.terminal history.state
  · rw [twice.historyBackwardValue_of_terminal hterm,
      twice.historyBackwardValue_of_terminal hterm]
  · calc
      twice.historyBackwardValue twice_wellFoundedPlay
          (recallModel.historyChooser
            (Profile.update matchingProfile () alternative))
          (fun outcome => matchUtility outcome ()) history ≤ 1 :=
        everyValue_le_one _ history
      _ = twice.historyBackwardValue twice_wellFoundedPlay matchingChooser
          (fun outcome => matchUtility outcome ()) history := by
        symm
        exact matchingValue_of_not_terminal history hterm

theorem matching_isSubgamePerfect :
    recallGame.IsSubgamePerfect twice_wellFoundedPlay matchingProfile matchUtility :=
  matching_isHistorywiseOptimal.isSubgamePerfect

/-! ## Falsifying control -/

def afterUpHistory : twice.History := ⟨.after .up, votedOnce⟩

theorem update_unit_eq_profile (profile : Profile recallGame.strategicSignature)
    (alternative : recallModel.Policy ()) :
    Profile.update profile () alternative = (fun _ => alternative) := by
  funext who
  rcases who with ⟨⟩
  exact Profile.update_same profile () alternative

/-- Replacing the mismatching plan by the matching plan after the first `up`
raises continuation value from zero to one. -/
theorem mismatching_not_isHistorywiseOptimal :
    ¬ recallGame.IsHistorywiseOptimal
      twice_wellFoundedPlay mismatchingProfile matchUtility := by
  intro hoptimal
  have hcomparison := hoptimal () matchingPolicy afterUpHistory
  rw [update_unit_eq_profile, show (fun _ => matchingPolicy) = matchingProfile from rfl]
    at hcomparison
  have hcomparison' : matchingValue afterUpHistory ≤ mismatchingValue afterUpHistory := by
    simpa [matchingValue, mismatchingValue, matchingChooser, mismatchingChooser]
      using hcomparison
  have hmatching : matchingValue afterUpHistory = 1 :=
    matchingValue_after .up votedOnce
  have hmismatching : mismatchingValue afterUpHistory = 0 :=
    mismatchingValue_after_up votedOnce
  rw [hmatching, hmismatching] at hcomparison'
  norm_num at hcomparison'

end GameTheory.Experimental.PostArchitecture.SequentialClientAdequacy
