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

open GameTheory Languages Protocol GameTheory.Math.Probability
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

/-- A guarded terminal-law value cannot exceed a bound on terminal outcomes. -/
theorem historyBackwardValue_le_of_terminal_le
    {E : ExecutionProtocol Unit} {certificate : E.WellFoundedPlay}
    {chooser : E.HistoryChooser} {payoff : E.History → ℝ} {bound : ℝ}
    (hbound : ∀ history, E.terminal history.state → payoff history ≤ bound)
    (history : E.History)
    (hintegrable : PayoffIntegrable
      (E.historyBackwardLaw certificate chooser history) payoff) :
    E.historyBackwardValue certificate chooser payoff history hintegrable ≤
      bound := by
  unfold ExecutionProtocol.historyBackwardValue
  calc
    expect (E.historyBackwardLaw certificate chooser history) payoff
        hintegrable ≤
      expect (E.historyBackwardLaw certificate chooser history)
        (fun _ => bound)
        (payoffIntegrable_constant _ bound) := by
      apply expect_mono
      intro final hfinal
      exact hbound final
        (E.historyBackwardLaw_support_terminal history final hfinal)
    _ = bound := expect_constant _ bound _

/-! ## Exact incumbent continuation values -/

abbrev matchingChooser : twice.HistoryChooser :=
  recallModel.historyChooser matchingProfile

abbrev mismatchingChooser : twice.HistoryChooser :=
  recallModel.historyChooser mismatchingProfile

private theorem matchUtility_terminal_bound
    (history : twice.History) (hterm : twice.terminal history.state) :
    |matchUtility history ()| ≤ 1 := by
  rcases history with ⟨state, trace⟩
  cases state with
  | start => simp [matchUtility]
  | after first => simp [matchUtility]
  | done first second =>
      by_cases hmatch : first = second <;> simp [matchUtility, hmatch]

/-- The bounded terminal matching payoff integrates every backward history law. -/
theorem matchIntegrable (chooser : twice.HistoryChooser)
    (history : twice.History) :
    PayoffIntegrable (twice.historyBackwardLaw twice_wellFoundedPlay
      chooser history) (fun outcome => matchUtility outcome ()) :=
  twice.payoffIntegrable_historyBackwardLaw_of_bounded_terminal
    (C := 1) matchUtility_terminal_bound history

def matchingValue (history : twice.History) : ℝ :=
  twice.historyBackwardValue twice_wellFoundedPlay matchingChooser
    (fun outcome => matchUtility outcome ()) history
    (matchIntegrable matchingChooser history)

def mismatchingValue (history : twice.History) : ℝ :=
  twice.historyBackwardValue twice_wellFoundedPlay mismatchingChooser
    (fun outcome => matchUtility outcome ()) history
    (matchIntegrable mismatchingChooser history)

theorem matching_step_start (trace : twice.Trace .start)
    (hterm : ¬ twice.terminal (.start : Round)) :
    twice.step .start
        (matchingChooser (⟨.start, trace⟩ : twice.History) hterm) =
      PMF.pure (.after .up) := by
  have hchoice :
      (matchingChooser (⟨.start, trace⟩ : twice.History) hterm).1 () =
        some .up := by
    simp only [matchingChooser, InformationModel.historyChooser,
      InformationModel.jointAt, matchingProfile, InformationModel.Policy.act]
    rw [show recallModel.infoOf () trace = Memory.fresh from
      recallInfoOf_eq_memory trace]
    rfl
  show (match (matchingChooser (⟨.start, trace⟩ : twice.History) hterm).1 () with
    | some vote => PMF.pure (Round.after vote)
    | none => PMF.pure (Round.after .up)) = PMF.pure (Round.after .up)
  rw [hchoice]

theorem matching_step_after (first : Vote) (trace : twice.Trace (Round.after first))
    (hterm : ¬ twice.terminal (Round.after first)) :
    twice.step (Round.after first)
        (matchingChooser (⟨Round.after first, trace⟩ : twice.History) hterm) =
      PMF.pure (Round.done first first) := by
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
    | some vote => PMF.pure (Round.done first vote)
    | none => PMF.pure (Round.done first .up)) = PMF.pure (Round.done first first)
  rw [hchoice]

theorem mismatching_step_after_up (trace : twice.Trace (Round.after .up))
    (hterm : ¬ twice.terminal (Round.after .up)) :
    twice.step (Round.after .up)
        (mismatchingChooser (⟨Round.after .up, trace⟩ : twice.History) hterm) =
      PMF.pure (Round.done .up .down) := by
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
    | some vote => PMF.pure (Round.done .up vote)
    | none => PMF.pure (Round.done .up .up)) = PMF.pure (Round.done .up .down)
  rw [hchoice]

private theorem value_of_constant_successors (chooser : twice.HistoryChooser)
    (history : twice.History) (hterm : ¬ twice.terminal history.state)
    (c : ℝ)
    (hchild : ∀ target
      (realized : target ∈ (twice.step history.state
        (chooser history hterm)).support)
      (hguard : PayoffIntegrable
        (twice.historyBackwardLaw twice_wellFoundedPlay chooser
          (history.extend (chooser history hterm).2 realized))
        (fun outcome => matchUtility outcome ())),
      twice.historyBackwardValue twice_wellFoundedPlay chooser
        (fun outcome => matchUtility outcome ())
        (history.extend (chooser history hterm).2 realized) hguard = c) :
    twice.historyBackwardValue twice_wellFoundedPlay chooser
      (fun outcome => matchUtility outcome ()) history
      (matchIntegrable chooser history) = c := by
  obtain ⟨houter, heq⟩ := twice.historyBackwardValue_of_not_terminal
    hterm (matchIntegrable chooser history) (fun _ => c)
      (by intro target realized hguard
          exact (hchild target realized hguard).symm)
  simpa only [expect_constant] using heq

theorem matchingValue_after (first : Vote) (trace : twice.Trace (Round.after first)) :
    matchingValue (⟨Round.after first, trace⟩ : twice.History) = 1 := by
  have hterm : ¬ twice.terminal (Round.after first) := by
    simp [Round.stopped]
  unfold matchingValue
  apply value_of_constant_successors matchingChooser _ hterm 1
  intro target realized hguard
  have hstep := matching_step_after first trace hterm
  rw [hstep, PMF.mem_support_pure_iff] at realized
  subst target
  rw [twice.historyBackwardValue_of_terminal
    (by simp [Round.stopped]) hguard]
  simp [matchUtility]

theorem matchingValue_start (trace : twice.Trace .start) :
    matchingValue (⟨.start, trace⟩ : twice.History) = 1 := by
  have hterm : ¬ twice.terminal (.start : Round) := by
    simp [Round.stopped]
  unfold matchingValue
  apply value_of_constant_successors matchingChooser _ hterm 1
  intro target realized hguard
  have hstep := matching_step_start trace hterm
  rw [hstep, PMF.mem_support_pure_iff] at realized
  subst target
  simpa only [matchingValue, ExecutionProtocol.History.extend] using
    matchingValue_after .up _

theorem mismatchingValue_after_up (trace : twice.Trace (Round.after .up)) :
    mismatchingValue (⟨Round.after .up, trace⟩ : twice.History) = 0 := by
  have hterm : ¬ twice.terminal (Round.after .up) := by
    simp [Round.stopped]
  unfold mismatchingValue
  apply value_of_constant_successors mismatchingChooser _ hterm 0
  intro target realized hguard
  have hstep := mismatching_step_after_up trace hterm
  rw [hstep, PMF.mem_support_pure_iff] at realized
  subst target
  rw [twice.historyBackwardValue_of_terminal
    (by simp [Round.stopped]) hguard]
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
        (fun outcome => matchUtility outcome ()) history
        (matchIntegrable chooser history) ≤ 1 := by
  apply historyBackwardValue_le_of_terminal_le (history := history)
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
  refine ⟨matchIntegrable
      (recallModel.historyChooser (Profile.update matchingProfile () alternative))
      history, matchIntegrable matchingChooser history, ?_⟩
  by_cases hterm : twice.terminal history.state
  · rw [twice.historyBackwardValue_of_terminal hterm,
      twice.historyBackwardValue_of_terminal hterm]
  · calc
      twice.historyBackwardValue twice_wellFoundedPlay
          (recallModel.historyChooser
            (Profile.update matchingProfile () alternative))
          (fun outcome => matchUtility outcome ()) history
          (matchIntegrable _ history) ≤ 1 :=
        everyValue_le_one _ history
      _ = twice.historyBackwardValue twice_wellFoundedPlay matchingChooser
          (fun outcome => matchUtility outcome ()) history
          (matchIntegrable matchingChooser history) := by
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
  obtain ⟨hother, hinc, hcomparison⟩ := hcomparison
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
