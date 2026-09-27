/-
# Well-founded randomized terminal histories

The canonical randomized chooser draws a legal joint action at each history.
Well-founded recursion follows its realized transitions to a terminal history.
-/

import GameTheory.Protocol.Backward
import GameTheory.Protocol.Randomized

noncomputable section

namespace GameTheory.Protocol

open GameTheory.Math.Probability

universe uι

variable {ι : Type uι} {E : ExecutionProtocol ι}

namespace ExecutionProtocol

variable (E)

/-- History extension inherits the successor order of its reached state. -/
def HistorySuccessor (later earlier : E.History) : Prop :=
  E.Successor later.state earlier.state

/-- A well-founded state protocol is also well-founded on complete histories. -/
theorem wellFounded_historySuccessor
    (certificate : E.WellFoundedPlay) :
    WellFounded E.HistorySuccessor :=
  certificate.onFun

/-- Well-founded recursion whose argument retains the complete history. -/
def historyBackwardRec {motive : E.History → Sort*}
    (certificate : E.WellFoundedPlay)
    (rule : ∀ history : E.History,
      (∀ later : E.History,
        E.HistorySuccessor later history → motive later) →
      motive history)
    (history : E.History) : motive history :=
  WellFounded.fix (E.wellFounded_historySuccessor certificate) rule history

/-- The unfolding equation for history-indexed backward recursion. -/
theorem historyBackwardRec_eq {motive : E.History → Sort*}
    (certificate : E.WellFoundedPlay)
    (rule : ∀ history : E.History,
      (∀ later : E.History,
        E.HistorySuccessor later history → motive later) →
      motive history)
    (history : E.History) :
    E.historyBackwardRec certificate rule history =
      rule history fun later _relation =>
        E.historyBackwardRec certificate rule later :=
  WellFounded.fix_eq
    (E.wellFounded_historySuccessor certificate) rule history

open Classical in
/-- The terminal-history law of a randomized history chooser. -/
def randomizedBackwardLaw (certificate : E.WellFoundedPlay)
    (chooser : E.RandomizedChooser) : E.History → PMF E.History :=
  E.historyBackwardRec certificate fun history recurse =>
    if hterm : E.terminal history.state then PMF.pure history
    else
      (chooser history hterm).bind fun drawn =>
        (E.step history.state drawn).bindOnSupport fun _target realized =>
          recurse (history.extend drawn.2 realized)
            ⟨drawn.1, drawn.2, realized⟩

open Classical in
theorem randomizedBackwardLaw_eq (certificate : E.WellFoundedPlay)
    (chooser : E.RandomizedChooser) (history : E.History) :
    E.randomizedBackwardLaw certificate chooser history =
      if hterm : E.terminal history.state then PMF.pure history
      else
        (chooser history hterm).bind fun drawn =>
          (E.step history.state drawn).bindOnSupport fun _target realized =>
            E.randomizedBackwardLaw certificate chooser
              (history.extend drawn.2 realized) := by
  rw [randomizedBackwardLaw, historyBackwardRec_eq]

theorem randomizedBackwardLaw_of_terminal
    {certificate : E.WellFoundedPlay} {chooser : E.RandomizedChooser}
    {history : E.History} (hterm : E.terminal history.state) :
    E.randomizedBackwardLaw certificate chooser history = PMF.pure history := by
  rw [randomizedBackwardLaw_eq, dite_eq_left hterm]

theorem randomizedBackwardLaw_of_not_terminal
    {certificate : E.WellFoundedPlay} {chooser : E.RandomizedChooser}
    {history : E.History} (hterm : ¬ E.terminal history.state) :
    E.randomizedBackwardLaw certificate chooser history =
      (chooser history hterm).bind fun drawn =>
        (E.step history.state drawn).bindOnSupport fun _target realized =>
          E.randomizedBackwardLaw certificate chooser
            (history.extend drawn.2 realized) := by
  rw [randomizedBackwardLaw_eq, dite_eq_right hterm]

/-- Every outcome of the well-founded randomized law has terminated. -/
theorem randomizedBackwardLaw_support_terminal
    {certificate : E.WellFoundedPlay} {chooser : E.RandomizedChooser}
    (history : E.History) :
    ∀ final ∈ (E.randomizedBackwardLaw certificate chooser history).support,
      E.terminal final.state := by
  induction history using
      (E.wellFounded_historySuccessor certificate).induction with
  | _ current ih =>
      intro final hfinal
      by_cases hterm : E.terminal current.state
      · rw [E.randomizedBackwardLaw_of_terminal hterm,
          PMF.mem_support_pure_iff] at hfinal
        subst final
        exact hterm
      · rw [E.randomizedBackwardLaw_of_not_terminal hterm,
          PMF.support_bind] at hfinal
        obtain ⟨drawn, _, hcontinue⟩ := Set.mem_iUnion₂.mp hfinal
        rw [PMF.mem_support_bindOnSupport_iff] at hcontinue
        obtain ⟨target, realized, hchild⟩ := hcontinue
        exact ih (current.extend drawn.2 realized)
          ⟨drawn.1, drawn.2, realized⟩ final hchild

/-- The terminal law equals a forward randomized run once that run has stopped. -/
theorem randomizedBackwardLaw_eq_runRandomizedFor
    {certificate : E.WellFoundedPlay} {chooser : E.RandomizedChooser}
    {horizon : ℕ} {history : E.History}
    (hstop : ∀ final ∈ (E.runRandomizedFor chooser horizon history).support,
      E.terminal final.state) :
    E.randomizedBackwardLaw certificate chooser history =
      E.runRandomizedFor chooser horizon history := by
  induction horizon generalizing history with
  | zero =>
      have hterm : E.terminal history.state :=
        hstop history (by simp)
      rw [E.randomizedBackwardLaw_of_terminal hterm,
        E.runRandomizedFor_zero]
  | succ horizon ih =>
      by_cases hterm : E.terminal history.state
      · rw [E.randomizedBackwardLaw_of_terminal hterm,
          E.runRandomizedFor_of_terminal _ _ hterm]
      · rw [E.randomizedBackwardLaw_of_not_terminal hterm,
          E.runRandomizedFor_succ_of_not_terminal chooser horizon hterm]
        apply bind_congr_on_support
        intro drawn hdraw
        apply bindOnSupport_congr
        intro target realized
        apply ih
        intro final hfinal
        apply hstop final
        rw [E.runRandomizedFor_succ_of_not_terminal chooser horizon hterm,
          PMF.support_bind]
        apply Set.mem_iUnion₂.mpr
        refine ⟨drawn, hdraw, ?_⟩
        rw [PMF.support_bindOnSupport]
        exact Set.mem_iUnion₂.mpr ⟨target, realized, hfinal⟩

/-- A global history horizon identifies the terminal law with the bounded runner. -/
theorem randomizedBackwardLaw_eq_runRandomizedFor_of_bound
    {certificate : E.WellFoundedPlay} {bound : ℕ}
    (bounded : E.BoundedHorizon bound) (chooser : E.RandomizedChooser)
    (history : E.History) :
    E.randomizedBackwardLaw certificate chooser history =
      E.runRandomizedFor chooser bound history := by
  apply E.randomizedBackwardLaw_eq_runRandomizedFor
  intro final hfinal
  rcases E.runRandomizedFor_terminal_or_length chooser bound history final hfinal with
    stopped | consumed
  · exact stopped
  · exact bounded final.state final.trace (by omega)

/-- A terminal payoff bound integrates under every randomized terminal law. -/
theorem payoffIntegrable_randomizedBackwardLaw_of_bounded_terminal
    {certificate : E.WellFoundedPlay} {chooser : E.RandomizedChooser}
    {payoff : E.History → ℝ} {C : ℝ}
    (hbound : ∀ final, E.terminal final.state → |payoff final| ≤ C)
    (history : E.History) :
    PayoffIntegrable (E.randomizedBackwardLaw certificate chooser history) payoff := by
  apply payoffIntegrable_of_bounded_on_support
  intro final hfinal
  exact hbound final (E.randomizedBackwardLaw_support_terminal history final hfinal)

end ExecutionProtocol

end GameTheory.Protocol
