/-
# Composing history choosers on child cones

The realized children of one legal step have disjoint continuation cones.
This permits a current joint action to be combined with independently chosen
continuation choosers, without imposing a common finite history carrier.
-/

import GameTheory.Protocol.SubgamePerfect

noncomputable section

namespace GameTheory.Protocol

open GameTheory.Math.Probability

universe uι

variable {ι : Type uι} {E : ExecutionProtocol ι}

namespace ExecutionProtocol

variable (E)

/-- A complete history lies in the cone of one realized child of `history`. -/
def HasChildCone (history : E.History)
    (chosen : {joint : ∀ i, Option (E.Action i) //
      E.Legal history.state joint}) (later : E.History) : Prop :=
  ∃ target, ∃ realized : target ∈ (E.step history.state chosen).support,
    E.HistoryReaches (history.extend chosen.2 realized) later

/-- Two child cones of the same selected joint action cannot overlap unless
their realized successor states coincide. -/
theorem childCone_target_unique
    {history : E.History}
    {chosen : {joint : ∀ i, Option (E.Action i) //
      E.Legal history.state joint}}
    {first second : E.State}
    (hfirst : first ∈ (E.step history.state chosen).support)
    (hsecond : second ∈ (E.step history.state chosen).support)
    {later : E.History}
    (reachFirst : E.HistoryReaches
      (history.extend chosen.2 hfirst) later)
    (reachSecond : E.HistoryReaches
      (history.extend chosen.2 hsecond) later) :
    first = second := by
  obtain ⟨firstFuel, firstReach⟩ := reachFirst
  obtain ⟨secondFuel, secondReach⟩ := reachSecond
  have hlength : (history.extend chosen.2 hfirst).trace.length =
      (history.extend chosen.2 hsecond).trace.length := by
    simp only [History.extend, Trace.length]
  have heq := firstReach.eq_start_of_same_length secondReach hlength
  exact congrArg History.state heq

/-- Combine a selected parent action with independently supplied choosers on
the realized child cones. A fallback makes the chooser total off those cones. -/
def graftHistoryChooser (fallback : E.HistoryChooser)
    (history : E.History)
    (chosen : {joint : ∀ i, Option (E.Action i) //
      E.Legal history.state joint})
    (continuation : ∀ target,
      target ∈ (E.step history.state chosen).support → E.HistoryChooser) :
    E.HistoryChooser := fun later hterm => by
  classical
  by_cases hhere : later = history
  · subst later
    exact chosen
  · by_cases hcone : E.HasChildCone history chosen later
    · let target := Classical.choose hcone
      let witness := Classical.choose_spec hcone
      exact continuation target witness.1 later hterm
    · exact fallback later hterm

theorem graftHistoryChooser_at_parent
    (fallback : E.HistoryChooser)
    (history : E.History)
    (chosen : {joint : ∀ i, Option (E.Action i) //
      E.Legal history.state joint})
    (continuation : ∀ target,
      target ∈ (E.step history.state chosen).support → E.HistoryChooser)
    (hterm : ¬ E.terminal history.state) :
    E.graftHistoryChooser fallback history chosen continuation history hterm =
      chosen := by
  simp [graftHistoryChooser]

/-- Within a selected child cone, the graft uses that child's chooser. -/
theorem graftHistoryChooser_on_child_cone
    (fallback : E.HistoryChooser)
    (history : E.History)
    (chosen : {joint : ∀ i, Option (E.Action i) //
      E.Legal history.state joint})
    (continuation : ∀ target,
      target ∈ (E.step history.state chosen).support → E.HistoryChooser)
    (target : E.State)
    (realized : target ∈ (E.step history.state chosen).support)
    (later : E.History)
    (hreach : E.HistoryReaches
      (history.extend chosen.2 realized) later)
    (hterm : ¬ E.terminal later.state) :
    E.graftHistoryChooser fallback history chosen continuation later hterm =
      continuation target realized later hterm := by
  classical
  have hneq : later ≠ history := by
    obtain ⟨fuel, hwithin⟩ := hreach
    have hlength := hwithin.trace_length_le
    simp only [History.extend, Trace.length] at hlength
    intro heq
    subst later
    omega
  have hcone : E.HasChildCone history chosen later :=
    ⟨target, realized, hreach⟩
  simp only [graftHistoryChooser, dite_eq_right hneq, dite_eq_left hcone]
  let selected := Classical.choose hcone
  let selectedProof := (Classical.choose_spec hcone).1
  have hselected : selected = target :=
    E.childCone_target_unique selectedProof realized
      (Classical.choose_spec hcone).2 hreach
  dsimp only [selected] at hselected
  simp only [hselected]

/-- The graft's terminal law is the selected transition law followed by each
child's own terminal law. This is the realization equation used by guarded
backward induction. -/
theorem historyBackwardLaw_graft
    (certificate : E.WellFoundedPlay)
    (fallback : E.HistoryChooser)
    (history : E.History)
    (hterm : ¬ E.terminal history.state)
    (chosen : {joint : ∀ i, Option (E.Action i) //
      E.Legal history.state joint})
    (continuation : ∀ target,
      target ∈ (E.step history.state chosen).support → E.HistoryChooser) :
    E.historyBackwardLaw certificate
      (E.graftHistoryChooser fallback history chosen continuation) history =
      (E.step history.state chosen).bindOnSupport fun target realized =>
        E.historyBackwardLaw certificate (continuation target realized)
          (history.extend chosen.2 realized) := by
  rw [E.historyBackwardLaw_of_not_terminal hterm,
    E.graftHistoryChooser_at_parent fallback history chosen continuation hterm]
  apply bindOnSupport_congr
  intro target realized
  apply E.historyBackwardLaw_congr_of_reaches
  intro later hreach hnotTerminal
  exact E.graftHistoryChooser_on_child_cone fallback history chosen
    continuation target realized later hreach hnotTerminal

end ExecutionProtocol

end GameTheory.Protocol
