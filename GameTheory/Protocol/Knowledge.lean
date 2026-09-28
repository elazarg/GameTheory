/-
# Protocol information as knowledge of histories

A player's information state is computed from the history, so it partitions
complete histories. Epistemic knowledge on that partition — the event holds
throughout the current cell — is exactly truth at every history compatible
with the player's information state. No premise on execution states is
needed: two histories reaching one state may leave a player differently
informed, so this knowledge concerns histories, never states.

Perfect recall says precisely that each player always knows its own past
play. Knowledge constrains every belief on an information set, not only
Bayes-consistent ones: a belief is a law on the compatible histories, and each
of them satisfies every known event.

This leaf is not re-exported by the Protocol root, whose dependency closure
stays independent of the epistemic layer.
-/

import GameTheory.Protocol.BehavioralAssessment
import GameTheory.Epistemic.Knowledge

namespace GameTheory.Protocol

open GameTheory.Epistemic

variable {ι : Type*} {E : ExecutionProtocol ι}

namespace InfoSignals

variable (S : InfoSignals E)

/-- Histories leaving player `i` in the same information state. -/
def historyPartition (i : ι) : Setoid E.History :=
  Setoid.ker fun history => S.infoOf i history.trace

theorem mem_cell_historyPartition_iff (i : ι) (history other : E.History) :
    other ∈ cell (S.historyPartition i) history ↔
      S.infoOf i history.trace = S.infoOf i other.trace :=
  Iff.rfl

/-- Knowledge at a history is truth at every history with the same information
state. -/
theorem mem_knows_historyPartition_iff (i : ι) (history : E.History)
    (event : Set E.History) :
    history ∈ Knows (S.historyPartition i) event ↔
      ∀ other : E.History, S.infoOf i other.trace = S.infoOf i history.trace →
        other ∈ event := by
  rw [mem_Knows_iff]
  exact ⟨fun hknown other hsame => hknown hsame.symm,
    fun hknown other hsame => hknown other hsame.symm⟩

/-- The set of histories at which player `i` has made exactly the moves it made
at `history`. -/
def samePlay (i : ι) (history : E.History) : Set E.History :=
  {other | S.ownPlay i other.trace = S.ownPlay i history.trace}

/-- **Perfect recall is knowledge of one's own play.** -/
theorem perfectRecall_iff_knows_ownPlay :
    S.PerfectRecall ↔
      ∀ (i : ι) (history : E.History),
        history ∈ Knows (S.historyPartition i) (S.samePlay i history) := by
  constructor
  · intro hrecall i history
    rw [mem_knows_historyPartition_iff]
    intro other hsame
    exact hrecall i other.trace history.trace hsame
  · intro hknown i first second traceFirst traceSecond hsame
    exact (S.mem_knows_historyPartition_iff i ⟨second, traceSecond⟩ _).1
      (hknown i ⟨second, traceSecond⟩) ⟨first, traceFirst⟩ hsame

end InfoSignals

namespace InformationModel

variable {M : InformationModel E}

/-- A known event contains every history of the information set. -/
theorem mem_of_knows {i : ι} {info : M.InfoState i}
    (history : M.InformationHistory i info) {event : Set E.History}
    (hknown : history.1 ∈ Knows (M.historyPartition i) event)
    (other : M.InformationHistory i info) : other.1 ∈ event :=
  (M.mem_knows_historyPartition_iff i history.1 event).1 hknown other.1
    (other.2.trans history.2.symm)

/-- **Knowledge fixes every belief.** Whatever law a player holds on its
information set, a known value of the history has probability one. -/
theorem belief_map_eq_pure_of_knows {i : ι} {info : M.InfoState i}
    (history : M.InformationHistory i info) {Value : Type*}
    (read : E.History → Value) (value : Value)
    (hknown : history.1 ∈ Knows (M.historyPartition i) {other | read other = value})
    (belief : PMF (M.InformationHistory i info)) :
    belief.map (fun other => read other.1) = PMF.pure value := by
  have hconstant : (fun other : M.InformationHistory i info => read other.1) =
      fun _ => value :=
    funext fun other => mem_of_knows history hknown other
  rw [hconstant]
  exact PMF.map_const belief value

end InformationModel

end GameTheory.Protocol
