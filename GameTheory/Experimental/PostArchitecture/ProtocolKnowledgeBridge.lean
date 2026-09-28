/-
# Protocol knowledge on merging histories

Evidence for the history-partition bridge. In the merging execution two
histories reach one terminal state after different own moves. Under own-play
recall each knows its own move, so the known event separates two histories
with the same execution state: no event about execution states is this
knowledge. The forgetful negative control is `GameTheory.Tests.ProtocolKnowledge`.
-/

import GameTheory.Protocol.Knowledge
import GameTheory.Protocol.OwnPlayRecall
import GameTheory.Experimental.PostArchitecture.KnowledgeOwnership

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.ProtocolKnowledgeBridge

open GameTheory GameTheory.Protocol GameTheory.Epistemic
open GameTheory.Protocol.ExecutionProtocol (Trace History)

section Merging

open KnowledgeOwnership

/-- The merging execution with its player remembering its own play. -/
abbrev recall : InfoSignals mergingExecution := mergingSignals.withOwnPlayRecall

/-- The history after choosing `action`. -/
def merged (action : Bool) : History mergingExecution := ⟨.merged, mergeTrace action⟩

theorem knows_own_move (action : Bool) :
    merged action ∈ Knows (recall.historyPartition ()) (recall.samePlay () (merged action)) :=
  (recall.perfectRecall_iff_knows_ownPlay.1 mergingSignals.withOwnPlayRecall_perfectRecall) () _

theorem merged_state (action : Bool) : (merged action).state = .merged := rfl

theorem merged_not_samePlay : merged false ∉ recall.samePlay () (merged true) := by
  intro hsame
  simp [InfoSignals.samePlay, recall, merged, mergeTrace, mergeJoint] at hsame

/-- **The known event is not an event about execution states.** Both histories
reach the same state, and only one of them lies in the known event. -/
theorem known_event_not_state_event :
    ¬ ∃ fact : mergingExecution.State → Prop,
      recall.samePlay () (merged true) = {history | fact history.state} := by
  rintro ⟨fact, hevent⟩
  have htrue : merged true ∈ recall.samePlay () (merged true) := rfl
  rw [hevent] at htrue
  apply merged_not_samePlay
  rw [hevent]
  exact htrue

end Merging

end GameTheory.Experimental.PostArchitecture.ProtocolKnowledgeBridge
