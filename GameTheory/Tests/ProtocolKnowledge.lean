/-
# Knowing one's own play

The two-vote protocol observes only whether play has stopped. Before voting the
player does not know that it has not voted yet, and a belief on its information
set may be certain of the opposite. Refined by own-play recall, the same player
knows its own play everywhere.
-/

import GameTheory.Protocol.Knowledge
import GameTheory.Protocol.OwnPlayRecall
import GameTheory.Tests.Randomized

noncomputable section

namespace GameTheory.Tests.ProtocolKnowledge

open GameTheory GameTheory.Protocol GameTheory.Epistemic GameTheory.Tests.Randomized
open GameTheory.Protocol.ExecutionProtocol (Trace History)

/-- The two-vote history before any vote. -/
def startHistory : History twice := ⟨_, .start⟩

/-- The two-vote history after one vote. -/
def afterVote : History twice := ⟨_, votedOnce⟩

/-- Without recall the player does not know that it has not voted yet. -/
theorem not_knows_own_play :
    startHistory ∉ Knows (signals.historyPartition ()) (signals.samePlay () startHistory) := by
  intro hknown
  have hafter := (signals.mem_knows_historyPartition_iff () _ _).1 hknown afterVote rfl
  simp [InfoSignals.samePlay, afterVote, votedOnce, startHistory, InfoSignals.ownPlay] at hafter

/-- The initial history in its information set. -/
def initialAt : model.InformationHistory () false := ⟨startHistory, rfl⟩

/-- The voted history in the same information set. -/
def afterAt : model.InformationHistory () false := ⟨afterVote, rfl⟩

/-- **Truth is not knowledge.** At the initial history the player has not voted,
yet a belief on its information set can be certain that it has. -/
theorem belief_contradicts_true_play :
    (PMF.pure afterAt).map (fun other => model.ownPlay () other.1.trace) ≠
      PMF.pure (model.ownPlay () initialAt.1.trace) := by
  rw [PMF.pure_map]
  intro hsame
  have hsupport := congrArg PMF.support hsame
  rw [PMF.support_pure, PMF.support_pure, Set.singleton_eq_singleton_iff] at hsupport
  simp [afterAt, initialAt, afterVote, votedOnce, startHistory, InfoSignals.ownPlay] at hsupport

/-- With own-play recall the player knows its own play at every history. -/
theorem recall_knows_own_play (history : History twice) :
    history ∈ Knows (signals.withOwnPlayRecall.historyPartition ())
      (signals.withOwnPlayRecall.samePlay () history) :=
  (signals.withOwnPlayRecall.perfectRecall_iff_knows_ownPlay.1
    signals.withOwnPlayRecall_perfectRecall) () history

end GameTheory.Tests.ProtocolKnowledge
