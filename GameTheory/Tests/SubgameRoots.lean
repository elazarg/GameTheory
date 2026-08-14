/-
# Imperfect-information subgame roots

The hidden-card protocol has two distinct decision histories in one blind
player information set.  A continuation rooted at just one deal would cut that
information set, so it is not a proper subgame.  The initial history remains a
subgame root, as it must in every protocol.
-/

import GameTheory.Protocol.SubgamePerfect
import GameTheory.Tests.Information

noncomputable section

namespace GameTheory.Tests.SubgameRoots

open GameTheory.Protocol
open GameTheory.Protocol.ExecutionProtocol
open GameTheory.Tests

def highDealHistory : hiddenCard.History :=
  ⟨.dealt .high, dealHistory .high⟩

def lowDealHistory : hiddenCard.History :=
  ⟨.dealt .low, dealHistory .low⟩

/-- The whole hidden-card game is a subgame of itself. -/
theorem initial_isSubgameRoot :
    dealModel.IsSubgameRoot hiddenCard.initHistory :=
  dealModel.initHistory_isSubgameRoot

/-- The high-deal continuation is not a subgame: it contains one node of the
blind seat's decision information set but excludes the indistinguishable
low-deal node. -/
theorem highDeal_not_isSubgameRoot :
    ¬ dealModel.IsSubgameRoot highDealHistory := by
  intro hroot
  have hcross := hroot Seat.blind highDealHistory lowDealHistory
    (HistoryReaches.refl hiddenCard highDealHistory)
    (dealt_not_terminal .high) (by rfl)
    (dealt_not_terminal .low) (by rfl)
    blind_cannot_tell
  rcases hcross with ⟨fuel, hreach⟩
  have hequal := ExecutionProtocol.ReachesWithin.eq_of_trace_length_eq
    hreach (by rfl)
  have hstate := congrArg (fun history : hiddenCard.History => history.state) hequal
  simp [highDealHistory, lowDealHistory] at hstate

end GameTheory.Tests.SubgameRoots
