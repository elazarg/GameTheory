/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeSmallPlayers
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauDebtTransfer

/-!
# Counterexample cardinality in the debt-transfer separator

The generic reset/incidence separator exposes three distinct player labels.
In the counterexample regime the unconditional three-player theorem excludes
the equality case, so the unmatched branch lives only at four or more
players.
-/

noncomputable section

namespace GameTheory

open Filter Set
open scoped Topology

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {reward : {S : Finset iota // S.Nonempty} → Payoff iota}

namespace QuittingCounterexampleRegime

/-- In a genuine counterexample, the unmatched reset/incidence separator has
ambient cardinality at least four.  The three-player output of the generic
finite geometry is dispatched by unconditional three-player existence. -/
theorem exists_matched_transfer_incidence_or_twoOpponent_separator_fourPlayers
    (regime : QuittingCounterexampleRegime reward)
    (source target : QuittingTerminalSemanticPair iota) (who : iota)
    (mass : QuittingTerminalOutcome iota → Real)
    (hmass : mass ∈ stdSimplex Real (QuittingTerminalOutcome iota))
    (hdebt : 0 < quittingTerminalSemanticDebt source who)
    (htransfer : quittingTerminalSemanticDebt source who ≤
      ∑ other ∈ (Finset.univ.erase who),
        quittingTerminalSemanticDebtChange source target other)
    (hincidence : 0 < quittingTerminalOpponentContainingMass who mass) :
    (∃ other, other ≠ who ∧
        0 < quittingTerminalSemanticDebtChange source target other ∧
        0 < quittingTerminalOpponentIncidenceMass who other mass) ∨
      ∃ receiver quitter,
        receiver ≠ who ∧ quitter ≠ who ∧ receiver ≠ quitter ∧
        quittingTerminalSemanticDebt source who /
            ((Finset.univ.erase who).card : Real) ≤
          quittingTerminalSemanticDebtChange source target receiver ∧
        0 < quittingTerminalOpponentIncidenceMass who quitter mass ∧
        4 ≤ Fintype.card iota := by
  rcases exists_matched_transfer_incidence_or_twoOpponent_separator
      source target who mass hmass hdebt htransfer hincidence with
    hmatch | ⟨receiver, quitter, hreceiver, hquitter, hdistinct,
      haverage, hpositive, _hthree⟩
  · exact Or.inl hmatch
  · exact Or.inr ⟨receiver, quitter, hreceiver, hquitter, hdistinct,
      haverage, hpositive, regime.three_lt_card⟩

end QuittingCounterexampleRegime

end GameTheory
