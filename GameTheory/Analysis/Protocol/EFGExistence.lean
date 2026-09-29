/-
# Sequential-equilibrium existence for finite extensive games

This explicit analytic import adds existence to the lightweight EFG
assessment interface. Finite tree-shaped execution supplies finite histories;
decision recall (implied by perfect recall) and inhabited total policies supply
the strategic hypotheses.
-/

import GameTheory.Analysis.Protocol.EFG
import GameTheory.Analysis.Protocol.SequentialExistence
import GameTheory.Protocol.FiniteHorizon

noncomputable section

namespace GameTheory.Languages.EFG.Game

open GameTheory.Protocol

universe uι us ua up uq uk

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (G : Game.{uι, us, ua, up, uq, uk} ι)
    [Fintype G.execution.State]

/-- Decision-recall EFGs with finitely many states have a sequential equilibrium.
Actions and information states may range over infinite carriers. The conclusion
is the existing EFG predicate. -/
theorem exists_isSequentialEquilibrium
    (hrecall : G.information.DecisionRecall)
    (fallback : (i : ι) → G.information.Policy i)
    (payoff : ι → G.History → ℝ) (certificate : G.execution.WellFoundedHistories) :
    ∃ assessment : G.information.BehavioralAssessment,
      G.IsSequentialEquilibrium
        (hrecall.decisionInformationAntichain)
        assessment certificate payoff := by
  let : Fintype G.History := G.historyFintype
  exact G.information.exists_sequentialEquilibrium hrecall fallback payoff certificate

omit [Fintype ι] [DecidableEq ι] in
/-- The finite tree certifies terminal play. -/
theorem wellFoundedHistories : G.execution.WellFoundedHistories :=
  let : Fintype G.History := G.historyFintype
  G.execution.wellFoundedHistories_of_fintype

end GameTheory.Languages.EFG.Game
