/-
# Subgame perfection for extensive-form games

The well-founded one-shot deviation principle is proved once for the accepted
`InformationModel`. This module exposes transparent EFG specializations and one
named equivalence; it adds no subtree evaluator or language-specific strategic
semantics.
-/

import GameTheory.Languages.EFG.Strategic
import GameTheory.Protocol.SubgamePerfect

noncomputable section

namespace GameTheory.Languages.EFG

open GameTheory.Protocol

universe uι us ua up uq uk

namespace Game

variable {ι : Type uι} (G : Game.{uι, us, ua, up, uq, uk} ι)

/-- A candidate EFG subgame root is a history whose continuation is closed
under every decision information set. -/
abbrev IsSubgameRoot (history : G.History) : Prop :=
  G.information.IsSubgameRoot history

/-- EFG subgame perfection is the canonical information-model predicate over
information-set-closed subgame roots. -/
abbrev IsSubgamePerfect [DecidableEq ι]
    (certificate : G.execution.WellFoundedPlay)
    (profile : Profile G.strategicSignature)
    (utility : G.History → ι → ℝ) : Prop :=
  G.information.IsSubgamePerfect certificate profile utility

/-- The stronger continuation predicate compares whole replacement plans after
every complete history, whether or not that history starts a proper subgame. -/
abbrev IsHistorywiseOptimal [DecidableEq ι]
    (certificate : G.execution.WellFoundedPlay)
    (profile : Profile G.strategicSignature)
    (utility : G.History → ι → ℝ) : Prop :=
  G.information.IsHistorywiseOptimal certificate profile utility

/-- EFG one-shot optimality is the canonical typed, history-local predicate. -/
abbrev HasNoProfitableOneShotDeviation [DecidableEq ι]
    [∀ who, DecidableEq (G.information.InfoState who)]
    (certificate : G.execution.WellFoundedPlay)
    (profile : Profile G.strategicSignature)
    (utility : G.History → ι → ℝ) : Prop :=
  G.information.HasNoProfitableOneShotDeviation
    certificate profile utility

/-- Historywise optimality implies textbook subgame perfection. -/
theorem IsHistorywiseOptimal.isSubgamePerfect [DecidableEq ι]
    {certificate : G.execution.WellFoundedPlay}
    {profile : Profile G.strategicSignature}
    {utility : G.History → ι → ℝ}
    (hoptimal : G.IsHistorywiseOptimal certificate profile utility) :
    G.IsSubgamePerfect certificate profile utility :=
  GameTheory.Protocol.InformationModel.IsHistorywiseOptimal.isSubgamePerfect
    G.information hoptimal

/-- **EFG historywise one-shot deviation principle.** On a well-founded EFG
where a nontrivial information state is not revisited, a profile is optimal
after every complete history exactly when it has no profitable one-shot
deviation after any history. -/
theorem isHistorywiseOptimal_iff_hasNoProfitableOneShotDeviation
    [DecidableEq ι]
    [∀ who, DecidableEq (G.information.InfoState who)]
    (hactsOnce : G.information.ActsOnceWhereItMatters)
    (certificate : G.execution.WellFoundedPlay)
    (profile : Profile G.strategicSignature)
    (utility : G.History → ι → ℝ) :
    G.IsHistorywiseOptimal certificate profile utility ↔
      G.HasNoProfitableOneShotDeviation certificate profile utility :=
  G.information.isHistorywiseOptimal_iff_hasNoProfitableOneShotDeviation
    hactsOnce certificate profile utility

end Game

end GameTheory.Languages.EFG
