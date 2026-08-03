/-
# Zermelo backward induction for EFG presentations

The constructive optimization lives in `Protocol.Zermelo`.  This file only
specializes its perfect-information premise and single-mover argument to the
transparent EFG presentation; it introduces neither a tree evaluator nor a
language-specific subgame-perfect predicate.
-/

import GameTheory.Languages.EFG.SubgamePerfect
import GameTheory.Protocol.Zermelo

noncomputable section

namespace GameTheory.Languages.EFG

open GameTheory.Protocol

universe uι us ua up uq uk

namespace Game

variable {ι : Type uι} (G : Game.{uι, us, ua, up, uq, uk} ι)

/-- Perfect information for an EFG presentation: a player's information state
identifies every complete history at which that player genuinely moves. -/
abbrev HasPerfectInformation : Prop :=
  G.information.SeparatesDecisionHistories

/-- **Zermelo backward induction for EFG presentations.** A well-founded,
perfect-information EFG with finite nonempty local choice carriers has a pure
subgame-perfect contingent-plan profile. -/
theorem exists_isSubgamePerfect
    [DecidableEq ι]
    [∀ who, DecidableEq (G.information.InfoState who)]
    [∀ who info, Finite (G.information.Choice who info)]
    [∀ who info, Nonempty (G.information.Choice who info)]
    (certificate : G.execution.WellFoundedPlay)
    (hperfect : G.HasPerfectInformation)
    (utility : G.History → ι → ℝ) :
    ∃ profile : Profile G.strategicSignature,
      G.IsSubgamePerfect certificate profile utility :=
  G.information.exists_isSubgamePerfect G.singleMover certificate hperfect utility

end Game

end GameTheory.Languages.EFG
