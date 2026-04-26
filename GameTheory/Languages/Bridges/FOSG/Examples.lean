import GameTheory.Languages.Bridges.FOSG.AugmentedEFG
import GameTheory.Languages.FOSG.Examples

/-!
# GameTheory.Languages.Bridges.FOSG.Examples

Compile-only smoke examples for the FOSG -> augmented-EFG bridge.
-/

namespace GameTheory

namespace FOSG

namespace AugmentedEFGBridge

namespace Examples

/-- The bounded augmented bridge elaborates on the one-player binary-choice
example once the paper's legal-observability WF condition is supplied. -/
noncomputable example
    [Fact GameTheory.FOSG.Examples.binaryChoice.LegalObservable] :
    EFG.AugmentedGame :=
  toAugmentedOfBoundedHorizon
    (G := GameTheory.FOSG.Examples.binaryChoice)
    GameTheory.FOSG.Examples.binaryChoiceBoundedHorizon

/-- The bounded augmented bridge elaborates on matching pennies once the
paper's legal-observability WF condition is supplied. -/
noncomputable example
    [Fact GameTheory.FOSG.Examples.MatchingPennies.game.LegalObservable] :
    EFG.AugmentedGame :=
  toAugmentedOfBoundedHorizon
    (G := GameTheory.FOSG.Examples.MatchingPennies.game)
    GameTheory.FOSG.Examples.MatchingPennies.boundedHorizon

end Examples

end AugmentedEFGBridge

end FOSG

end GameTheory
