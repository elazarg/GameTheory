import GameTheory.Languages.Bridges.FOSG.AugmentedEFG
import GameTheory.Languages.Bridges.FOSG.SerialExec
import GameTheory.Languages.FOSG.Examples

/-!
# GameTheory.Languages.Bridges.FOSG.Examples

Compile-only smoke examples for the FOSG -> augmented-EFG bridge.
-/

namespace GameTheory

namespace FOSG

namespace AugmentedEFGBridge

namespace Examples

/-- The canonical bridge execution kernel elaborates on the one-player
binary-choice example. -/
noncomputable example
    [Fact GameTheory.FOSG.Examples.binaryChoice.LegalObservable]
    (σ : GameTheory.FOSG.Examples.binaryChoice.LegalBehavioralProfile) :
    PMF (SerialExec.State GameTheory.FOSG.Examples.binaryChoice) :=
  SerialExec.runOriginal
    (G := GameTheory.FOSG.Examples.binaryChoice)
    1 σ

/-- The kernel erasure theorem specializes to binary choice. -/
example
    [Fact GameTheory.FOSG.Examples.binaryChoice.LegalObservable]
    (σ : GameTheory.FOSG.Examples.binaryChoice.LegalBehavioralProfile) :
    PMF.map
        (SerialExec.erase (G := GameTheory.FOSG.Examples.binaryChoice))
        (SerialExec.runOriginal
          (G := GameTheory.FOSG.Examples.binaryChoice)
          1 σ) =
      GameTheory.FOSG.Examples.binaryChoice.runDist 1 σ :=
  SerialExec.runOriginal_erases_to_native
    (G := GameTheory.FOSG.Examples.binaryChoice)
    1 σ

/-- The canonical bridge execution kernel elaborates on matching pennies. -/
noncomputable example
    [Fact GameTheory.FOSG.Examples.MatchingPennies.game.LegalObservable]
    (σ : GameTheory.FOSG.Examples.MatchingPennies.game.LegalBehavioralProfile) :
    PMF (SerialExec.State GameTheory.FOSG.Examples.MatchingPennies.game) :=
  SerialExec.runOriginal
    (G := GameTheory.FOSG.Examples.MatchingPennies.game)
    1 σ

/-- The kernel erasure theorem specializes to matching pennies. -/
example
    [Fact GameTheory.FOSG.Examples.MatchingPennies.game.LegalObservable]
    (σ : GameTheory.FOSG.Examples.MatchingPennies.game.LegalBehavioralProfile) :
    PMF.map
        (SerialExec.erase (G := GameTheory.FOSG.Examples.MatchingPennies.game))
        (SerialExec.runOriginal
          (G := GameTheory.FOSG.Examples.MatchingPennies.game)
          1 σ) =
      GameTheory.FOSG.Examples.MatchingPennies.game.runDist 1 σ :=
  SerialExec.runOriginal_erases_to_native
    (G := GameTheory.FOSG.Examples.MatchingPennies.game)
    1 σ

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
