/-
# Factored-observation stochastic-game example

This small simultaneous two-bit game is deliberately utility-free: FOSG owns
execution and information, while a later consumer may attach an evaluation.
It is the canonical replacement for the one-step native FOSG examples in the
pinned v1 `GameTheory/Languages/FOSG/Examples.lean` at commit
`a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`.

Unlike the old fixture, it installs neither a finite-history enumeration nor a
bounded evaluator.  Its regression is the exact canonical history law of the
stable FOSG-to-EFG serializer.
-/

import GameTheory.Languages.Bridges.FOSGToEFG
import GameTheory.Languages.Bridges.NFGFOSG
import Mathlib.Logic.Equiv.Bool

noncomputable section

namespace GameTheory.Examples.FOSG

open GameTheory.Languages
open GameTheory.Languages.Bridges
open GameTheory.Probability

/-- Two players choose Boolean actions simultaneously; the terminal outcome
records both actions.  An external utility can turn this syntax into matching
pennies or another two-action game without changing its execution semantics. -/
def twoBitSource : NFG.Game Bool where
  Action _ := Bool
  Outcome := Bool × Bool
  outcome actions := (actions false, actions true)

private instance twoBitActionNonempty :
    ∀ player : Bool, Nonempty (twoBitSource.Action player) :=
  fun _ => ⟨false⟩

/-- The one-shot FOSG compilation is the canonical simultaneous execution and
factored-observation example; it does not define another FOSG runner. -/
abbrev twoBit : FOSG.Game Bool :=
  NFG.OneShotFOSG.game twoBitSource

/-- The source remains genuinely simultaneous: both real players are active
at its only decision state. -/
theorem source_simultaneous :
    twoBit.execution.active .initial false ∧
      twoBit.execution.active .initial true :=
  ⟨trivial, trivial⟩

/-- The two source players are scheduled in false-then-true order. -/
def falseFirst : FOSGToEFG.ExplicitOrder Bool where
  slots := 2
  player := finTwoEquiv

/-- The serialized target remains an ordinary stable EFG. -/
abbrev serialized : EFG.Game Bool :=
  FOSGToEFG.toEFG twoBit falseFirst

/-- Every target behavioral profile has a canonical source projection, and
erasing three serialized microsteps gives exactly one source round. -/
theorem serialized_exact
    (target : (player : Bool) →
      (FOSGToEFG.information twoBit falseFirst).BehavioralPolicy player) :
    FinDist.map (FOSGToEFG.eraseHistory twoBit falseFirst)
        ((FOSGToEFG.information twoBit falseFirst).runBehavioral target 3) =
      twoBit.information.runBehavioral
        (FOSGToEFG.projectBehavioral twoBit falseFirst target) 1 := by
  simpa [falseFirst, FOSGToEFG.roundWidth] using
    FOSGToEFG.map_erase_runBehavioral_eq_source twoBit falseFirst target 1

/-- Translating a source policy into the hidden-phase EFG preserves the same
literal one-round source-history law. -/
theorem translated_serialized_exact
    (source : (player : Bool) → twoBit.information.BehavioralPolicy player) :
    FinDist.map (FOSGToEFG.eraseHistory twoBit falseFirst)
        ((FOSGToEFG.information twoBit falseFirst).runBehavioral
          (FOSGToEFG.translateBehavioral twoBit falseFirst source) 3) =
      twoBit.information.runBehavioral source 1 := by
  simpa [falseFirst, FOSGToEFG.roundWidth] using
    FOSGToEFG.map_erase_runBehavioral_translate twoBit falseFirst source 1

end GameTheory.Examples.FOSG
