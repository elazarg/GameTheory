import GameTheoryComplexity.PPAD
import GameTheoryComplexity.Tests.RawEndOfLine

/-! Source-aware decoding recovers a raw answer when endpoint search returns an
empty invalid-promise witness, and retains ordinary endpoint solutions. -/

namespace GameTheory.Complexity.Tests.PPAD

open GameTheory.Complexity.Backend
open GameTheory.Complexity.Tests.EndOfLine
open GameTheory.Complexity.Tests.RawEndOfLine

example : rawToEndpointDecode ![brokenInitialLink, []] = [false] := by decide

example : rawToEndpointDecode ![oneBitPath, [true]] = [true] := by decide

example : rawToEndpointDecode ![missingCircuits, []] = [] := by decide

example : rawEndOfLineRelation brokenInitialLink
    (rawToEndpointDecode ![brokenInitialLink, []]) :=
  rawToEndpointReduction.sound _ _ (Or.inr ⟨brokenInitialLink_not_strong_source, rfl⟩)

example : rawEndOfLineRelation brokenInitialLink [false] := by
  exact (rawEndOfLineVerdict_accept _ _).mp brokenInitialLink_accepts_origin

end GameTheory.Complexity.Tests.PPAD
