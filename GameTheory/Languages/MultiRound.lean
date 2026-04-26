import GameTheory.Languages.MultiRound.Syntax
import GameTheory.Languages.MultiRound.SOS
import GameTheory.Languages.MultiRound.Compile
import GameTheory.Languages.MultiRound.Theorems
import GameTheory.Languages.MultiRound.Examples

/-!
# GameTheory.Languages.MultiRound

Public entrypoint for the sequential/protocol language layer.

`Syntax` and `SOS` are the source-language presentation; `Compile` and
`Theorems` are the reduction interface to the generic semantic stack.
Reader-facing `Examples` stays separate from compilation `Tests`.
-/
