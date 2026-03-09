import GameTheory.Languages.Sequential.Syntax
import GameTheory.Languages.Sequential.SOS
import GameTheory.Languages.Sequential.Compile
import GameTheory.Languages.Sequential.Theorems
import GameTheory.Languages.Sequential.Examples

/-!
# GameTheory.Languages.Sequential

Public entrypoint for the sequential/protocol language layer.

`Syntax` and `SOS` are the source-language presentation; `Compile` and
`Theorems` are the reduction interface to the generic semantic stack.
Reader-facing `Examples` stays separate from compilation `Tests`.
-/
