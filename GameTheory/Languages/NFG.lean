import GameTheory.Languages.NFG.Syntax
import GameTheory.Languages.NFG.Compile
import GameTheory.Languages.NFG.Examples

/-!
# GameTheory.Languages.NFG

Public entrypoint for the normal-form game language layer.

- `Syntax` defines the `NFGGame` structure, strategy profiles, and pure solution concepts
- `Compile` maps the language into `KernelGame` and provides mixed strategy support
- `Examples` demonstrates Prisoner's Dilemma and Matching Pennies
-/
