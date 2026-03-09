import GameTheory.Languages.EFG.Syntax
import GameTheory.Languages.EFG.SOS
import GameTheory.Languages.EFG.Compile
import GameTheory.Languages.EFG.CompileObs
import GameTheory.Languages.EFG.Kuhn
import GameTheory.Languages.EFG.Theorems
import GameTheory.Languages.EFG.Examples
import GameTheory.Languages.EFG.Refinements
import GameTheory.Theorems.OneShotDeviation
import GameTheory.Theorems.Zermelo

/-!
# GameTheory.Languages.EFG

Public entrypoint for the extensive-form language layer.

This surface is intentionally textbook-facing:
- `Syntax` defines the tree, information structure, and native histories
- `SOS` exposes the structural execution view
- `Compile` maps the language into generic semantic targets
- `Theorems` packages language-level reductions
- `Examples` stays separate from `Tests`
-/
