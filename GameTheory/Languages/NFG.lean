import GameTheory.Languages.NFG.Syntax
import GameTheory.Languages.NFG.Compile
import GameTheory.Languages.NFG.Examples
import GameTheory.Languages.NFG.CongestionGame
import GameTheory.Languages.NFG.CoalitionalGame
import GameTheory.Languages.NFG.Bargaining
import GameTheory.Languages.NFG.Matching
import GameTheory.Languages.NFG.PublicGoods
import GameTheory.Languages.NFG.Stackelberg

/-!
# GameTheory.Languages.NFG

Public entrypoint for the normal-form game language layer.

- `Syntax` defines the `NFGGame` structure, strategy profiles, and pure solution concepts
- `Compile` maps the language into `KernelGame` and provides mixed strategy support
- `Examples` demonstrates Prisoner's Dilemma and Matching Pennies
- `CongestionGame` defines congestion games with Rosenthal's potential
- `CoalitionalGame` defines TU coalitional games and the Shapley value
- `Bargaining` formalizes the Nash bargaining solution
- `Matching` formalizes stable matching (Gale-Shapley)
- `PublicGoods` models voluntary contribution games
- `Stackelberg` models leader-follower games
-/
