/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Languages.NFG.Syntax
import GameTheory.Languages.NFG.Compile
import GameTheory.Languages.NFG.Examples
import GameTheory.Languages.NFG.CongestionGame
import GameTheory.Languages.NFG.PublicGoods
import GameTheory.Languages.NFG.Stackelberg

/-!
# GameTheory.Languages.NFG

Public entrypoint for the normal-form game language layer.

- `Syntax` defines the `NFGGame` structure, strategy profiles, and pure solution concepts
- `Compile` maps the language into `KernelGame` and provides mixed strategy support
- `Examples` demonstrates Prisoner's Dilemma and Matching Pennies
- `CongestionGame` defines congestion games with Rosenthal's potential
- `PublicGoods` models voluntary contribution games
- `Stackelberg` models leader-follower games

Non-strategic-form models (coalitional games, axiomatic bargaining,
matching markets) live under `GameTheory.Cooperative`.
-/
