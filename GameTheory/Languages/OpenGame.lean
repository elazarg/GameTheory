/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Languages.OpenGame.Syntax
import GameTheory.Languages.OpenGame.Compile
import GameTheory.Languages.OpenGame.Sequential
import GameTheory.Languages.OpenGame.DAG
import GameTheory.Languages.OpenGame.Ownership
import GameTheory.Languages.OpenGame.Deviation
import GameTheory.Languages.OpenGame.FinTensor
import GameTheory.Languages.OpenGame.Theorems
import GameTheory.Languages.OpenGame.Correlation
import GameTheory.Languages.OpenGame.Mixed
import GameTheory.Languages.OpenGame.CoendContext
import GameTheory.Languages.OpenGame.Evolutionary

/-!
# Open Games

Public entrypoint for the Open Games research layer. It includes:

* deterministic wiring, finite sequential and sparse-DAG shapes;
* ownership, deviation-family, correlation, and evolutionary refinements;
* finite probabilistic composition and Bayesian coend contexts.

Cross-language translations are exposed by `GameTheory.Languages.Bridges`.
Reader-facing examples remain in the separate `GameTheoryExamples` target.
Modules state known non-laws explicitly; importing this umbrella does not turn
scoped results into broader category or sparse-SPE claims.
-/
