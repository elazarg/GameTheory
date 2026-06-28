/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import Math.OnlineLearning.MultiplicativeWeights

/-!
# Online learning

Umbrella module. Split across `OnlineLearning/`:

- `MultiplicativeWeights` — the multiplicative-weights (Hedge) algorithm and its
  sublinear external-regret bound `log |A| / η + (eᵑ−1−η)/η · T`.
-/
