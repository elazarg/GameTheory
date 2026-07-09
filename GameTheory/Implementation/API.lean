/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Implementation.API.Definitions
import GameTheory.Implementation.API.Theorems
import GameTheory.Implementation.API.Examples

/-!
# k-implementation API

Public API aggregator for the k-implementation mechanization.

The API is split by intent:

* `GameTheory.Implementation.API.Definitions` for vocabulary;
* `GameTheory.Implementation.API.Theorems` for positive theorem statements;
* `GameTheory.Implementation.API.Examples` for worked examples and
  counterexamples.

The files are import-only: they do not create wrapper declarations or duplicate
names from the detailed proof modules.
-/
