/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Languages.Expressiveness.Basic
import GameTheory.Languages.Expressiveness.Relations
import GameTheory.Languages.Expressiveness.CausalContext
import GameTheory.Languages.Expressiveness.MAID_EFG
import GameTheory.Languages.Expressiveness.EFG_FOSG

/-!
# GameTheory.Languages.Expressiveness

Umbrella import for language expressiveness definitions and semantic comparison
lenses.

This is retained public reduction infrastructure, not merely an index of the
comparisons currently instantiated inside the repository. Consequently the
API includes closure operations such as identity, composition, restriction,
and subreductions even when a particular combinator has no current internal
caller; downstream language comparisons can build on them without changing
the core semantic vocabulary.
-/
