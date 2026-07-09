/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Implementation.Singleton
import GameTheory.Implementation.SetPrice
import GameTheory.Implementation.Mixed
import GameTheory.Implementation.Regular
import GameTheory.Implementation.Device
import GameTheory.Implementation.Informational
import GameTheory.Implementation.VCG

/-!
# k-implementation theorem API

Curated import surface for the main positive theorem layer of the
k-implementation mechanization.

This module delegates to the detailed theorem files and adds no aliases. It is
the intended import for users who want:

* finite singleton implementation and price formulae;
* exact rectangular target-set prices via dominance-skeleton and
  branch-certificate search surfaces;
* transfer-class saturation theorems for restricted implementation languages;
* the `ε`-Nash threshold/singleton-price `ℓ∞`/`ℓ¹` sandwich;
* the constructive mixed-equilibrium-to-implementation direction, the
  unrestricted converse counterexample boundary, the corrected
  selection-admissible mixed-extension price formula, and the analytic
  own-USC price formula with nondegenerate exact attainment;
* the compact regular-game analogue of the singleton price theorem under
  semantic/analytic admissibility, including metric exact attainment and
  zero-cost existence iff Nash, plus compact own-USC undominated-strategy
  existence;
* pointwise recommendation-device implementation theorems for correlated
  equilibria, including weak and strict support-sensitive forms;
* informational-game transfer theorems and transfer-class saturation theorems;
* the factored VCG conformance-bonus and equivalence-class theorems, including
  the redundant-report transfer-class obstruction.

Counterexamples and worked examples are kept out of this module; import
`GameTheory.Implementation.API.Examples` for those.
-/
