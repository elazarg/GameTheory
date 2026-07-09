/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Implementation.Basic
import GameTheory.Implementation.Exact
import GameTheory.Implementation.SetPrice
import GameTheory.Implementation.Mixed
import GameTheory.Implementation.Regular
import GameTheory.Implementation.Device
import GameTheory.Implementation.Informational
import GameTheory.Implementation.VCG

/-!
# k-implementation definitions API

Curated import surface for the definition layer of the k-implementation
mechanization.

This module is intentionally import-only. It exposes the canonical definitions
from the detailed modules without duplicating them under wrapper names:

* profile-observed implementation, k-implementation, and transfer-class
  equivalence/saturation vocabulary;
* exact implementation and rectangular dominance-skeleton set-price
  certificates;
* mixed-extension implementation gaps, admissibility predicates, and
  admissible/analytic price notions;
* regular compact-game implementation gaps, additive-subsidy kernels,
  semantic/analytic admissibility predicates, and admissible/analytic price
  notions;
* informational-game and signal-blind implementation notions, including their
  transfer-class equivalence/saturation vocabulary;
* implementation devices and interim dominance notions used in the paper's
  correlated-equilibrium device theorems;
* VCG and combinatorial-auction predicates used by the implementation theorem.

Use this import when downstream work needs the vocabulary but not the bundled
paper theorem/examples import surface.
-/
