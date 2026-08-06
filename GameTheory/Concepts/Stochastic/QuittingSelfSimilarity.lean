/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

/-!
# Strategic self-similarity of quitting holonomy

Entry point for the self-similarity layer:

* exact affine/max-affine residual and idempotent algebra;
* finite repetition and neutral pumping;
* absorbed-mass affine and max-plus tangent normalization;
* a proved negative/zero/positive max-plus dynamics trichotomy;
* compact tangent-core and extended obstacle extraction for arbitrary
  finite-block sequences; and
* first-order and neutral-face consequences for actual finite quitting blocks.

The accompanying derivation and research boundary are documented in
`docs/uniform-equilibrium/SelfSimilarity.md`.
-/

import GameTheory.Concepts.Stochastic.QuittingSelfSimilarityHolonomyIteration
import GameTheory.Concepts.Stochastic.QuittingSelfSimilarityAffineTangent
import GameTheory.Concepts.Stochastic.QuittingSelfSimilarityMaxPlusDynamics
import GameTheory.Concepts.Stochastic.QuittingSelfSimilarityRealizedNeutral
import GameTheory.Concepts.Stochastic.QuittingSelfSimilarityEarlyExcess
