/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

/-!
# Strategic self-similarity of quitting holonomy

Entry point for the self-similarity layer:

* exact affine/max-affine residual and idempotent algebra;
* absorbed-mass tangent normalization near the identity; and
* first-order and neutral-face consequences for actual finite quitting blocks.

The accompanying derivation and research boundary are documented in
`docs/uniform-equilibrium/SelfSimilarity.md`.
-/

import GameTheory.Concepts.Stochastic.QuittingSelfSimilarityHolonomy
import GameTheory.Concepts.Stochastic.QuittingSelfSimilarityAffineTangent
import GameTheory.Concepts.Stochastic.QuittingSelfSimilarityMaxAffineTangent
import GameTheory.Concepts.Stochastic.QuittingSelfSimilarityRealizedNeutral
