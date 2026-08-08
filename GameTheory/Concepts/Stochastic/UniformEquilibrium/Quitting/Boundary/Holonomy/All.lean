/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Boundary.Holonomy.Compactness
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Boundary.Holonomy.RealizedTangent

/-!
# Boundary holonomy for finite quitting blocks

Public umbrella for the finite-boundary-holonomy family.

The source-retaining branch packages actual finite root blocks and proves
compactness at fixed cutoff or fixed last stage.  The coefficient branch gives
affine and max-affine residual cocycles, self-similarity, absorbed-mass tangent
normal forms, realized first-order bounds, and compact coordinate
subsequences.

These are complementary interfaces.  Fixed-cutoff compactness retains the
strategic source but does not cover escaping block length.  Tangent-coordinate
compactness covers coefficient projections but does not prove that the
limiting coordinates are realized by a strategic block, retain a source path,
or admit a strategic decoder.
-/
