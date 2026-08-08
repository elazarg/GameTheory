/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Holonomy.Compactness
import UniformEquilibrium.Quitting.Boundary.Holonomy.RealizedTangent
import UniformEquilibrium.Quitting.Boundary.Holonomy.AllTailRepairValue
import UniformEquilibrium.Quitting.Boundary.Holonomy.BehavioralTailEvaluation
import UniformEquilibrium.Quitting.Boundary.Holonomy.BehavioralTailRepairValue
import UniformEquilibrium.Quitting.Boundary.Holonomy.AggregateTerminalAnchor

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

The fixed-prefix repair interface evaluates a bounded prescribed/best-response
boundary pair through the affine/max-affine holonomy.  Its gain modulus is
uniform over every pair in the boundary box and therefore survives an infimum
over any one source-independent tail family.  It does not construct or certify
the pairs as tails.  The behavioral-tail adapter identifies prescribed payoff
through an actual phase switch and the finite all-behavior envelope through the
same holonomy.  The corresponding infinite-tail envelope identity remains a
separate supremum-interchange theorem.

The behavioral-tail repair value specializes the abstract fixed family to the
prescribed/envelope pair co-realized by each actual tail and inherits the same
Lipschitz and buffered repair/obstruction laws.  The aggregate terminal anchor
keeps the marked packet on the optimizer controlled by the calibrated
prepend-loss theorem; it is intentionally distinct from the min--max anchor.
-/
