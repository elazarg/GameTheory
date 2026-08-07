/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingAnalyticGerm
import GameTheory.Concepts.Stochastic.QuittingProjectiveAnalyticFirstEvent
import GameTheory.Concepts.Stochastic.QuittingProjectiveAnalyticPacket
import GameTheory.Concepts.Stochastic.QuittingProjectiveTargetMismatch
import GameTheory.Concepts.Stochastic.QuittingProjectiveSingletonLCP
import GameTheory.Concepts.Stochastic.QuittingProjectiveAnchoredSingletonLCP
import GameTheory.Concepts.Stochastic.QuittingWeightedProjectiveLasso
import GameTheory.Concepts.Stochastic.QuittingSingleSeamProjectiveLasso
import GameTheory.Concepts.Stochastic.QuittingProjectiveResolvedChart
import GameTheory.Concepts.Stochastic.QuittingVanishingChargeRecurrenceNoGo
import Math.FinitePivotOrbit
import Math.CompactFiniteChargedReturn

/-!
# Projective quitting packets and charged-lasso boundary

Public entry point for the proved projective layer:

* exact vanishing-discount quitting-germ algebra;
* matching-order extraction of the normalized cemetery and singleton masses,
  vanishing residual nonsingleton mass, the endpoint value mixture, and
  limiting complementarity as a complete singleton packet;
* the target-mismatch regression: an exact analytic matching branch whose
  positive-cemetery packet value is quantitatively separated from every
  nearby terminal approximate equilibrium, while other exact uniform targets
  remain available;
* zero-anchor and affine-anchor normalized singleton projective-LCP algebra;
* resolved affine feasibility-or-Farkas duality, together with the explicit
  arc-lifting contract required to turn a feasible tangent into a physical
  successor;
* finite output-or-repeated-label recurrence;
* finite charged return: a sufficiently charged bounded finite orbit contains
  a close returned block carrying fixed aggregate absorption;
* the no-go regression, now correctly scoped to bounded-total-charge paths and
  to comparison with a source one-step charge; and
* pointwise, rotation-uniform weighted, and single-seam projective-lasso
  correction and compilation.

The arbitrary-game producer is not contained here.  Before the three
accepted-target construction ingredients, it requires an explicit target
gate: accept the packet value with an executable continuation contract, or
reject it and retarget through a proved alternative.  On an accepted target
the remaining ingredients are:

1. construction and coverage of resolved quitting Bellman charts, including
   real/Puiseux arc lifting of feasible lexicographic tangents;
2. semantic decoding of projective Farkas obstructions; and
3. arbitrarily large finite-prefix real absorption on the continuing physical
   branch, or a strategic consumer for the complementary bounded-charge
   boundary.

A separate rotation-uniform recurrence theorem is no longer required for an
exact bounded forward orbit.  Compact finite charged return selects one block
with a small endpoint seam and fixed aggregate absorption; the single-seam
compiler supplies rotation-uniformity automatically.
-/