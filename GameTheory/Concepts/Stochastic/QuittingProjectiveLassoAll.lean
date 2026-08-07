/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingAnalyticGerm
import GameTheory.Concepts.Stochastic.QuittingProjectiveAnalyticFirstEvent
import GameTheory.Concepts.Stochastic.QuittingProjectiveSingletonLCP
import GameTheory.Concepts.Stochastic.QuittingProjectiveAnchoredSingletonLCP
import GameTheory.Concepts.Stochastic.QuittingWeightedProjectiveLasso
import GameTheory.Concepts.Stochastic.QuittingProjectiveResolvedChart
import GameTheory.Concepts.Stochastic.QuittingVanishingChargeRecurrenceNoGo
import Math.FinitePivotOrbit

/-!
# Projective quitting packets and charged-lasso boundary

Public entry point for the proved projective layer:

* exact vanishing-discount quitting-germ algebra;
* matching-order extraction of the normalized cemetery, singleton, and
  residual nonsingleton first-event masses;
* zero-anchor and affine-anchor normalized singleton projective-LCP algebra;
* resolved affine feasibility-or-Farkas duality, together with the explicit
  arc-lifting contract required to turn a feasible tangent into a physical
  successor;
* finite output-or-repeated-label recurrence;
* the no-go regression showing that repeated labels and compact recurrence do
  not imply a return small relative to vanishing charge; and
* pointwise and rotation-uniform weighted charged-lasso correction and
  compilation.

The arbitrary-game producer is not contained here.  It still requires four
separate ingredients:

1. completion of analytic singleton-packet extraction by proving the limiting
   value-mixture identity and passing endpoint complementarity to the limit;
2. construction and coverage of resolved quitting Bellman charts, including
   real/Puiseux arc lifting of feasible lexicographic tangents;
3. semantic decoding of projective Farkas obstructions; and
4. a rotation-uniform relative-return or recurrent-monodromy theorem producing
   the weighted lasso seam.

See `docs/uniform-equilibrium/ProjectiveLassoProducer.md`.
-/
