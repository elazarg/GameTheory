/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingAnalyticGerm
import GameTheory.Concepts.Stochastic.QuittingProjectiveSingletonLCP
import GameTheory.Concepts.Stochastic.QuittingProjectiveLassoWeighted
import GameTheory.Concepts.Stochastic.QuittingVanishingChargeRecurrenceNoGo
import Math.AffineEqualityFarkas
import Math.FinitePivotOrbit

/-!
# Projective quitting packets and charged-lasso boundary

Public entry point for the proved projective layer:

* exact vanishing-discount quitting-germ algebra;
* normalized singleton projective-LCP algebra;
* resolved affine feasibility-or-Farkas duality;
* finite output-or-repeated-label recurrence;
* the no-go regression showing that repeated labels and compact recurrence do
  not imply a return small relative to vanishing charge; and
* pointwise and weighted charged-lasso correction and compilation.

The arbitrary-game producer is not contained here.  It still requires a
semantic decoder for projective Farkas obstructions and a relative-return or
recurrent-monodromy theorem.  See
`docs/uniform-equilibrium/ProjectiveLassoProducer.md`.
-/
