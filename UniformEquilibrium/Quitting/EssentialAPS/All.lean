/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.EssentialAPS.Cycle
import UniformEquilibrium.Quitting.EssentialAPS.Regression
import UniformEquilibrium.Quitting.EssentialAPS.InfiniteContraction
import UniformEquilibrium.Quitting.EssentialAPS.UniformPayoff
import UniformEquilibrium.Quitting.EssentialAPS.AdaptiveMeshUniformPayoff
import UniformEquilibrium.Quitting.EssentialAPS.Multivalued.All

/-!
# Essential APS for the quitting singleton-flow stratum

Umbrella import for the exact successor graph; algebraic, segment, and proper
essential-APS prefixes; the carrier-restricted greatest fixed family;
convex-fiber and unique-live-successor progress extraction; finite and coherent
infinite executable APS runs; compact greatest fibers under unique live
successors; uniform positive mass in every shifted window; the deterministic
conversion from total mass to playerwise opponent mass; and uniform opponent
block contraction for the implemented singleton roots.  It also exports the
qualitative survival-decay route, variable logarithmic subdivision,
nonperiodic Snell supersolution, and uniform-payoff compiler.  The fixed-width
and geometric-contraction APIs remain available as quantitative
specializations.

The multivalued layer adds a separate finite-SCC execution surface.  It keeps
graph connectivity distinct from exact singleton-arc witnesses and returns a
finite absorbing execution, a component-charged recurrent execution, or a
reached typed obstruction.  Its occupation regression prevents cancellation
between distinct recurrent SCCs from being used as a chronological path.

The capstone for the functional unique-live stratum remains
`quittingEssentialAPS_isUniformEquilibriumPayoff_of_terminalFree_unique_live_adaptiveMesh`.
The multivalued layer is an execution producer only: it does not claim the
survival-contraction or punishment hypotheses needed by that uniform-payoff
compiler.
-/
