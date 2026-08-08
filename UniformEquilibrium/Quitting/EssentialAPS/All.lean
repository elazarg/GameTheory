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

The multivalued subdirectory is a separate execution layer.  Given a reached
node in a finite Flesch-successor SCC, it distinguishes a finite executable
absorbing exit, one charged chronological recurrent path inside that SCC, and
a reached typed obstruction.  It does not infer a segment from full convex-hull
APS membership or combine occupations from different recurrent components.

The capstone is
`quittingEssentialAPS_isUniformEquilibriumPayoff_of_terminalFree_unique_live_adaptiveMesh`.
It proves that every initial point of the displayed compact terminal-free
unique-live component is a uniform-equilibrium payoff.  Its source-agnostic
compiler is
`isUniformEquilibriumPayoff_of_proper_infiniteSingletonPath_of_initialSurvival`:
any bounded viable singleton-flow path with pointwise proper hazards and
vanishing deleted-player survival from its initial time has the same
conclusion.

The implementation remains conditional.  The uniform-payoff capstone treats
the compact functional unique-live-successor singleton-flow stratum.  The
multivalued SCC theorem constructs an executable path or a typed obstruction
from witnessed segment data, but does not by itself supply the tail-contraction
or punishment hypotheses needed by the uniform-payoff compiler.
-/
