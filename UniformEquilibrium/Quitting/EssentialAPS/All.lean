/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.EssentialAPS.Cycle
import UniformEquilibrium.Quitting.EssentialAPS.Regression
import UniformEquilibrium.Quitting.EssentialAPS.InfiniteContraction
import UniformEquilibrium.Quitting.EssentialAPS.OccupationCancellationRegression
import UniformEquilibrium.Quitting.EssentialAPS.SegmentClosedExecution
import UniformEquilibrium.Quitting.EssentialAPS.UniformPayoff
import UniformEquilibrium.Quitting.EssentialAPS.AdaptiveMeshUniformPayoff

/-!
# Essential APS for the quitting singleton-flow stratum

Umbrella import for the exact successor graph; algebraic, segment, and proper
essential-APS prefixes; the carrier-restricted greatest fixed family;
convex-fiber and unique-live-successor progress extraction; finite and coherent
infinite executable APS runs; multivalued chronological execution under the
exact segment-closure hypothesis; compact greatest fibers under unique live
successors; uniform positive mass in every shifted window; the deterministic
conversion from total mass to playerwise opponent mass; and uniform opponent
block contraction for the implemented singleton roots.  It also exports the
qualitative survival-decay route, variable logarithmic subdivision,
nonperiodic Snell supersolution, and uniform-payoff compiler.  The fixed-width
and geometric-contraction APIs remain available as quantitative
specializations.

The occupation-cancellation regression records a separate semantic boundary:
a balanced invariant occupation over several closed classes need not select a
chronological execution with the same cancellation.

The capstone is
`quittingEssentialAPS_isUniformEquilibriumPayoff_of_terminalFree_unique_live_adaptiveMesh`.
It proves that every initial point of the displayed compact terminal-free
unique-live component is a uniform-equilibrium payoff.  Its source-agnostic
compiler is
`isUniformEquilibriumPayoff_of_proper_infiniteSingletonPath_of_initialSurvival`:
any bounded viable singleton-flow path with pointwise proper hazards and
vanishing deleted-player survival from its initial time has the same
conclusion.

The implementation remains conditional.  It treats the compact functional
unique-live-successor singleton-flow stratum and does not identify this
stratum with all quitting games.
-/
