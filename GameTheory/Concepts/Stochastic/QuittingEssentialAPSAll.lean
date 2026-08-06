/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingEssentialAPSCycle
import GameTheory.Concepts.Stochastic.QuittingEssentialAPSRegression
import GameTheory.Concepts.Stochastic.QuittingEssentialAPSInfiniteContraction
import GameTheory.Concepts.Stochastic.QuittingInfinitePathSupersolution

/-!
# Essential APS for the quitting singleton-flow stratum

Umbrella import for the exact successor graph; algebraic, segment, and proper
essential-APS prefixes; the carrier-restricted greatest fixed family;
convex-fiber and unique-live-successor progress extraction; finite and coherent
infinite executable APS runs; compact greatest fibers under unique live
successors; uniform positive mass in every shifted window; the deterministic
conversion from total mass to playerwise opponent mass; uniform opponent block
contraction for the implemented singleton roots; and the nonperiodic
quit-only-error supersolution compiler consumed by an accuracy-indexed mesh.

The structural capstone is
`exists_quittingEssentialAPSInfiniteRun_with_opponentBlockContraction_unique_live`.
It simultaneously returns a coherent executable run, exact Bellman transport,
and a uniform opponent-survival factor strictly below one.

The implementation remains conditional.  It treats the compact functional
unique-live-successor singleton-flow stratum.  It now supplies path existence,
exact Bellman transport, opponent-survival contraction, and the game-facing
compiler for a uniformly small immediate-Quit error.  The remaining adapter is
to subdivide the nonperiodic coarse arcs at an accuracy-indexed, possibly
nonuniform mesh while preserving the selected initial value.  The structural
hypotheses are not identified with all quitting games.
-/