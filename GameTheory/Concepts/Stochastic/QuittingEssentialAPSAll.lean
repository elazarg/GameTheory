/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingEssentialAPSCycle
import GameTheory.Concepts.Stochastic.QuittingEssentialAPSRegression
import GameTheory.Concepts.Stochastic.QuittingEssentialAPSInfiniteContraction

/-!
# Essential APS for the quitting singleton-flow stratum

Umbrella import for the exact successor graph; algebraic, segment, and proper
essential-APS prefixes; the carrier-restricted greatest fixed family;
convex-fiber and unique-live-successor progress extraction; finite and coherent
infinite executable APS runs; compact greatest fibers under unique live
successors; uniform positive mass in every shifted window; the deterministic
conversion from total mass to playerwise opponent mass; and uniform opponent
block contraction for the implemented singleton roots.

The capstone is
`exists_quittingEssentialAPSInfiniteRun_with_opponentBlockContraction_unique_live`.
It simultaneously returns a coherent executable run, exact Bellman transport,
and a uniform opponent-survival factor strictly below one.

The implementation remains conditional.  It treats the compact functional
unique-live-successor singleton-flow stratum.  It now supplies path existence,
exact Bellman transport, and opponent-survival contraction, but it does not by
itself prove the local root-Nash inequalities needed by the existing
nonperiodic equilibrium compiler, nor identify this stratum with all quitting
games.
-/
