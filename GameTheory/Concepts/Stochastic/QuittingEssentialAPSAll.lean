/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingEssentialAPSCycle
import GameTheory.Concepts.Stochastic.QuittingEssentialAPSRegression
import GameTheory.Concepts.Stochastic.QuittingEssentialAPSUniformPayoff

/-!
# Essential APS for the quitting singleton-flow stratum

Umbrella import for the exact successor graph; algebraic, segment, and proper
essential-APS prefixes; the carrier-restricted greatest fixed family;
convex-fiber and unique-live-successor progress extraction; finite and coherent
infinite executable APS runs; compact greatest fibers under unique live
successors; uniform positive mass in every shifted window; bounded-drift
opponent charging; block survival contraction; the nonperiodic quit-error
supersolution; accuracy-indexed variable subdivision; and uniformization.

The structural capstone is
`exists_quittingEssentialAPSInfiniteRun_with_opponentBlockContraction_unique_live`.
It returns a coherent executable run, exact Bellman transport, and a uniform
opponent-survival factor below one.

The game-theoretic capstone is
`quittingEssentialAPS_isUniformEquilibriumPayoff_unique_live`.  It compiles the
same compact functional unique-live, terminal-free stratum to a genuine
uniform-equilibrium payoff by assigning each coarse arc its own finite mesh
length.  Exact block products preserve opponent extinction, while the common
Snell supersolution prevents the local Quit error from accumulating over
calendar time.

The result remains conditional: it does not identify this structural stratum
with every finite quitting game.
-/

-- This umbrella deliberately contains only imports and status documentation.
-- The CI validation branch checks the complete imported capstone transitively.
