/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingEssentialAPSCycle
import GameTheory.Concepts.Stochastic.QuittingEssentialAPSRegression
import GameTheory.Concepts.Stochastic.QuittingEssentialAPSCompactFixedPoint

/-!
# Essential APS for the quitting singleton-flow stratum

Umbrella import for the exact successor graph, the owner-indexed essential APS
operator, its carrier-restricted greatest fixed point, convex-fiber,
unique-successor, total bounded-window circuit progress extraction, compact
fixed fibers on compact unique-successor carriers, the zero-mass regression,
and the supplied finite proper-cycle compiler.

The implementation is deliberately conditional: it certifies the continuous
one-randomizer-at-a-time stratum and does not identify that stratum with all
quitting-game equilibria.
-/
