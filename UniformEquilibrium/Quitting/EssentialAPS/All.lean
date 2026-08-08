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
import UniformEquilibrium.Quitting.EssentialAPS.Multivalued.ChronologicalSCC

/-!
# Essential APS root, cycle, infinite-run, and uniform-payoff compilers

This umbrella module exposes the finite exact-cycle route, the one-sided
infinite-contraction route, and the multivalued SCC execution route.  The last
one separates finite Flesch graph data from exact singleton-flow segment
witnesses and returns a chronological absorbing exit, a charged recurrent
path, or a typed obstruction.  Its regression shows explicitly why a globally
balanced occupation across closed SCCs is not one executable path.
-/
