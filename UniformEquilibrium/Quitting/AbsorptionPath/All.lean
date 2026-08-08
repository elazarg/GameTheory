/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.RealizedMarkedAbsorptionCylinder
import UniformEquilibrium.Quitting.AbsorptionPath.MarkedObstacleRecord

/-!
# Finite absorption-path semantic layer

Public entry point for the finite semantics used by the marked absorption-path
program.  `RealizedMarkedAbsorptionCylinder` retains the calibrated source and
exports exact coalition-mass accounting, bounded chronological samples, free
terminal-continuation evaluation, and same-source concatenation laws.
`MarkedObstacleRecord` forgets that source after encoding one stage while
retaining the factor, survival, Bellman, and obstacle coordinates needed by a
future completed chronological graph.

This layer is not the source-forgetting block cylinder, generalized completed
trace carrier, or repair decoder.  Those objects still require a compact marked
chronological obstacle graph, independent packet/provenance coordinates, exact
finite seam pullback, and an all-length repair theorem.
-/
