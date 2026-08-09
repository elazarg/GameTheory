/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.RealizedMarkedAbsorptionCylinder
import UniformEquilibrium.Quitting.AbsorptionPath.MarkedObstacleRecord
import UniformEquilibrium.Quitting.AbsorptionPath.MarkedAbsorptionCylinder

/-!
# Finite absorption-path semantic layer

Public entry point for the finite semantics used by the marked absorption-path
program.  `RealizedMarkedAbsorptionCylinder` retains the calibrated source and
exports exact coalition-mass accounting, bounded chronological samples, free
terminal-continuation evaluation, and same-source concatenation laws.
`MarkedObstacleRecord` forgets that source after encoding one stage while
retaining the factor, survival, Bellman, and obstacle coordinates needed by a
completed chronological graph.  `MarkedAbsorptionCylinder` is the finite
source-free graph: its complete carrier is associative, the realized encoder
commutes exactly with adjacent block concatenation, and semantic coherence is
preserved by exact-anchor splicing.

This layer is not the generalized completed-trace carrier or repair decoder.
Those objects still require compact completion of the marked chronological
graph, a provenance convention for extensionally identical stages, continuous
projection laws, completed `Never` semantics, and any finite seam pullback
needed by surgery.
-/
