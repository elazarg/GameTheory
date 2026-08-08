/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.RealizedMarkedAbsorptionCylinder

/-!
# Finite absorption-path realization layer

Public entry point for the source-retaining finite semantics used by the marked
absorption-path program.  It exports the exact coalition-mass accounting,
bounded chronological samples, free terminal-continuation evaluation, and
same-source concatenation laws of `RealizedMarkedAbsorptionCylinder`.

This layer is not the source-forgetting compact cylinder, generalized completed
trace carrier, or repair decoder.  Those objects require a marked chronological
obstacle graph, independent packet/provenance coordinates, exact finite seam
pullback, and an all-length repair theorem.
-/
