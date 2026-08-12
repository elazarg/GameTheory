/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.CapDebtBellmanReduction
import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.IdealSingletonCapDebtLasso
import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.IdealSingletonBlockApproximation
import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.CyclicLabelAdapter
import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.IdealSingletonCarrierBridge
import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.IdealSingletonZeroRetentionCarrier
import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.AmbientCarrierElimination

/-!
# Three-element corrected-core elimination

This umbrella exports the exact cap-debt recursion, diffuse singleton-block
carrier construction, cyclic relabeling, and the resulting elimination of the
three-element corrected-core counterexample branch.
-/
