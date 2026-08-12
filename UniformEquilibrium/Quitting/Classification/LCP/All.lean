/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.Normalization
import UniformEquilibrium.Quitting.Classification.LCP.StrategicTransport
import UniformEquilibrium.Quitting.Classification.LCP.MatrixClasses
import UniformEquilibrium.Quitting.Classification.LCP.NormalCore
import UniformEquilibrium.Quitting.Classification.LCP.NormalCoreStrictnessExample
import UniformEquilibrium.Quitting.Classification.LCP.Gate
import UniformEquilibrium.Quitting.Classification.LCP.FirstLayerSimple
import UniformEquilibrium.Quitting.Classification.LCP.LaterLayerAbnormal
import UniformEquilibrium.Quitting.Classification.LCP.HomogeneousProducer
import UniformEquilibrium.Quitting.Classification.LCP.IsolatedEndpointProducer
import UniformEquilibrium.Quitting.Classification.LCP.OrdinaryNonQProducer
import UniformEquilibrium.Quitting.Classification.LCP.SupportHierarchy
import UniformEquilibrium.Quitting.Classification.LCP.OrdinaryNonQClosure
import UniformEquilibrium.Quitting.Classification.LCP.CounterexampleNecessary

/-!
# LCP normalization and algebraic classification for finite quitting games

This umbrella exports the theorem-bearing infrastructure proved in this folder:

* the faithful playerwise solo normalization with explicit nontermination
  payoff;
* exact strategic transport of ordinary terminal approximate-Nash inequalities;
* the standard/projective Q split and projective Q-bar;
* the audit of the printed normal-player recursion together with the corrected
  distinct-witness object and an explicit quitting table on which its
  stabilized core is strictly smaller than the one-step screen;
* the unconditional algebraic matrix-regime gate with its precise residual
  class; and
* the complete corrected all-abnormal producer, including the later-layer
  two-scale owner/blocker construction;
* the complete corrected homogeneous producer, including both vertex and
  nonvertex simplex witnesses; and
* the complete ordinary non-Q producer, including the all-Continue
  provenance contradiction, the contracting multi-hazard endpoint, and the
  isolated-endpoint blocker repair; and
* the sharp unconditional counterexample restriction: the corrected normal
  core is nonempty, nonhomogeneous, and its principal matrix is textbook
  standard Q (hence also projective Q).

It deliberately does not export a source-theorem record or a completed
strategic classification theorem.  Concrete sunspot semantics, continuous
absorption paths, and the
absorption-path-to-ordinary compiler remain explicit obligations.
-/
