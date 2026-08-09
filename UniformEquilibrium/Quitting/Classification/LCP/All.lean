/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.Normalization
import UniformEquilibrium.Quitting.Classification.LCP.StrategicTransport
import UniformEquilibrium.Quitting.Classification.LCP.MatrixClasses
import UniformEquilibrium.Quitting.Classification.LCP.NormalCore
import UniformEquilibrium.Quitting.Classification.LCP.Gate
import UniformEquilibrium.Quitting.Classification.LCP.FirstLayerSimple

/-!
# LCP normalization and algebraic classification for finite quitting games

This umbrella exports the theorem-bearing infrastructure proved in this folder:

* the faithful playerwise solo normalization with explicit nontermination
  payoff;
* exact strategic transport of ordinary terminal approximate-Nash inequalities;
* the standard/projective Q split and projective Q-bar;
* the audit of the printed normal-player recursion together with the corrected
  distinct-witness object;
* the unconditional algebraic matrix-regime gate with its precise residual
  class; and
* a concrete producer for the strict subcase in which the first corrected
  normal layer is empty: an exact stationary terminal Nash profile whose own
  terminal payoff is directly a uniform-equilibrium payoff.

It deliberately does not export a source-theorem record or a completed
strategic classification theorem.  The later-layer all-abnormal construction,
homogeneous and non-Q stationary producers, concrete sunspot semantics,
continuous absorption paths, and the absorption-path-to-ordinary compiler
remain explicit obligations.
-/
