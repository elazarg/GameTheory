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

/-!
# LCP normalization and algebraic classification for finite quitting games

This umbrella exports only theorem-bearing infrastructure proved in this
folder:

* the faithful playerwise solo normalization with explicit nontermination
  payoff;
* exact strategic transport of ordinary terminal approximate-Nash inequalities;
* the standard/projective Q split and projective Q-bar;
* the audit of the printed normal-player recursion together with the corrected
  distinct-witness object; and
* the unconditional algebraic matrix-regime gate with its precise residual
  class.

It deliberately does not export a source-theorem record or a strategic
classification theorem.  The stationary, sunspot, continuous-path, and
absorption-path-to-ordinary implications remain producer obligations until
they are formalized with concrete strategy and path semantics.
-/