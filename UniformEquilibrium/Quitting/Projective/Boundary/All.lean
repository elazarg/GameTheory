/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Projective.Boundary.PacketTargetSemantics
import UniformEquilibrium.Quitting.Projective.Boundary.TargetMismatchRegression

/-!
# Projective fixed-target semantic adapters

This narrow umbrella exports:

* the thin specialization of the game-generic terminal target semantics to a
  normalized singleton packet's stored value; and
* the explicit analytic target-mismatch rejection and sure-exit replacement
  regression.

It does not decide the semantic alternative from projective data, construct an
executable cemetery continuation, convert a rejection witness into a chart or
Farkas obstruction, produce a monotone retarget, or prove termination of
repeated retargeting.  Those constructive projective obligations remain open.
-/
