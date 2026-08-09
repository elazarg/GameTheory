/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Analytic.Germ
import UniformEquilibrium.Quitting.Projective.AnalyticFirstEvent
import UniformEquilibrium.Quitting.Projective.AnalyticPacket
import UniformEquilibrium.Quitting.Projective.TargetMismatch
import UniformEquilibrium.Quitting.Projective.SingletonLCP
import UniformEquilibrium.Quitting.Projective.AnchoredSingletonLCP
import UniformEquilibrium.Quitting.Projective.SignedProjectiveLasso
import UniformEquilibrium.Quitting.Projective.WeightedProjectiveLasso
import UniformEquilibrium.Quitting.Projective.SignedProjectiveLassoStrictness
import UniformEquilibrium.Quitting.Projective.SingleSeamProjectiveLasso
import UniformEquilibrium.Quitting.Projective.ForwardBlockSingleSeam
import UniformEquilibrium.Quitting.Projective.FiniteForwardProjectiveLasso
import UniformEquilibrium.Quitting.Projective.PunishmentFloorForwardBudget
import UniformEquilibrium.Quitting.Projective.ResolvedChart
import UniformEquilibrium.Quitting.Projective.Boundary.All
import UniformEquilibrium.Quitting.Debt.Ledger.VanishingChargeRecurrenceNoGo
import Math.FinitePivotOrbit
import Math.CompactFiniteChargedReturn

/-!
# Projective quitting packets and charged-lasso boundary

Public entry point for the proved projective layer:

* exact vanishing-discount quitting-germ algebra;
* matching-order extraction of the normalized cemetery and singleton masses,
  vanishing residual nonsingleton mass, the endpoint value mixture, and
  limiting complementarity as a complete singleton packet;
* the game-generic fixed-target terminal acceptance/rejection specification,
  exposed here only through thin packet-value wrappers;
* the target-mismatch regression: an exact analytic matching branch whose
  positive-cemetery packet value has an explicit quantitative terminal
  rejection witness, while an independently proved sure-exit uniform target
  is available;
* zero-anchor and affine-anchor normalized singleton projective-LCP algebra;
* resolved affine feasibility-or-Farkas duality, together with the explicit
  arc-lifting contract required to turn a feasible tangent into a physical
  successor;
* finite output-or-repeated-label recurrence;
* finite charged return on one fixed compact carrier;
* payload-preserving finite forward packets and their complete compilation to
  single-seam projective lassos and uniform-equilibrium payoffs;
* the game-level alternative between a uniform payoff and one common charge
  bound for every punishment-floor exact forward-orbit prefix;
* the no-go regression showing that repeated labels and compact recurrence do
  not imply a return small relative to a vanishing one-step charge;
* exact characterization of signed monodromy as cyclic-value correction,
  together with pointwise, absolute-weighted, and signed lasso compilation;
* automatic rotation-uniformity for a cycle whose defect is concentrated at
  one closing seam;
* the one-player two-phase regression proving that signed acceptance is
  strictly weaker than absolute-weighted acceptance for a fixed candidate; and
* the converse exact-cycle adapter proving that the corresponding all-accuracy
  existential producer hypotheses remain equivalent.

The arbitrary-game producer is not contained here.  The terminal semantic
layer characterizes exactly what it would mean to accept or reject one fixed
packet value, and the mismatch example proves one concrete rejection.  It does
not select a branch from projective packet, chart, or Farkas data.  Its
conditional retarget adapter assumes target-free uniform-payoff existence and
therefore is not a producer for that existence.

The constructive projective target gate remains open: an accepted packet must
still receive an executable continuation contract, while a rejected packet
must yield a strategically produced retarget, rank descent, chart/Farkas
obstruction, or genuine terminal nonexistence certificate.  Beyond that gate,
the continuing projective branch still requires:

1. construction and coverage of resolved quitting Bellman charts, including
   real/Puiseux arc lifting of feasible lexicographic tangents;
2. semantic decoding of projective Farkas obstructions; and
3. production of arbitrarily charged finite forward packets in one compact
   carrier, or another candidate whose signed monodromy is small relative to
   real absorption, together with a strategic consumer for the complementary
   bounded-charge boundary.

A separate rotation-uniform recurrence theorem is no longer required for an
exact finite forward-packet producer.  Compact finite charged return selects
one block with a small endpoint seam and fixed aggregate absorption; the
forward-block and single-seam compilers supply the lasso and its
rotation-uniformity automatically.  For other upstream candidates, the signed
interface remains the exact acceptance test; it does not by itself produce a
candidate or weaken the all-accuracy exact-cycle obligation.
-/
