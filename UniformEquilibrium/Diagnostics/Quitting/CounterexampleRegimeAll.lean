/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeOrbitLimit
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeOrbitSelfLoop
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeBallisticity
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeCapCarrier
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeCoalitionLocks
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeDebtConservation
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeKilledTailPotential
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeExactCycleStrata
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeFiniteInstability
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeFloorViolationBudget
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimePacket
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimePacketDefect
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimePacketEnergy
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimePacketSupport
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimePacketSurplus
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeQuantitative
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimePeriodicWindows
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeSearchConsequences
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeSeam
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeSmallPlayers
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTailBridge
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentPacket
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeToggles
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeViolationCollapse
import UniformEquilibrium.Diagnostics.Quitting.FourPlayerSingletonBlocker
import UniformEquilibrium.Diagnostics.Quitting.MinimalFinCounterexample
import UniformEquilibrium.Quitting.AbsorptionPath.CollisionConcentration
import UniformEquilibrium.Quitting.AbsorptionPath.NormalizedFiniteWindowOccupation
import UniformEquilibrium.Quitting.AbsorptionPath.FiniteWindowRefusalReweighting
import UniformEquilibrium.Quitting.AbsorptionPath.SurvivalWeightedObstructionAdapter
import UniformEquilibrium.Quitting.Classification.SingletonPacketDefectAlgebra
import UniformEquilibrium.Quitting.Cycles.PhantomBoundaryLimitGeometry
import UniformEquilibrium.Quitting.Cycles.PeriodicNormalizedSeam
import UniformEquilibrium.Quitting.Debt.Dynamic.DynamicDebtCapChargedAnchorCounterexample
import UniformEquilibrium.Quitting.Debt.Dynamic.PeriodicDebtHolonomy
import UniformEquilibrium.Quitting.Debt.Dynamic.PunishmentFloorCapSplice
import UniformEquilibrium.Quitting.Paths.OutsiderNeverGluing
import UniformEquilibrium.Quitting.Terminal.TailCompression.SummableTailBestResponse

/-!
# Quitting counterexample regime

This is the public umbrella for the combined counterexample normal form, its
canonical prefix-charge capacity, quantitative exact-D restrictions,
search-facing recurrence tests, the exact bridge from optimized exact-D tails
to punishment-floor prefixes, the membership-toggle and
stationary-cap instability families, support dynamics of the forced packet,
canonical minimal finite counterexamples, emptiness at small player types,
orbit value limits, quantitative floor-violation budgets, the collapse that
makes the extracted optimized tail's absorption unconditionally summable,
its positive-debt all-Continue self-loop limit, and exact evaluation of
periodically restarted tail windows.  The optimized tail additionally carries
exact finite and infinite debt conservation, a logarithmic owner-clock bound,
the positive phantom-plateau theorem, closed augmented-cap membership in the
global floor carrier, and a canonical periodic-window family whose player and
refusal/phase obstruction stabilize on an infinite set.  The forced packet's
noncomplementarity has one uniform compact refusal margin across all normalized
packets of the fixed table.  Stable pure quitting coalitions independently
generate unbounded canonical prefix charge, linking the sure-exit and capacity
screens.  The umbrella also exports the augmented-cap splice
interface and the finite regressions delimiting singleton complementarity and
cap-only arguments.

Every unaugmented value on the optimized tail already dominates the behavioral
punishment floor, so every finite chronological tail segment reverses to a
legal exact floor prefix with the same charge.  The tail is also uniformly
ballistic in absorption time: after one date, every positive-absorption window
has endpoint distance at least one fixed positive multiple of its absorbed
mass.  Thus no late window closes at little-o of charge scale.  This does not
produce recurrence; finite total charge permits a bounded ballistic approach
to the limiting all-Continue state.  The signed normalization is retained
more precisely: either the tail is eventually literally all-Continue, or
positive one-stage windows extract a nonzero charge-tangent packet from the
same roots.  Its remaining finite sign dispatch is a negative coordinate or,
after excluding all negative coordinates, a positive active-owner coordinate.
The corresponding phase-repair and support-enlargement consumers remain open.

Independently of that selected-tail geometry, reward-table closure gives a
robust finite-cycle restriction: a hypothetical counterexample has one
positive-radius reward neighborhood containing no punishment-admissible exact
cycle of any period.  For a fixed root cycle, a common own-set reward shift is
governed by an exact finite global feedback system.  On an absorbing cycle its
value correction is unique, its unit multipliers lie on probability scale,
and the system eliminates player by player.  This does not prove density of
solved-cycle strata or show that own-set shifts exhaust general reward-table
perturbations.

For proper-face arguments, the umbrella exports an original-coordinate
outsider-`Never` estimate.  If the outsider's live continuation is at most
`eta` below its solo reward and insider absorption is at most `delta` at every
date, every behavioral deviation gains at most `eta + 2*M*delta` over literal
`Never`.  The theorem does not derive either quantitative premise from a
restricted equilibrium.

The umbrella also exports the general summable-tail boundary geometry used by
the regime: an explicit remaining-charge bound on literal behavioral best
responses, simultaneous annotation convergence with an active-owner pinning
criterion, and the scalar phase/refusal algebra that separates underfunding
from punishment-floor failure.  None of these results identifies the forced
packet with a tail occupation or realizes an augmented cap as a suffix.
At the local dynamic-debt level, vanishing of the named diagonal seam is
exactly the criterion for the displayed root to lift to a Nash--Bellman edge
between augmented caps; the umbrella does not assert that this criterion holds
along the optimized tail.
Playerwise dynamic debt is also exported as an exact killed-potential
reference account.  An excessive account with the same initial value can
dissipate only by losing the corresponding surviving boundary: boundary
dominance is equivalent to zero total killed dissipation, forces every
positively reached local dissipation to vanish, and strict dissipation forces
strict boundary shortfall.  The counterexample
regime does not supply that boundary dominance, so this accounting theorem
does not erase the positive phantom plateau.
Product-root collision mass is at most `choose (card ι) 2` times squared
one-stage absorption.  The exported weighted-window concentration theorem has
a separate zero-absorption branch; its conditional singleton-mixture payoff
comparison applies when both absorption and singleton mass are positive.
On a supplied finite exact-debt window, a positive debt coordinate that returns
to its initial value forces every opponent to Continue throughout.  Two
distinct returning positive coordinates make the entire window all-Continue,
so an absorbing return can carry at most one such coordinate.
The forced packet's weighted surplus is a quadratic form depending only on the
symmetric reciprocal part of the singleton solo-effect matrix.  Consequently
every counterexample packet supports a pair with positive reciprocal solo
effect; if all reciprocal pair sums are nonpositive, the complementary-mixture
compiler supplies a uniform payoff.
Canonical source-typed finite windows now retain normalized singleton owner
occupation, collision mass, and full absorbing delivery.  Late collision
vanishes at the product-law rate, and positive limiting owner occupation pins
the annotation boundary directly.  Normalizing the singleton mixture by total
absorption gives a collision error bound without a positive singleton-mass
premise.  Refusal conditioning uses a different
deleted-player survival law; its normalized discrepancy is explicitly bounded
by the chronological reweighting error divided by a positive deleted-absorption
denominator.  No theorem here makes that ratio vanish for the canonical
windows.
Adjacent source windows also form exact survival-weighted obstruction blocks:
singleton and collision charge in the later window is killed by the earlier
joint-survival factor, while endpoint displacement is an unweighted
coboundary.  This makes normalized tangent composition explicit, but does not
yet supply a strategically feasible raw-current family or a compatible
co-state.

Periodic attachment has a second, exact normalization fence.  For an
absorbing exact Nash--Bellman word, the finite-stop and refusal branches of
the literal periodic best-response envelope are controlled by endpoint drift
divided by the joint and opponent survival gaps.  Ordinary endpoint
convergence does not imply these normalized ratios vanish; on the optimized
counterexample tail the joint-absorption ratio is eventually bounded away
from zero in endpoint-distance scale.  In the refusal branch, positive debt
can survive precisely in this normalization, so a
tail-derived singleton packet and a phantom plateau need not contradict one
another even after occupation identification.  The isolated
opponent-survival-one branch remains the separately classified negative-solo
exception.
-/
