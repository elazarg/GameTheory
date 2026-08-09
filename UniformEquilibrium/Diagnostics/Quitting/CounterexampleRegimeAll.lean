/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeOrbitLimit
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeOrbitSelfLoop
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimePacket
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimePacketSurplus
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeQuantitative
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeSearchConsequences
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeSeam
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeSmallPlayers
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTailBridge
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeToggles
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeViolationCollapse

/-!
# Quitting counterexample regime

This is the public umbrella for the combined counterexample normal form, its
canonical prefix-charge capacity, quantitative exact-D restrictions,
search-facing recurrence tests, the conditional bridge from optimized
exact-D tails to punishment-floor prefixes, the membership-toggle and
stationary-cap instability families, emptiness at small player types, orbit
value limits, the floor-violation collapse that makes the extracted optimized
tail's absorption unconditionally summable, its positive-debt all-Continue
self-loop limit, the forced packet's strict refusal defect, and the exact
pure-time/`Never` evaluation interface for periodically restarted tail
windows.
-/
