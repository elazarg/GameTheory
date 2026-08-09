/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeOrbitLimit
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeOrbitSelfLoop
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeCapCarrier
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeCoalitionLocks
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeDebtConservation
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeFiniteInstability
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeFloorViolationBudget
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimePacket
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimePacketDefect
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimePacketSupport
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimePacketSurplus
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeQuantitative
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimePeriodicWindows
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeSearchConsequences
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeSeam
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeSmallPlayers
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTailBridge
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeToggles
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeViolationCollapse
import UniformEquilibrium.Diagnostics.Quitting.FourPlayerSingletonBlocker
import UniformEquilibrium.Diagnostics.Quitting.MinimalFinCounterexample
import UniformEquilibrium.Quitting.Debt.Dynamic.DynamicDebtCapChargedAnchorCounterexample
import UniformEquilibrium.Quitting.Debt.Dynamic.PunishmentFloorCapSplice

/-!
# Quitting counterexample regime

This is the public umbrella for the combined counterexample normal form, its
canonical prefix-charge capacity, quantitative exact-D restrictions,
search-facing recurrence tests, the conditional bridge from optimized
exact-D tails to punishment-floor prefixes, the membership-toggle and
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
-/
