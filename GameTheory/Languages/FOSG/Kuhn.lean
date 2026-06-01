/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Languages.FOSG.Kuhn.Bridge
import GameTheory.Languages.FOSG.Kuhn.HistoryNative
import GameTheory.Languages.FOSG.Kuhn.ReachableHistory
import GameTheory.Languages.FOSG.Kuhn.ReachableHistoryLemmas
import GameTheory.Languages.FOSG.Kuhn.ReachableHistoryLaw
import GameTheory.Languages.FOSG.Kuhn.StepIndependence
import GameTheory.Languages.FOSG.Kuhn.HistoryMarginal
import GameTheory.Languages.FOSG.Kuhn.TerminalLaw
import GameTheory.Languages.FOSG.Kuhn.ReachableNative

/-!
# Kuhn's Theorem for FOSGs

Umbrella module. The development is split across `Kuhn/`:

- `Kuhn.Bridge` exposes the `ObsModelCore` Kuhn theorems through the FOSG bridge.
- `Kuhn.HistoryNative` / `Kuhn.ReachableHistory*` build the native FOSG
  behavioral/mixed machinery over FOSG histories and reachable histories.
- `Kuhn.StepIndependence`, `Kuhn.HistoryMarginal`, `Kuhn.TerminalLaw`,
  `Kuhn.ReachableNative` assemble the terminal-history laws and the native
  `mixed_to_behavioral` direction.
-/
