/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Languages.FOSG.ReachableHistory
import GameTheory.Languages.FOSG.Native

/-!
# Kuhn's Theorem for FOSGs

Umbrella module. The development is split by phase:

- `Native.History` exposes the generic `ObsModelCore` Kuhn theorems through
  FOSG execution-state names.
- `ReachableHistory` builds the reachable-history model and the legal/reachable
  strategy conversion facts used by native FOSG Kuhn.
- `Native` contains the native FOSG marginal, terminal-law, and reachable
  terminal-law corollaries.
-/
