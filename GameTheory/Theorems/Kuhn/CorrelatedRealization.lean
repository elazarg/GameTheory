/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Theorems.Kuhn.CorrelatedRealization.ObsLevel
import GameTheory.Theorems.Kuhn.CorrelatedRealization.ReachFactor
import GameTheory.Theorems.Kuhn.CorrelatedRealization.ProductPreservation
import GameTheory.Theorems.Kuhn.CorrelatedRealization.ObsLocality
import GameTheory.Theorems.Kuhn.CorrelatedRealization.Hierarchy

/-! # Correlated realization and Kuhn M→B wrappers

Umbrella module. Split across `CorrelatedRealization/`:

- `ObsLevel` — observation-level correlated realization wrappers.
- `ReachFactor` — pureRun reachability bridge and reach factoring under PSAR.
- `ProductPreservation` — product / coordination preservation.
- `ObsLocality` — observation-locality of per-player consistency and the
  generalized M→B step.
- `Hierarchy` — semantic vs. syntactic recall conditions and the public
  `ObsModel`-surface Kuhn M→B theorem hierarchy.
-/
