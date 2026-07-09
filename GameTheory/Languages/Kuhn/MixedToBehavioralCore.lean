/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Languages.Kuhn.MixedToBehavioralCore.ReachFactor
import GameTheory.Languages.Kuhn.MixedToBehavioralCore.CoreKuhnSemantic

/-! # Mixed-to-behavioral realization on `KuhnModel`

Umbrella module. Split across `MixedToBehavioralCore/`:

- `ReachFactor` — correlated realization for mixed plan distributions, the
  reach-factoring core, and the observation-local Kuhn step.
- `CoreKuhnSemantic` — semantic step mass/support and locality conditions and
  the core theorem `ObsModelCore.kuhn_mixed_to_behavioral_semantic`.

The stronger `ObsModel` layer and syntactic recall corollaries live in
`CorrelatedRealization.lean`.
-/
