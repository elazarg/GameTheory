/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Theorems.Kuhn.BehavioralToMixed
import GameTheory.Languages.Kuhn
import GameTheory.Theorems.Kuhn.CorrelatedRealization

/-!
# GameTheory.Theorems.Kuhn

Kuhn's theorem: behavioral and mixed strategy equivalence.

The semantic core lives on `KuhnModel`/`ObsModelCore`:
- **B→M** (`ObsModelCore.kuhn_behavioral_to_mixed` in
  `BehavioralToMixedCore.lean`): no recall needed, but requires the semantic
  horizon-separation condition used to fold sequential randomization into an
  ex-ante product distribution.
- **M→B** (`ObsModelCore.kuhn_mixed_to_behavioral_semantic` in
  `MixedToBehavioralCore.lean`): stated over semantic step/locality
  assumptions.

`ObsModel` is the stronger snapshot-refined compatibility layer. It is
useful when a client naturally has faithful observation-history snapshots and
wants syntactic recall corollaries such as
`kuhn_mixed_to_behavioral_pspr` or automatic `HorizonSeparation`.

This file re-exports the Kuhn model, the core theorems, the migration wrappers,
and the generic outcome-equality schema types used by language-specific Kuhn
reductions.
-/
