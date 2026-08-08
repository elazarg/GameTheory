/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Terminal.TailCompression.ElementaryCaps

/-!
# Finite semantic compression of quitting tails

Public entry point for elementary quitting-tail caps and their survival
classification.  The current layer provides the sure-joint, sure-solo, and
Never grammar, exact finite-prefix laws, the full/deleted-survival trichotomy,
exact Never semantics, and prescribed-value compression in the positive-Never-
mass branch.  It also proves full prescribed/all-behavior semantic density by
sure-joint caps when full and every deleted survival limit vanish.

It does not yet prove simultaneous prescribed and all-behavior best-response
approximation in all three survival branches.  The positive-survival
best-response estimate and the exceptional sure-solo branch remain separate
obligations.
-/
