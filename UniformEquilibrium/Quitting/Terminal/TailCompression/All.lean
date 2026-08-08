/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Terminal.TailCompression.ElementaryCaps
import UniformEquilibrium.Quitting.Terminal.TailCompression.ElementaryCapEnvelopeIdentities

/-!
# Finite semantic compression of quitting tails

Public entry point for elementary quitting-tail caps and their survival
classification.  The current layer provides the sure-joint, sure-solo, and
Never grammar, exact finite-prefix laws, the full/deleted-survival trichotomy,
exact Never semantics, and prescribed-value compression in the positive-Never-
mass branch.  It also proves full prescribed/all-behavior semantic density by
sure-joint caps when full and every deleted survival limit vanish.

For a sure-solo cap, the owner's deviation problem is exactly the corresponding
Never problem, while the ordinary full/deleted-survival prefix estimates apply
to prescribed values and nonowner envelopes.  This isolates the only remaining
analytic hinge in the two nonzero-survival branches: a sharp Never-envelope
estimate charged by the loss of deleted survival, rather than by its uncentered
value at the cutoff.

It does not yet prove simultaneous prescribed and all-behavior best-response
approximation in all three survival branches.  The positive-survival
best-response estimate, and hence the capstone combining all three branches,
remain separate obligations.
-/
