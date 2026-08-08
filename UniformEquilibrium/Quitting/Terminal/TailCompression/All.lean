/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Terminal.TailCompression.ElementaryCaps
import UniformEquilibrium.Quitting.Terminal.TailCompression.ElementaryCapEnvelopeIdentities
import UniformEquilibrium.Quitting.Terminal.TailCompression.ElementaryNeverCoupling

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
to prescribed values and nonowner envelopes.  The sharp Never coupling is
charged by the deleted-survival loss
`2 * M * (χ_i(N) - χ_i(∞))`, first for every pure quit time and then for the
literal behavioral supremum.  It closes the positive-joint and unique-positive-
deleted branches.  The resulting capstone selects one cap and cutoff which
simultaneously approximate every prescribed coordinate and every player's
all-behavior best-response envelope.
-/
