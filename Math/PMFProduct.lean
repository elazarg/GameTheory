/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import Math.PMFProduct.Basic
import Math.PMFProduct.Bind
import Math.PMFProduct.Bool
import Math.PMFProduct.CoalitionMass
import Math.PMFProduct.Conditioning
import Math.PMFProduct.Update
import Math.PMFProduct.Independence
import Math.PMFProduct.TotalVariation

/-!
# Independent Product Distributions

Umbrella module. Split across `PMFProduct/`:

- `Basic` — `pmfPi` product distributions and the `Ignores` coordinate algebra.
- `Bind` — bind/factorization and pushforward lemmas.
- `CoalitionMass` — coalition-sum and survival-telescope identities for
  independent Bernoulli marginals.
- `Conditioning` — conditioning and disintegration.
- `Update` — coordinate-update lemmas and coordinate conditioning.
- `Independence` — bind/scalar coordinate independence.
-/
