/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the LICENSE file.
-/

import GameTheory.Concepts.Stochastic.QuittingSharedPunishment
import GameTheory.Concepts.Stochastic.QuittingSharedPunishmentThreePlayerClassification

/-!
# Shared-punishment results

This module is the public entrypoint for shared-punishment results in finite
quitting games.

* `QuittingSharedPunishment` contains the exact two-player factorization and
  zero shared-excess theorem.
* `QuittingSharedPunishmentThreePlayerClassification` develops a cyclic
  three-player table with exact shared excess `3/4` and classifies all
  minimizing behavior plans and stationary rows.
The two-player theorem and the three-player cyclic example give a sharp
separation: coordinatewise punishment plans can be combined at zero price for
two players, while a common plan can have a strictly positive unavoidable
price for three players.

The related full-exposure table in
`QuittingSharedPunishmentThreePlayerDice` is a separate development: it studies
a different reward and best-reply representation rather than the exact
shared-excess comparison collected here.
-/
