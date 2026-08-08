/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the LICENSE file.
-/

import UniformEquilibrium.Quitting.Punishment.SharedPunishment
import UniformEquilibrium.Quitting.Classification.ThreePlayer.SharedPunishmentThreePlayerClassification
import UniformEquilibrium.Quitting.Classification.ThreePlayer.SharedPunishmentThreePlayerDice

/-!
# Shared-punishment results

This module is the public entrypoint for shared-punishment results in finite
quitting games.

* `QuittingSharedPunishment` contains the exact two-player factorization and
  zero shared-excess theorem.
* `QuittingSharedPunishmentThreePlayerClassification` develops a cyclic
  three-player table with exact shared excess `3/4` and classifies all
  minimizing behavior plans and stationary rows.
* `QuittingSharedPunishmentThreePlayerDice` studies the related full-exposure
  Steinhaus--Trybuła table and identifies Never as an exact best reply against
  every committed opponent plan.

The two-player theorem and the two three-player developments expose distinct
ways in which common punishment departs from coordinatewise punishment once a
third player is present.
-/
