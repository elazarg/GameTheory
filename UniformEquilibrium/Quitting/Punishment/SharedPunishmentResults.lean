/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the LICENSE file.
-/

import UniformEquilibrium.Quitting.Punishment.SharedPunishment
import UniformEquilibrium.Quitting.Classification.ThreePlayer.All

/-!
# Shared-punishment and three-player classification results

This module is the public entrypoint for shared-punishment results in finite
quitting games and for the theorem-bearing three-player classification
umbrella already containing those concrete developments.

* `QuittingSharedPunishment` contains the exact two-player factorization and
  zero shared-excess theorem.
* `QuittingSharedPunishmentThreePlayerClassification` develops a cyclic
  three-player table with exact shared excess `3/4` and classifies all
  minimizing behavior plans and stationary rows.
* `QuittingSharedPunishmentThreePlayerDice` studies the related full-exposure
  Steinhaus--Trybuła table and identifies Never as an exact best reply against
  every committed opponent plan.
* `Quitting.Classification.ThreePlayer.Existence` exposes the unconditional
  three-player quitting-game existence theorem and its precise Solan source
  boundary.

The two-player theorem and the two concrete three-player developments expose
distinct ways in which common punishment departs from coordinatewise
punishment once a third player is present.  The general three-player theorem
is imported through the classification umbrella rather than inferred from
those examples.
-/
