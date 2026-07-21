/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Welfare.FolkTheorem.Feasible
import GameTheory.Concepts.Welfare.FolkTheorem.Discounting
import GameTheory.Concepts.Welfare.FolkTheorem.Geometry
import GameTheory.Concepts.Welfare.FolkTheorem.Periodic
import GameTheory.Concepts.Welfare.FolkTheorem.Trigger
import GameTheory.Concepts.Welfare.FolkTheorem.Main

/-!
# Observable-Mixed-Action Discounted Folk Theorem Machinery

Umbrella module. Split across `FolkTheorem/`:

- `Feasible` — feasible / individually-rational payoff sets, opponent minmax
  punishment values, security vectors.
- `Discounting` — finite-cycle averages and patient-player margin lemmas; the
  generic discounted repeated game lives in `Concepts.Repeated.Discounted`.
- `Geometry` — topology and compact inner approximations of feasible,
  individually rational payoff sets.
- `Periodic` — rotation equivalences and periodic discounted continuation bounds.
- `Trigger` — trigger strategies and their discounted-repeated Nash property.
- `Main` — finite-cycle approximation, the discounted Folk theorem, and
  topological properties of the payoff sets.
-/
