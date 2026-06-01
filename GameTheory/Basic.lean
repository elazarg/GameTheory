/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Data.Real.Basic

/-!
# GameTheory.Basic

Tiny shared vocabulary used across the whole library — the kernel-game core,
the solution concepts, and the (otherwise independent) cooperative branch —
without pulling in any of the kernel-game machinery.

Currently this is just `Payoff`. Keep it minimal: anything heavier belongs
in `Core/` or `Foundation`-style infrastructure, not here.
-/

namespace GameTheory

/-- A payoff vector for `ι` players. -/
abbrev Payoff (ι : Type) : Type := ι → ℝ

end GameTheory
