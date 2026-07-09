/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import Mathlib.Data.Real.Basic

/-!
# Euclidean preferences on the real line

This file contains the basic distance-from-peak preference relation shared by
the median-voter and proxy-voting developments.
-/

namespace GameTheory

/-- Euclidean single-peaked preference: agent `i` with ideal point `peak i`
strictly prefers alternative `a` to `b` exactly when `a` is closer to the ideal
point. -/
def Prefers {ι : Type*} (peak : ι → ℝ) (i : ι) (a b : ℝ) : Prop :=
  |a - peak i| < |b - peak i|

end GameTheory
