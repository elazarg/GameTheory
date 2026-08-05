/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.BlockPairK11DyadicData

/-! # Independently checked second active root of K11 phase 10 -/

namespace GameTheory.BlockPairK11.DyadicCertificate

open Math.Interval

def phaseTenRootOne : DyadicInterval Precision :=
  ⟨15718699880824927933521, 15718724059341320226105⟩

set_option linter.style.nativeDecide false in
theorem phaseTenRootOne_eq : phaseTenRootOne = box 29 := by
  native_decide

end GameTheory.BlockPairK11.DyadicCertificate
