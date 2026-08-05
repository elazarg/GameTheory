/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.BlockPairK11DyadicData

/-! # Independently checked first active root of K11 phase 10 -/

namespace GameTheory.BlockPairK11.DyadicCertificate

open Math.Interval

def phaseTenRootZero : DyadicInterval Precision :=
  ⟨64607252271049750494769, 64607276449566142787354⟩

set_option linter.style.nativeDecide false in
theorem phaseTenRootZero_eq : phaseTenRootZero = box 28 := by
  native_decide

end GameTheory.BlockPairK11.DyadicCertificate
