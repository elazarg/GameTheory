/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Examples.BlockPair.K11DyadicData

/-! # Independently checked K11 phase group 0--2 -/

namespace GameTheory.BlockPairK11.DyadicCertificate

open LocalInterval

opaque phaseGroupZeroTwo : Vector (LocalPhaseData Precision) 3 := Vector.ofFn ![
  buildLocalPhaseData box 0,
  buildLocalPhaseData box 1,
  buildLocalPhaseData box 2
]

set_option linter.style.nativeDecide false in
theorem phaseGroupZeroTwo_eq : phaseGroupZeroTwo = Vector.ofFn ![
    buildLocalPhaseData box 0,
    buildLocalPhaseData box 1,
    buildLocalPhaseData box 2
  ] := by
  native_decide

end GameTheory.BlockPairK11.DyadicCertificate
