/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Examples.BlockPair.K11DyadicData

/-! # Independently checked K11 phase group 3--5 -/

namespace GameTheory.BlockPairK11.DyadicCertificate

open LocalInterval

opaque phaseGroupThreeFive : Vector (LocalPhaseData Precision) 3 :=
  Vector.ofFn ![
    buildLocalPhaseData box 3,
    buildLocalPhaseData box 4,
    buildLocalPhaseData box 5
  ]

set_option linter.style.nativeDecide false in
theorem phaseGroupThreeFive_eq : phaseGroupThreeFive = Vector.ofFn ![
    buildLocalPhaseData box 3,
    buildLocalPhaseData box 4,
    buildLocalPhaseData box 5
  ] := by
  native_decide

end GameTheory.BlockPairK11.DyadicCertificate
