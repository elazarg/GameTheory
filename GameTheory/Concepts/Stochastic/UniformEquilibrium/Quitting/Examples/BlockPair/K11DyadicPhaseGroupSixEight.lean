/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Examples.BlockPair.K11DyadicData

/-! # Independently checked K11 phase group 6--8 -/

namespace GameTheory.BlockPairK11.DyadicCertificate

open LocalInterval

opaque phaseGroupSixEight : Vector (LocalPhaseData Precision) 3 :=
  Vector.ofFn ![
    buildLocalPhaseData box 6,
    buildLocalPhaseData box 7,
    buildLocalPhaseData box 8
  ]

set_option linter.style.nativeDecide false in
theorem phaseGroupSixEight_eq : phaseGroupSixEight = Vector.ofFn ![
    buildLocalPhaseData box 6,
    buildLocalPhaseData box 7,
    buildLocalPhaseData box 8
  ] := by
  native_decide

end GameTheory.BlockPairK11.DyadicCertificate
