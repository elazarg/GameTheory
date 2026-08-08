/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Examples.BlockPair.K11DyadicData

/-! # Independently checked K11 phase 9 -/

namespace GameTheory.BlockPairK11.DyadicCertificate

open LocalInterval

opaque phaseNine : LocalPhaseData Precision :=
  buildLocalPhaseData box 9

set_option linter.style.nativeDecide false in
theorem phaseNine_eq : phaseNine = buildLocalPhaseData box 9 := by
  native_decide

end GameTheory.BlockPairK11.DyadicCertificate
