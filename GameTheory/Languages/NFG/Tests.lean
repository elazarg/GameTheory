/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Languages.NFG.Examples
import GameTheory.Languages.NFG.CountableExample

/-!
# GameTheory.Languages.NFG.Tests

Compilation validation entrypoint for normal-form games.

Reader-facing worked examples belong in `GameTheory.Languages.NFG.Examples`.
-/

namespace NFG.Tests

noncomputable section

example : IsNashPure prisonersDilemma pd_defect_defect :=
  pd_defect_is_nash

example : ¬ IsNashPure prisonersDilemma pd_coop_coop :=
  pd_coop_not_nash

example :
    prisonersDilemma.toKernelGame.outcomeKernel pd_defect_defect =
      PMF.pure (prisonersDilemma.outcome pd_defect_defect) :=
  rfl

example : prisonersDilemma.toKernelGame.IsNash pd_defect_defect :=
  (IsNashPure_iff_kernelGame _ _).mp pd_defect_is_nash

example : IsNashPure natChoose natChoose_zero :=
  natChoose_zero_is_nash

example : IsDominant natChoose 0 0 :=
  natChoose_zero_dominant_0

end

end NFG.Tests
