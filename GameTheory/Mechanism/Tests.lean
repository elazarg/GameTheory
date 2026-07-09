/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Mechanism.Contracts.Basic

/-!
# GameTheory.Mechanism.Tests

Compilation validation entrypoint for mechanism-design modules.
-/

namespace GameTheory.Mechanism.Tests

noncomputable section

example (I : PrincipalAgent Bool Bool) (a : Bool) :
    I.agentUtility (I.linearPayment 1) a = I.socialSurplus a :=
  I.agentUtility_linearPayment_one a

example (I : PrincipalAgent Bool Bool) (a : Bool) :
    I.principalUtility (I.linearPayment 1) a = 0 :=
  I.principalUtility_linearPayment_one a

end

end GameTheory.Mechanism.Tests
