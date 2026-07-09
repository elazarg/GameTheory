/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Semantics.TransitionTrace
import Semantics.Simulation

/-!
# Semantics.Tests

Compilation validation entrypoint for generic transition semantics.
-/

namespace Semantics.Tests

open Semantics.Transition

def incStep (_ : PUnit) (s t : Nat) : Prop :=
  t = s + 1

def incTrace : ReachActionTraceFrom incStep 0 [PUnit.unit, PUnit.unit] [0, 1, 2] :=
  ReachActionTraceFrom.snoc
    (ReachActionTraceFrom.snoc ReachActionTraceFrom.nil rfl rfl)
    rfl
    rfl

example : ReachBy incStep [PUnit.unit, PUnit.unit] 0 2 :=
  incTrace.toReachBy rfl

example : ReachStateTraceFrom incStep 0 [0, 1, 2] :=
  incTrace.toReachStateTrace

example : [0, 1, 2].length = [PUnit.unit, PUnit.unit].length + 1 :=
  incTrace.length_states_eq_succ_actions

def identitySimulation : HomSimulation incStep incStep where
  stateMap := id
  labelMap := id
  step := fun h => h

example :
    ReachBy incStep [PUnit.unit, PUnit.unit] 0 2 :=
  identitySimulation.reachBy_map (incTrace.toReachBy rfl)

end Semantics.Tests
