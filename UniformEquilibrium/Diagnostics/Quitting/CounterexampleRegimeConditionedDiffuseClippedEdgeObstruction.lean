/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeConditionedDiffuseFloorClip

/-!
# State matching obstruction for clipped reset edges

The floor-clipped reset certificate has a fixed tail simplex coordinate:
every such edge has tail `(target, quittingAllContinueSimplexRoot)`.  The
predecessor root is allowed to have positive absorption.  Consequently two
certificates of this form cannot be concatenated at a positive-charge edge:
matching the first current state to the second tail state would force the
first root to be all-Continue, whose absorption mass is zero.

This is a state-space obstruction, independent of compactness or closedness.
It identifies the missing datum in any chronological reset argument: the next
target must be selected with the preceding root simplex coordinate, rather
than merely with a fresh all-Continue tail.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

namespace ClippedStateMatchingObstruction

omit [DecidableEq ι] in
theorem positive_absorption_current_ne_allContinue_tail
    {current : QuittingNashBellmanPoint ι}
    {target : Payoff ι}
    {predecessor : Payoff ι}
    {root : QuittingRootSimplex ι}
    (hcurrent : current = (predecessor, root))
    (htail : (target, quittingAllContinueSimplexRoot) = current)
    (hpositive : 0 < quittingRootAbsorptionMass
      (quittingRootOfSimplex root)) : False := by
  have hroot : root = quittingAllContinueSimplexRoot := by
    have hsnd := congrArg Prod.snd htail
    simpa [hcurrent] using hsnd.symm
  have hrootOf : quittingRootOfSimplex root =
      (quittingAllContinueRoot : ι → PMF Bool) := by
    rw [hroot]
    exact quittingRootOfSimplex_allContinueSimplexRoot
  rw [hrootOf, quittingRootAbsorptionMass_allContinueRoot] at hpositive
  linarith

omit [DecidableEq ι] in
theorem no_composable_positive_absorption_clipped_edges
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {current tail nextTail : QuittingNashBellmanPoint ι}
    {target : Payoff ι}
    {predecessorRoot : QuittingRootSimplex ι}
    (hfirstCurrent : current =
      (quittingRootSuccessorPayoff reward tail.1
        (quittingRootOfSimplex predecessorRoot), predecessorRoot))
    (hfirstPositive : 0 < quittingRootAbsorptionMass
      (quittingRootOfSimplex predecessorRoot))
    (hnextTail : nextTail =
      (target, quittingAllContinueSimplexRoot))
    (hmatch : current = nextTail) : False := by
  have htail : (target, quittingAllContinueSimplexRoot) = current :=
    hnextTail.symm.trans hmatch.symm
  apply positive_absorption_current_ne_allContinue_tail
    hfirstCurrent htail hfirstPositive

end ClippedStateMatchingObstruction

end GameTheory
