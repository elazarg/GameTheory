/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauMarkedExitNashificationRegression

/-!
# Iterated reset does not turn a marked collision into a cycle

At a marked collision row, the marked coordinate can have zero local Nash
defect while the other-player defect is positive.  Finiteness of the player
set then makes it tempting to reset a positive-defect opponent, repeat, and
read player-label recurrence as a sure-exit or toggle cycle.

The two-player marked-exit regression already rules out that inference.  This
module records the complete asynchronous best-response chain.  Starting from
the sure collision, resetting the unmarked player to its unique pure best
response transfers the whole unit defect to the formerly marked player and
kills the collision.  Resetting that player next kills the remaining defect
and reaches all-Continue.  The root is now exact Nash but has zero absorption.

Thus the reset sequence does make progress on *local* defect, but it does not
retain the collision, a sure-exit row, or an absorbing cycle.  A player-label
recurrence argument needs a state/edge invariant strong enough to survive
each reset; finiteness alone supplies no such invariant.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

namespace QuittingMarkedExitNashificationRegression

/-- First asynchronous reset: the unmarked player switches from sure Quit to
its unique pure best response, Continue. -/
def firstResetRoot : Bool → PMF Bool :=
  Function.update markedCollisionRoot true (PMF.pure false)

/-- Second asynchronous reset: the formerly marked player now also switches
from sure Quit to Continue. -/
def secondResetRoot : Bool → PMF Bool :=
  Function.update firstResetRoot false (PMF.pure false)

/-- The first reset has the expected pure-action coordinates. -/
theorem firstResetRoot_probabilities :
    (firstResetRoot false true).toReal = 1 ∧
      (firstResetRoot true true).toReal = 0 := by
  simp [firstResetRoot, markedCollisionRoot]

/-- The second reset is literally the all-Continue root. -/
theorem secondResetRoot_eq_allContinue :
    secondResetRoot = (quittingAllContinueRoot : Bool → PMF Bool) := by
  funext who
  cases who <;> simp [secondResetRoot, firstResetRoot,
    quittingAllContinueRoot]

/-- At the collision row, the unmarked player carries the whole unit local
defect. -/
theorem markedCollisionRoot_unmarked_coordinateNashDefect :
    quittingRootCoordinateNashDefect reward tail markedCollisionRoot true = 1 := by
  rw [quittingRootCoordinateNashDefect,
    quittingRootSuccessorPayoff_eq_endpointMix,
    quitPayoff_true, continuePayoff_true]
  norm_num [markedCollisionRoot]

/-- Resetting the unmarked player eliminates its own local defect. -/
theorem firstResetRoot_unmarked_coordinateNashDefect :
    quittingRootCoordinateNashDefect reward tail firstResetRoot true = 0 := by
  rw [quittingRootCoordinateNashDefect,
    quittingRootSuccessorPayoff_eq_endpointMix,
    quitPayoff_true, continuePayoff_true]
  norm_num [firstResetRoot, markedCollisionRoot]

/-- The first reset transfers the whole unit local defect to the formerly
marked player. -/
theorem firstResetRoot_marked_coordinateNashDefect :
    quittingRootCoordinateNashDefect reward tail firstResetRoot false = 1 := by
  rw [quittingRootCoordinateNashDefect,
    quittingRootSuccessorPayoff_eq_endpointMix,
    quitPayoff_false, continuePayoff_false]
  norm_num [firstResetRoot, markedCollisionRoot]

/-- The first reset kills the displayed collision atom. -/
theorem firstResetRoot_collisionMass :
    quittingRootCoalitionMass firstResetRoot (Finset.univ : Finset Bool) = 0 := by
  unfold quittingRootCoalitionMass
  have hcomp : (Finset.univ : Finset Bool)ᶜ = ∅ := by
    ext who
    simp
  rw [coalitionMass, hcomp]
  simp [quittingRootQuitRates, firstResetRoot, markedCollisionRoot]

/-- After both strict best-response switches, every coordinate has zero local
defect. -/
theorem secondResetRoot_coordinateNashDefect (who : Bool) :
    quittingRootCoordinateNashDefect reward tail secondResetRoot who = 0 := by
  rw [secondResetRoot_eq_allContinue]
  cases who
  · rw [quittingRootCoordinateNashDefect,
      quittingRootSuccessorPayoff_eq_endpointMix,
      quitPayoff_false, continuePayoff_false]
    norm_num [quittingAllContinueRoot]
  · rw [quittingRootCoordinateNashDefect,
      quittingRootSuccessorPayoff_eq_endpointMix,
      quitPayoff_true, continuePayoff_true]
    norm_num [quittingAllContinueRoot]

/-- The reset endpoint is exact endpoint Nash. -/
theorem secondResetRoot_isExactEndpointNash :
    IsεQuittingRootEndpointNash reward tail 0 secondResetRoot := by
  rw [secondResetRoot_eq_allContinue]
  intro who
  cases who
  · rw [endpointDifference_false]
    norm_num [quittingAllContinueRoot]
  · rw [endpointDifference_true]
    norm_num [quittingAllContinueRoot]

/-- The exact-Nash endpoint of the reset chain is nonabsorbing. -/
theorem secondResetRoot_absorptionMass :
    quittingRootAbsorptionMass secondResetRoot = 0 := by
  rw [secondResetRoot_eq_allContinue,
    quittingRootAbsorptionMass_allContinueRoot]

/-- **Reset-chain regression headline.**

The two strict asynchronous best-response switches transform defect vector
`(0,1)` into `(1,0)` and then `(0,0)`.  At the same time the collision mass
falls from one to zero and the terminal exact-Nash root has zero absorption.
This is a finite, fully co-realized counterexample to deriving an absorbing
cycle from recurrence of reset-player labels alone. -/
theorem iterated_bestResponseReset_transfers_then_kills_defect :
    quittingRootCoordinateNashDefect reward tail markedCollisionRoot false = 0 ∧
    quittingRootCoordinateNashDefect reward tail markedCollisionRoot true = 1 ∧
    quittingRootCoalitionMass markedCollisionRoot
        (Finset.univ : Finset Bool) = 1 ∧
    quittingRootCoordinateNashDefect reward tail firstResetRoot false = 1 ∧
    quittingRootCoordinateNashDefect reward tail firstResetRoot true = 0 ∧
    quittingRootCoalitionMass firstResetRoot
        (Finset.univ : Finset Bool) = 0 ∧
    (∀ who, quittingRootCoordinateNashDefect reward tail secondResetRoot who = 0) ∧
    IsεQuittingRootEndpointNash reward tail 0 secondResetRoot ∧
    quittingRootAbsorptionMass secondResetRoot = 0 := by
  exact ⟨markedCollisionRoot_marked_coordinateNashDefect,
    markedCollisionRoot_unmarked_coordinateNashDefect,
    markedCollisionRoot_collisionMass,
    firstResetRoot_marked_coordinateNashDefect,
    firstResetRoot_unmarked_coordinateNashDefect,
    firstResetRoot_collisionMass,
    secondResetRoot_coordinateNashDefect,
    secondResetRoot_isExactEndpointNash,
    secondResetRoot_absorptionMass⟩

end QuittingMarkedExitNashificationRegression

end GameTheory
