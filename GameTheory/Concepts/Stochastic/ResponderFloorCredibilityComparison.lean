/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Responder-floor comparison from unilateral credibility

This file isolates the value comparison underlying the implication from
responder credibility to the responder-floor condition in Question 110.

For a responder strategy `response` and a coalition strategy `coalition`, let
`floorPayoff response coalition` be the payoff in the floor game and let
`responsePayoff response coalition` be the payoff in the actual response
game.  If the floor payoff is pointwise no larger than the response payoff,
then, against any fixed prescribed coalition strategy,

`sup_response inf_coalition floorPayoff`

is no larger than

`sup_response responsePayoff response prescribedCoalition`.

Consequently, a unilateral credibility bound on the latter value implies the
same bound on the security floor.  The proof records the load-bearing facts
explicitly: the same responder strategy type is used in both games, the fixed
prescribed coalition strategy is an admissible floor-game coalition strategy,
and the payoff comparison holds for every strategy pair.

The repository does not yet contain Question 110's finite turn-based
absorbing response arena and its derived floor game.  This module therefore
formalizes only the reusable strategy-level comparison, without introducing
an architecture interface ahead of that model.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace ResponderFloorComparison

variable {ResponderStrategy CoalitionStrategy : Type*}

/-- The responder's maximin value in the floor game. -/
def securityFloor
    (floorPayoff : ResponderStrategy → CoalitionStrategy → ℝ) : ℝ :=
  sSup (Set.range fun response =>
    sInf (Set.range (floorPayoff response)))

/-- The best unilateral responder payoff against one fixed coalition strategy. -/
def unilateralValueAgainst
    (payoff : ResponderStrategy → CoalitionStrategy → ℝ)
    (fixedCoalition : CoalitionStrategy) : ℝ :=
  sSup (Set.range fun response => payoff response fixedCoalition)

/--
The floor-game security value is at most the actual-game unilateral value
against a fixed coalition strategy, provided actual payoffs dominate floor
payoffs pointwise.

The boundedness assumptions are exactly those needed to use `sInf` and `sSup`
over `ℝ`; they are automatic for the finite bounded-payoff games intended in
Question 110.
-/
theorem securityFloor_le_unilateralValueAgainst
    [Nonempty ResponderStrategy]
    (floorPayoff responsePayoff :
      ResponderStrategy → CoalitionStrategy → ℝ)
    (fixedCoalition : CoalitionStrategy)
    (hfloorBelow : ∀ response,
      BddBelow (Set.range (floorPayoff response)))
    (hresponseAbove : BddAbove
      (Set.range fun response => responsePayoff response fixedCoalition))
    (hpayoff : ∀ response coalition,
      floorPayoff response coalition ≤ responsePayoff response coalition) :
    securityFloor floorPayoff ≤
      unilateralValueAgainst responsePayoff fixedCoalition := by
  unfold securityFloor unilateralValueAgainst
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨response, rfl⟩
  calc
    sInf (Set.range (floorPayoff response)) ≤
        floorPayoff response fixedCoalition :=
      csInf_le (hfloorBelow response) ⟨fixedCoalition, rfl⟩
    _ ≤ responsePayoff response fixedCoalition :=
      hpayoff response fixedCoalition
    _ ≤ sSup (Set.range fun response =>
        responsePayoff response fixedCoalition) :=
      le_csSup hresponseAbove ⟨response, rfl⟩

/--
Responder credibility against the prescribed coalition implies the
responder-floor inequality with the same error allowance.
-/
theorem securityFloor_le_prescribed_add_of_unilateralCredibility
    [Nonempty ResponderStrategy]
    (floorPayoff responsePayoff :
      ResponderStrategy → CoalitionStrategy → ℝ)
    (fixedCoalition : CoalitionStrategy)
    (prescribedPayoff error : ℝ)
    (hfloorBelow : ∀ response,
      BddBelow (Set.range (floorPayoff response)))
    (hresponseAbove : BddAbove
      (Set.range fun response => responsePayoff response fixedCoalition))
    (hpayoff : ∀ response coalition,
      floorPayoff response coalition ≤ responsePayoff response coalition)
    (hcredible : unilateralValueAgainst responsePayoff fixedCoalition ≤
      prescribedPayoff + error) :
    securityFloor floorPayoff ≤ prescribedPayoff + error :=
  (securityFloor_le_unilateralValueAgainst floorPayoff responsePayoff
    fixedCoalition hfloorBelow hresponseAbove hpayoff).trans hcredible

end ResponderFloorComparison
end GameTheory
