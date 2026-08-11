/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauFractionalResetDropout

/-!
# A pair-dropout route need not carry a profitable toggle

The finite routed-reset theorem extracts a full member-Continue move from a
positive pair cylinder to a positive singleton cylinder.  Its endpoint moves
are deliberately arbitrary, so the routed edge has no payoff sign by itself.

This two-player regression makes that fence exact.  Starting from sure joint
Quit, first force player `false` to Continue and then force player `true` to
Continue.  The route is

`{false,true} -> {true} -> empty`,

and the final root is exact Nash against the zero continuation.  Nevertheless
at the pair row player `false` strictly prefers Quit to Continue: the first
dropout moves in the direction opposite to its better endpoint.

Thus a pair-to-singleton crossing cannot be used as a positive edge in a
strict-toggle circulation or Boolean-curl argument unless the reset producer
separately proves that the selected full move is payoff-improving at that
same root and continuation.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

namespace QuittingPairDropoutSignRegression

/-- Player `false` values the joint collision at `1` and the singleton
`{true}` at `0`.  Both own singleton rewards are `-1`, making all-Continue
exact Nash against the zero continuation. -/
def reward (quitters : {S : Finset Bool // S.Nonempty}) : Payoff Bool :=
  fun who =>
    if false ∈ quitters.1 ∧ true ∈ quitters.1 then
      if who then 0 else 1
    else if who ∈ quitters.1 then
      -1
    else
      0

def tail : Payoff Bool := fun _ => 0

/-- The initial sure collision. -/
def pairRoot : Bool -> PMF Bool := fun _ => PMF.pure true

/-- The unsigned pair dropout: player `false` is forced to Continue. -/
def singletonRoot : Bool -> PMF Bool :=
  Function.update pairRoot false (PMF.pure false)

/-- Erasing the survivor reaches all-Continue. -/
def finalRoot : Bool -> PMF Bool :=
  Function.update singletonRoot true (PMF.pure false)

theorem singletonRoot_probabilities :
    (singletonRoot false true).toReal = 0 ∧
      (singletonRoot true true).toReal = 1 := by
  simp [singletonRoot, pairRoot]

theorem finalRoot_eq_allContinue :
    finalRoot = (quittingAllContinueRoot : Bool -> PMF Bool) := by
  funext who
  cases who <;>
    simp [finalRoot, singletonRoot, quittingAllContinueRoot]

theorem pairRoot_pairMass :
    quittingRootCoalitionMass pairRoot (Finset.univ : Finset Bool) = 1 := by
  unfold quittingRootCoalitionMass
  have hcomplement : (Finset.univ : Finset Bool)ᶜ = ∅ := by
    ext who
    simp
  rw [coalitionMass, hcomplement]
  simp [quittingRootQuitRates, pairRoot]

theorem singletonRoot_singletonMass :
    quittingRootCoalitionMass singletonRoot ({true} : Finset Bool) = 1 := by
  unfold quittingRootCoalitionMass
  have hcomplement : ({true} : Finset Bool)ᶜ = {false} := by decide
  rw [coalitionMass, hcomplement]
  simp [quittingRootQuitRates, singletonRoot, pairRoot]

/-- At the pair row, player `false` gets `1` by staying in the pair. -/
theorem pairRoot_quitPayoff_false :
    quittingRootQuitPayoff reward tail pairRoot false = 1 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [QuittingExactDynamicDebtVanishingCounterexample.expect_pmfPi_bool]
  simp [expect_eq_sum, quittingRootPayoff, reward, tail, pairRoot]

/-- At the same row, forcing player `false` to Continue yields `{true}` and
payoff `0`. -/
theorem pairRoot_continuePayoff_false :
    quittingRootContinuePayoff reward tail pairRoot false = 0 := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [QuittingExactDynamicDebtVanishingCounterexample.expect_pmfPi_bool]
  simp [expect_eq_sum, quittingRootPayoff, reward, tail, pairRoot]

/-- The routed Continue dropout is strictly anti-improving. -/
theorem pairRoot_dropout_endpointDifference :
    quittingRootEndpointDifference reward tail pairRoot false = 1 := by
  rw [quittingRootEndpointDifference, pairRoot_quitPayoff_false,
    pairRoot_continuePayoff_false]
  norm_num

/-- Despite the unsigned first dropout, erasing both players reaches an exact
Nash root. -/
theorem finalRoot_isZeroNash :
    IsεQuittingRootNash reward tail 0 finalRoot := by
  rw [finalRoot_eq_allContinue,
    isZeroQuittingRootNash_allContinue_iff_singleton_le]
  intro who
  cases who <;>
    simp [reward, tail, quittingSingletonTerminal]

theorem finalRoot_totalNashDefect :
    quittingRootTotalNashDefect reward tail finalRoot = 0 := by
  unfold quittingRootTotalNashDefect
  simp_rw [(isZeroQuittingRootNash_iff_coordinateNashDefect_eq_zero
    reward tail finalRoot).mp finalRoot_isZeroNash]
  simp

/-- **Regression headline.**  A positive pair-to-singleton route inside a
finite word ending at zero Nash defect need not be a strict profitable
membership toggle. -/
theorem pair_dropout_can_oppose_betterEndpoint_before_zeroDefect_endpoint :
    quittingRootCoalitionMass pairRoot (Finset.univ : Finset Bool) = 1 ∧
      quittingRootCoalitionMass singletonRoot ({true} : Finset Bool) = 1 ∧
      quittingRootEndpointDifference reward tail pairRoot false = 1 ∧
      finalRoot = (quittingAllContinueRoot : Bool -> PMF Bool) ∧
      quittingRootTotalNashDefect reward tail finalRoot = 0 := by
  exact ⟨pairRoot_pairMass, singletonRoot_singletonMass,
    pairRoot_dropout_endpointDifference, finalRoot_eq_allContinue,
    finalRoot_totalNashDefect⟩

end QuittingPairDropoutSignRegression

end GameTheory
