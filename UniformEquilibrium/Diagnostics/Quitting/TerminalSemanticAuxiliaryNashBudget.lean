/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticAtomicSupportBoundary
import UniformEquilibrium.Quitting.AbsorptionPath.NormalizedFiniteWindowOccupation
import UniformEquilibrium.Quitting.Cycles.PeriodOneTangentAtlas

/-!
# Auxiliary-target budget at the minimum terminal-semantic stratum

An auxiliary continuation need not be a realizable semantic state.  It may be
used only to select a one-stage mixed Nash root, which is then prefixed to an
actual minimum carrier point.  Comparing the auxiliary continuation with the
prescribed/envelope pair gives an exact absorption budget.

The budget forces every positive minimum terminal-semantic pair onto the
all-Continue Nash face.  In particular the provenance-preserving atomic branch
of the previous global reduction is empty.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-! ## One-coordinate auxiliary-target estimate -/

/-- Prefix debt against the actual semantic pair is controlled by an exact
Nash root selected against the lower auxiliary continuation `pair.2 - h`.
The extra coefficient is exactly the singleton absorption mass of the player.
-/
theorem quittingTerminalSemanticDebt_prefix_le_auxiliaryNash
    (pair : QuittingTerminalSemanticPair ι) (h : Payoff ι)
    (root : ι → PMF Bool) (who : ι)
    (hh : 0 ≤ h who)
    (hnash : IsεQuittingRootNash reward (pair.2 - h) 0 root) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPrefix reward root pair) who ≤
      quittingStationaryContinueMass root *
          quittingTerminalSemanticDebt pair who +
        quittingRootCoalitionMass root {who} * h who := by
  let auxiliary : Payoff ι := pair.2 - h
  let quitValue := quittingRootQuitPayoff reward pair.1 root who
  let continueAux := quittingRootContinuePayoff reward auxiliary root who
  let opponentContinue := quittingRootOpponentContinueMass root who
  have hauxiliary : auxiliary who + h who = pair.2 who := by
    dsimp [auxiliary]
    ring
  have hquitInvariant : quittingRootQuitPayoff reward auxiliary root who =
      quitValue := by
    exact quittingRootQuitPayoff_continuation_invariant
      reward auxiliary pair.1 root who
  have hcontinueActual :
      quittingRootContinuePayoff reward
          (Function.update pair.1 who (pair.2 who)) root who =
        continueAux + opponentContinue * h who := by
    calc
      quittingRootContinuePayoff reward
          (Function.update pair.1 who (pair.2 who)) root who =
          quittingRootContinuePayoff reward
            (Function.update auxiliary who (pair.2 who)) root who := by
              unfold quittingRootContinuePayoff
              apply quittingRootExpectedPayoff_continuation_congr
              simp
      _ = quittingRootContinuePayoff reward
            (Function.update auxiliary who (auxiliary who + h who))
              root who := by rw [hauxiliary]
      _ = continueAux + opponentContinue * h who := by
            exact quittingRootContinuePayoff_update_add
              reward auxiliary root who (h who)
  have hopponentContinueNonneg : 0 ≤ opponentContinue :=
    quittingRootOpponentContinueMass_nonneg root who
  have hincrementNonneg : 0 ≤ opponentContinue * h who :=
    mul_nonneg hopponentContinueNonneg hh
  have henvelope :
      (quittingTerminalSemanticPrefix reward root pair).2 who ≤
        quittingRootSuccessorPayoff reward auxiliary root who +
          opponentContinue * h who := by
    change max quitValue
        (quittingRootContinuePayoff reward
          (Function.update pair.1 who (pair.2 who)) root who) ≤ _
    rw [hcontinueActual,
      quittingRootSuccessorPayoff_eq_max_of_isZeroNash
        reward auxiliary root who hnash,
      hquitInvariant]
    apply max_le
    · exact (le_max_left _ _).trans
        (le_add_of_nonneg_right hincrementNonneg)
    · dsimp only [continueAux]
      have hright := le_max_right quitValue
        (quittingRootContinuePayoff reward auxiliary root who)
      linarith
  have hsuccessorDifference :
      quittingRootSuccessorPayoff reward auxiliary root who -
          quittingRootSuccessorPayoff reward pair.1 root who =
        quittingStationaryContinueMass root *
          (quittingTerminalSemanticDebt pair who - h who) := by
    rw [quittingRootSuccessorPayoff_sub_eq_continueMass_mul]
    dsimp [auxiliary, quittingTerminalSemanticDebt]
    ring
  have hsingleton : opponentContinue -
      quittingStationaryContinueMass root =
        quittingRootCoalitionMass root {who} := by
    exact quittingRootOpponentContinue_sub_continue_eq_singletonMass root who
  unfold quittingTerminalSemanticDebt
  change (quittingTerminalSemanticPrefix reward root pair).2 who -
      quittingRootSuccessorPayoff reward pair.1 root who ≤ _
  calc
    (quittingTerminalSemanticPrefix reward root pair).2 who -
        quittingRootSuccessorPayoff reward pair.1 root who ≤
      (quittingRootSuccessorPayoff reward auxiliary root who +
          opponentContinue * h who) -
        quittingRootSuccessorPayoff reward pair.1 root who :=
      sub_le_sub_right henvelope _
    _ = quittingStationaryContinueMass root *
          quittingTerminalSemanticDebt pair who +
        quittingRootCoalitionMass root {who} * h who := by
      calc
        (quittingRootSuccessorPayoff reward auxiliary root who +
              opponentContinue * h who) -
            quittingRootSuccessorPayoff reward pair.1 root who =
          (quittingRootSuccessorPayoff reward auxiliary root who -
              quittingRootSuccessorPayoff reward pair.1 root who) +
            opponentContinue * h who := by ring
        _ = _ := by
          rw [hsuccessorDifference, ← hsingleton]
          ring

/-! ## Summed minimum-debt budget -/

/-- Exact minimum-debt absorption budget.  Collision mass is the probability
of two or more simultaneous quitters; singleton masses are unnormalized
one-stage probabilities. -/
theorem minimumTerminalSemantic_auxiliaryNash_budget
    (pair : QuittingTerminalSemanticPair ι)
    (h : Payoff ι) (root : ι → PMF Bool) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hh : ∀ who, 0 ≤ h who)
    (hnash : IsεQuittingRootNash reward (pair.2 - h) 0 root) :
    quittingTerminalSemanticDebtSum pair *
          quittingRootCollisionMass root +
        ∑ who, quittingRootCoalitionMass root {who} *
          (quittingTerminalSemanticDebtSum pair - h who) ≤ 0 := by
  let prefixed := quittingTerminalSemanticPrefix reward root pair
  have hprefixed : prefixed ∈ quittingTerminalSemanticCarrier reward :=
    quittingTerminalSemanticPrefix_mem_carrier
      reward root pair hM hreward hpair
  have hcoordinate : ∀ who,
      quittingTerminalSemanticDebt prefixed who ≤
        quittingStationaryContinueMass root *
            quittingTerminalSemanticDebt pair who +
          quittingRootCoalitionMass root {who} * h who := by
    intro who
    exact quittingTerminalSemanticDebt_prefix_le_auxiliaryNash
      (reward := reward) pair h root who (hh who) hnash
  have hsum : quittingTerminalSemanticDebtSum prefixed ≤
      quittingStationaryContinueMass root *
          quittingTerminalSemanticDebtSum pair +
        ∑ who, quittingRootCoalitionMass root {who} * h who := by
    unfold quittingTerminalSemanticDebtSum
    calc
      ∑ who, quittingTerminalSemanticDebt prefixed who ≤
          ∑ who, (quittingStationaryContinueMass root *
              quittingTerminalSemanticDebt pair who +
            quittingRootCoalitionMass root {who} * h who) :=
        Finset.sum_le_sum fun who _ => hcoordinate who
      _ = quittingStationaryContinueMass root *
            ∑ who, quittingTerminalSemanticDebt pair who +
          ∑ who, quittingRootCoalitionMass root {who} * h who := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
  have hminPrefix : quittingTerminalSemanticDebtSum pair ≤
      quittingTerminalSemanticDebtSum prefixed :=
    hminimum prefixed hprefixed
  have habsorption :=
    QuittingFiniteRootWindow.quittingRootAbsorptionMass_eq_sum_singletonMass_add_collisionMass
      root
  unfold quittingRootAbsorptionMass at habsorption
  have hraw : quittingTerminalSemanticDebtSum pair ≤
      quittingStationaryContinueMass root *
          quittingTerminalSemanticDebtSum pair +
        ∑ who, quittingRootCoalitionMass root {who} * h who :=
    hminPrefix.trans hsum
  have habsBudget : quittingTerminalSemanticDebtSum pair *
      (1 - quittingStationaryContinueMass root) ≤
        ∑ who, quittingRootCoalitionMass root {who} * h who := by
    nlinarith
  rw [habsorption] at habsBudget
  calc
    quittingTerminalSemanticDebtSum pair *
          quittingRootCollisionMass root +
        ∑ who, quittingRootCoalitionMass root {who} *
          (quittingTerminalSemanticDebtSum pair - h who) =
      quittingTerminalSemanticDebtSum pair *
          ((∑ who, quittingRootCoalitionMass root {who}) +
            quittingRootCollisionMass root) -
        ∑ who, quittingRootCoalitionMass root {who} * h who := by
          simp_rw [mul_sub]
          rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
          ring
    _ ≤ 0 := by linarith

/-! ## Strict auxiliary cube collapses to all Continue -/

/-- Any auxiliary exact Nash root whose coordinate shifts lie strictly inside
the total-debt cube has zero absorption and is the all-Continue root. -/
theorem minimumTerminalSemantic_auxiliaryNash_eq_allContinue
    (pair : QuittingTerminalSemanticPair ι)
    (h : Payoff ι) (root : ι → PMF Bool) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (hh : ∀ who, 0 ≤ h who)
    (hstrict : ∀ who, h who < quittingTerminalSemanticDebtSum pair)
    (hnash : IsεQuittingRootNash reward (pair.2 - h) 0 root) :
    root = (quittingAllContinueRoot : ι → PMF Bool) := by
  have hbudget := minimumTerminalSemantic_auxiliaryNash_budget
    (reward := reward) pair h root hM hreward hpair hminimum hh hnash
  have hcollisionNonneg : 0 ≤ quittingRootCollisionMass root :=
    quittingRootCollisionMass_nonneg root
  have htermsNonneg : ∀ who ∈ (Finset.univ : Finset ι),
      0 ≤ quittingRootCoalitionMass root {who} *
        (quittingTerminalSemanticDebtSum pair - h who) := by
    intro who _
    exact mul_nonneg
      (MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg root {who})
      (sub_nonneg.mpr (hstrict who).le)
  have hsumNonneg : 0 ≤ ∑ who,
      quittingRootCoalitionMass root {who} *
        (quittingTerminalSemanticDebtSum pair - h who) :=
    Finset.sum_nonneg htermsNonneg
  have hcollisionZero : quittingRootCollisionMass root = 0 := by
    nlinarith
  have hsumZero : ∑ who,
      quittingRootCoalitionMass root {who} *
        (quittingTerminalSemanticDebtSum pair - h who) = 0 := by
    rw [hcollisionZero, mul_zero, zero_add] at hbudget
    exact le_antisymm hbudget hsumNonneg
  have hsingletonZero : ∀ who,
      quittingRootCoalitionMass root {who} = 0 := by
    have hzeroTerms :=
      (Finset.sum_eq_zero_iff_of_nonneg htermsNonneg).mp hsumZero
    intro who
    have hproduct := hzeroTerms who (Finset.mem_univ who)
    have hcoefficient : 0 < quittingTerminalSemanticDebtSum pair - h who :=
      sub_pos.mpr (hstrict who)
    nlinarith [MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg
      root {who}]
  have habsorption :=
    QuittingFiniteRootWindow.quittingRootAbsorptionMass_eq_sum_singletonMass_add_collisionMass
      root
  have hsingletonSum :
      (∑ who, quittingRootCoalitionMass root {who}) = 0 := by
    exact Finset.sum_eq_zero fun who _ => hsingletonZero who
  have habsorptionZero : quittingRootAbsorptionMass root = 0 := by
    rw [habsorption, hsingletonSum, hcollisionZero, zero_add]
  have hcontinue : quittingStationaryContinueMass root = 1 := by
    unfold quittingRootAbsorptionMass at habsorptionZero
    linarith
  funext who
  have hpure := eq_pure_false_of_quittingStationaryContinueMass_eq_one
    hcontinue who
  simpa [quittingAllContinueRoot] using hpure

/-- On the closed auxiliary cube, collision mass vanishes and singleton
absorption can occur only at a coordinate shifted by the full minimum debt.
This is the critical-boundary form of the auxiliary-target budget. -/
theorem minimumTerminalSemantic_auxiliaryNash_criticalFace
    (pair : QuittingTerminalSemanticPair ι)
    (h : Payoff ι) (root : ι → PMF Bool) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (hh : ∀ who, 0 ≤ h who)
    (hle : ∀ who, h who ≤ quittingTerminalSemanticDebtSum pair)
    (hnash : IsεQuittingRootNash reward (pair.2 - h) 0 root) :
    quittingRootCollisionMass root = 0 ∧
      ∀ who, 0 < quittingRootCoalitionMass root {who} →
        h who = quittingTerminalSemanticDebtSum pair := by
  have hbudget := minimumTerminalSemantic_auxiliaryNash_budget
    (reward := reward) pair h root hM hreward hpair hminimum hh hnash
  have hcollisionNonneg : 0 ≤ quittingRootCollisionMass root :=
    quittingRootCollisionMass_nonneg root
  have htermsNonneg : ∀ who ∈ (Finset.univ : Finset ι),
      0 ≤ quittingRootCoalitionMass root {who} *
        (quittingTerminalSemanticDebtSum pair - h who) := by
    intro who _
    exact mul_nonneg
      (MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg root {who})
      (sub_nonneg.mpr (hle who))
  have hsumNonneg : 0 ≤ ∑ who,
      quittingRootCoalitionMass root {who} *
        (quittingTerminalSemanticDebtSum pair - h who) :=
    Finset.sum_nonneg htermsNonneg
  have hcollisionZero : quittingRootCollisionMass root = 0 := by
    nlinarith
  have hsumZero : ∑ who,
      quittingRootCoalitionMass root {who} *
        (quittingTerminalSemanticDebtSum pair - h who) = 0 := by
    rw [hcollisionZero, mul_zero, zero_add] at hbudget
    exact le_antisymm hbudget hsumNonneg
  have hzeroTerms :=
    (Finset.sum_eq_zero_iff_of_nonneg htermsNonneg).mp hsumZero
  refine ⟨hcollisionZero, ?_⟩
  intro who hmass
  have hproduct := hzeroTerms who (Finset.mem_univ who)
  nlinarith

/-- Every exact Nash root against the prescribed coordinate of a positive
minimum semantic pair is collision-free.  Any singleton quitter must carry
the entire total debt. -/
theorem minimumTerminalSemantic_exactNash_criticalFace
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (hnash : IsεQuittingRootNash reward pair.1 0 root) :
    quittingRootCollisionMass root = 0 ∧
      ∀ who, 0 < quittingRootCoalitionMass root {who} →
        quittingTerminalSemanticDebt pair who =
          quittingTerminalSemanticDebtSum pair := by
  let debt : Payoff ι := fun who => quittingTerminalSemanticDebt pair who
  have hdebtNonneg : ∀ who, 0 ≤ debt who := fun who =>
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hM hreward hpair who
  have hdebtLe : ∀ who,
      debt who ≤ quittingTerminalSemanticDebtSum pair := by
    intro who
    unfold quittingTerminalSemanticDebtSum
    exact Finset.single_le_sum
      (fun player _ => hdebtNonneg player) (Finset.mem_univ who)
  have htail : pair.2 - debt = pair.1 := by
    funext who
    dsimp [debt, quittingTerminalSemanticDebt]
    ring
  have hnashAux : IsεQuittingRootNash reward (pair.2 - debt) 0 root := by
    rw [htail]
    exact hnash
  simpa [debt] using minimumTerminalSemantic_auxiliaryNash_criticalFace
    (reward := reward) pair debt root hM hreward hpair hminimum hpositive
      hdebtNonneg hdebtLe hnashAux

/-! ## Every positive minimum point is an all-Continue plateau -/

/-- Finite mixed Nash existence, in the exact root-Nash form used by the
auxiliary-target argument. -/
theorem exists_isZeroQuittingRootNash
    (tail : Payoff ι) :
    ∃ root : ι → PMF Bool, IsεQuittingRootNash reward tail 0 root := by
  obtain ⟨simplexRoot, hendpoint⟩ :=
    exists_isZeroQuittingRootEndpointNash_simplex reward tail
  refine ⟨quittingRootOfSimplex simplexRoot, ?_⟩
  exact (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
    reward tail (quittingRootOfSimplex simplexRoot)).mp hendpoint

/-- Quantitative singleton margin at every positive minimum semantic pair. -/
theorem minimumTerminalSemantic_singletonMargin
    (pair : QuittingTerminalSemanticPair ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair) (who : ι) :
    quittingTerminalSemanticDebtSum pair ≤ pair.2 who -
      reward (quittingSingletonTerminal who) who := by
  let zeroShift : Payoff ι := fun _ => 0
  obtain ⟨zeroRoot, hzeroNash⟩ :=
    exists_isZeroQuittingRootNash (reward := reward) pair.2
  have hzeroRoot : zeroRoot =
      (quittingAllContinueRoot : ι → PMF Bool) := by
    apply minimumTerminalSemantic_auxiliaryNash_eq_allContinue
      (reward := reward) pair zeroShift zeroRoot hM hreward hpair hminimum
        hpositive
    · intro player
      simp [zeroShift]
    · intro player
      simpa [zeroShift] using hpositive
    · have htail : pair.2 - zeroShift = pair.2 := by
        funext player
        simp [zeroShift]
      rw [htail]
      exact hzeroNash
  have hsingletonLeEnvelope :
      reward (quittingSingletonTerminal who) who ≤ pair.2 who := by
    have hnashAll : IsεQuittingRootNash reward pair.2 0
        (quittingAllContinueRoot : ι → PMF Bool) := by
      simpa [hzeroRoot] using hzeroNash
    exact (isZeroQuittingRootNash_allContinue_iff_singleton_le
      reward pair.2).mp hnashAll who
  by_contra hnot
  have hgap : pair.2 who - reward (quittingSingletonTerminal who) who <
      quittingTerminalSemanticDebtSum pair := lt_of_not_ge hnot
  let ε := (quittingTerminalSemanticDebtSum pair -
    (pair.2 who - reward (quittingSingletonTerminal who) who)) / 2
  have hεpos : 0 < ε := by
    dsimp [ε]
    linarith
  have hεlt : ε < quittingTerminalSemanticDebtSum pair := by
    dsimp [ε]
    linarith
  let shift : Payoff ι := fun player =>
    if player = who then quittingTerminalSemanticDebtSum pair - ε else 0
  have hshiftNonneg : ∀ player, 0 ≤ shift player := by
    intro player
    by_cases hplayer : player = who
    · simp [shift, hplayer]
      linarith
    · simp [shift, hplayer]
  have hshiftStrict : ∀ player,
      shift player < quittingTerminalSemanticDebtSum pair := by
    intro player
    by_cases hplayer : player = who
    · have hshift : shift player =
          quittingTerminalSemanticDebtSum pair - ε := by
        simp [shift, hplayer]
      rw [hshift]
      linarith
    · have hshift : shift player = 0 := by
        simp [shift, hplayer]
      rw [hshift]
      exact hpositive
  obtain ⟨root, hnash⟩ :=
    exists_isZeroQuittingRootNash (reward := reward) (pair.2 - shift)
  have hrootAll : root =
      (quittingAllContinueRoot : ι → PMF Bool) :=
    minimumTerminalSemantic_auxiliaryNash_eq_allContinue
      (reward := reward) pair shift root hM hreward hpair hminimum
        hpositive hshiftNonneg hshiftStrict hnash
  have hnashAll : IsεQuittingRootNash reward (pair.2 - shift) 0
      (quittingAllContinueRoot : ι → PMF Bool) := by
    simpa [hrootAll] using hnash
  have hsingletonAux :=
    (isZeroQuittingRootNash_allContinue_iff_singleton_le
      reward (pair.2 - shift)).mp hnashAll who
  have hshiftWho : shift who = quittingTerminalSemanticDebtSum pair - ε := by
    simp [shift]
  rw [Pi.sub_apply, hshiftWho] at hsingletonAux
  dsimp [ε] at hsingletonAux
  linarith

/-- Every positive minimum semantic pair is an exact all-Continue Nash
self-loop, and has the quantitative singleton margin above. -/
theorem minimumTerminalSemantic_is_allContinuePlateau
    (pair : QuittingTerminalSemanticPair ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair) :
    IsεQuittingRootNash reward pair.1 0
        (quittingAllContinueRoot : ι → PMF Bool) ∧
      quittingTerminalSemanticPrefix reward quittingAllContinueRoot pair =
        pair ∧
      ∀ who, quittingTerminalSemanticDebtSum pair ≤ pair.2 who -
        reward (quittingSingletonTerminal who) who := by
  have hdebtNonneg : ∀ who, 0 ≤ quittingTerminalSemanticDebt pair who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hM hreward hpair
  have hsingleton : ∀ who,
      reward (quittingSingletonTerminal who) who ≤ pair.1 who := by
    intro who
    have hmargin := minimumTerminalSemantic_singletonMargin
      (reward := reward) pair hM hreward hpair hminimum hpositive who
    have hcoordinateLe : quittingTerminalSemanticDebt pair who ≤
        quittingTerminalSemanticDebtSum pair := by
      unfold quittingTerminalSemanticDebtSum
      exact Finset.single_le_sum
        (fun player _ => hdebtNonneg player) (Finset.mem_univ who)
    unfold quittingTerminalSemanticDebt at hcoordinateLe
    linarith
  have hnashAll :=
    (isZeroQuittingRootNash_allContinue_iff_singleton_le reward pair.1).mpr
      hsingleton
  exact ⟨hnashAll,
    quittingTerminalSemanticPrefix_allContinue_eq_of_isZeroNash
      reward pair hdebtNonneg hnashAll,
    minimumTerminalSemantic_singletonMargin
      (reward := reward) pair hM hreward hpair hminimum hpositive⟩

/-! ## Global consequences -/

/-- A provenance atomic minimum-semantic solo row cannot exist. -/
theorem not_hasProvenanceAtomicMinimumSemanticSoloRow
    (regime : QuittingCounterexampleRegime reward) :
    ¬ HasProvenanceAtomicMinimumSemanticSoloRow regime := by
  rintro ⟨current, tail, owner, hazard, anchor, _hcurrentCarrier,
    htailCarrier, _hcurrentMin, htailMin, _hprefix, _hnash,
    _hcurrentDebt, htailDebt, _hotherDebt, _hownerPin,
    _hanchorNe, hattractive, _hquit, _hendpoint, _hisolated,
    _hgap, _hpunishment, _hcontinue⟩
  have htailDebtNonneg : ∀ player,
      0 ≤ quittingTerminalSemanticDebt tail player :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward
      (quittingRewardBound_nonneg reward)
      (abs_reward_le_quittingRewardBound reward) htailCarrier
  have htailPositive : 0 < quittingTerminalSemanticDebtSum tail := by
    unfold quittingTerminalSemanticDebtSum
    exact Finset.sum_pos' (fun player _ => htailDebtNonneg player)
      ⟨owner, Finset.mem_univ owner, htailDebt⟩
  have hplateau := minimumTerminalSemantic_is_allContinuePlateau
    (reward := reward) tail (quittingRewardBound_nonneg reward)
      (abs_reward_le_quittingRewardBound reward) htailCarrier htailMin
      htailPositive
  have hsingleton :=
    (isZeroQuittingRootNash_allContinue_iff_singleton_le reward tail.1).mp
      hplateau.1 anchor
  exact (not_lt_of_ge hsingleton) hattractive

/-- Every counterexample has a positive minimum all-Continue semantic
plateau; the provenance atomic alternative is eliminated. -/
theorem noUniformPayoff_implies_positiveMinimumSemanticPlateau
    [Nonempty ι]
    (regime : QuittingCounterexampleRegime reward)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    HasPositiveMinimumTerminalSemanticPlateau reward := by
  obtain ⟨pair, _root, hpair, _hnash, hminimum, hdebt, _hface⟩ :=
    exists_positive_minimumTerminalSemanticDebt_face_of_no_uniformPayoff
      reward hM hreward regime.not_exists_uniformEquilibriumPayoff
  have hdebtNonneg : ∀ player,
      0 ≤ quittingTerminalSemanticDebt pair player :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hM hreward hpair
  have hpositive : 0 < quittingTerminalSemanticDebtSum pair := by
    obtain ⟨who, hwho⟩ := hdebt
    unfold quittingTerminalSemanticDebtSum
    exact Finset.sum_pos' (fun player _ => hdebtNonneg player)
      ⟨who, Finset.mem_univ who, hwho⟩
  have hplateau := minimumTerminalSemantic_is_allContinuePlateau
    (reward := reward) pair hM hreward hpair hminimum hpositive
  exact ⟨pair, hpair, hminimum, hdebt, hplateau.1, hplateau.2.1⟩

end GameTheory
