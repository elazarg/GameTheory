/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticMinimumDebtSimplex

/-!
# Weighted auxiliary Nash budget

The auxiliary-target argument does not depend on the unweighted sum of
best-response debts.  Any nonnegative costate gives a scalar debt objective.
At a positive minimum of that objective, collision pays the full minimum
cost, while singleton `i` receives exactly the subsidy `theta i * h i`.

This yields an anisotropic Nash moat.  The formulation uses the product
`theta i * h i` rather than division by `theta i`, so the boundary remains
meaningful even when some costate coordinates vanish.  The strict moat only
needs every displayed subsidy to lie below the positive minimum value.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Scalar best-response debt selected by a costate. -/
def quittingTerminalSemanticWeightedDebtSum
    (theta : Payoff ι) (pair : QuittingTerminalSemanticPair ι) : ℝ :=
  ∑ who, theta who * quittingTerminalSemanticDebt pair who

/-- Weighted auxiliary-target budget at a minimum carrier point. -/
theorem minimumTerminalSemantic_weightedAuxiliaryNash_budget
    (theta : Payoff ι) (pair : QuittingTerminalSemanticPair ι)
    (h : Payoff ι) (root : ι → PMF Bool) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticWeightedDebtSum theta pair ≤
        quittingTerminalSemanticWeightedDebtSum theta candidate)
    (htheta : ∀ who, 0 ≤ theta who)
    (hh : ∀ who, 0 ≤ h who)
    (hnash : IsεQuittingRootNash reward (pair.2 - h) 0 root) :
    quittingTerminalSemanticWeightedDebtSum theta pair *
          quittingRootCollisionMass root +
        ∑ who, quittingRootCoalitionMass root {who} *
          (quittingTerminalSemanticWeightedDebtSum theta pair -
            theta who * h who) ≤ 0 := by
  let prefixed := quittingTerminalSemanticPrefix reward root pair
  have hprefixed : prefixed ∈ quittingTerminalSemanticCarrier reward :=
    quittingTerminalSemanticPrefix_mem_carrier
      reward root pair hM hreward hpair
  have hcoordinate : ∀ who,
      theta who * quittingTerminalSemanticDebt prefixed who ≤
        theta who *
          (quittingStationaryContinueMass root *
              quittingTerminalSemanticDebt pair who +
            quittingRootCoalitionMass root {who} * h who) := by
    intro who
    exact mul_le_mul_of_nonneg_left
      (quittingTerminalSemanticDebt_prefix_le_auxiliaryNash
        (reward := reward) pair h root who (hh who) hnash)
      (htheta who)
  have hsum : quittingTerminalSemanticWeightedDebtSum theta prefixed ≤
      quittingStationaryContinueMass root *
          quittingTerminalSemanticWeightedDebtSum theta pair +
        ∑ who, quittingRootCoalitionMass root {who} *
          (theta who * h who) := by
    unfold quittingTerminalSemanticWeightedDebtSum
    calc
      ∑ who, theta who * quittingTerminalSemanticDebt prefixed who ≤
          ∑ who, theta who *
            (quittingStationaryContinueMass root *
                quittingTerminalSemanticDebt pair who +
              quittingRootCoalitionMass root {who} * h who) :=
        Finset.sum_le_sum fun who _ => hcoordinate who
      _ = quittingStationaryContinueMass root *
            ∑ who, theta who * quittingTerminalSemanticDebt pair who +
          ∑ who, quittingRootCoalitionMass root {who} *
            (theta who * h who) := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib]
        congr 1
        · calc
            ∑ who, theta who *
                (quittingStationaryContinueMass root *
                  quittingTerminalSemanticDebt pair who) =
                ∑ who, quittingStationaryContinueMass root *
                  (theta who * quittingTerminalSemanticDebt pair who) := by
              apply Finset.sum_congr rfl
              intro who _
              ring
            _ = _ := by rw [Finset.mul_sum]
        · apply Finset.sum_congr rfl
          intro who _
          ring
  have hminPrefix : quittingTerminalSemanticWeightedDebtSum theta pair ≤
      quittingTerminalSemanticWeightedDebtSum theta prefixed :=
    hminimum prefixed hprefixed
  have hraw : quittingTerminalSemanticWeightedDebtSum theta pair ≤
      quittingStationaryContinueMass root *
          quittingTerminalSemanticWeightedDebtSum theta pair +
        ∑ who, quittingRootCoalitionMass root {who} *
          (theta who * h who) := hminPrefix.trans hsum
  have habsBudget : quittingTerminalSemanticWeightedDebtSum theta pair *
      (1 - quittingStationaryContinueMass root) ≤
        ∑ who, quittingRootCoalitionMass root {who} *
          (theta who * h who) := by
    nlinarith
  have habsorption :=
    QuittingFiniteRootWindow.quittingRootAbsorptionMass_eq_sum_singletonMass_add_collisionMass
      root
  unfold quittingRootAbsorptionMass at habsorption
  rw [habsorption] at habsBudget
  calc
    quittingTerminalSemanticWeightedDebtSum theta pair *
          quittingRootCollisionMass root +
        ∑ who, quittingRootCoalitionMass root {who} *
          (quittingTerminalSemanticWeightedDebtSum theta pair -
            theta who * h who) =
      quittingTerminalSemanticWeightedDebtSum theta pair *
          ((∑ who, quittingRootCoalitionMass root {who}) +
            quittingRootCollisionMass root) -
        ∑ who, quittingRootCoalitionMass root {who} *
          (theta who * h who) := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
      ring
    _ ≤ 0 := by linarith

/-- The open anisotropic moat: if every singleton subsidy is strictly below
the positive weighted minimum, every exact auxiliary Nash root is
all-Continue. -/
theorem minimumTerminalSemantic_weightedAuxiliaryNash_eq_allContinue
    (theta : Payoff ι) (pair : QuittingTerminalSemanticPair ι)
    (h : Payoff ι) (root : ι → PMF Bool) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticWeightedDebtSum theta pair ≤
        quittingTerminalSemanticWeightedDebtSum theta candidate)
    (hpositive : 0 < quittingTerminalSemanticWeightedDebtSum theta pair)
    (htheta : ∀ who, 0 ≤ theta who)
    (hh : ∀ who, 0 ≤ h who)
    (hstrict : ∀ who, theta who * h who <
      quittingTerminalSemanticWeightedDebtSum theta pair)
    (hnash : IsεQuittingRootNash reward (pair.2 - h) 0 root) :
    root = (quittingAllContinueRoot : ι → PMF Bool) := by
  have hbudget := minimumTerminalSemantic_weightedAuxiliaryNash_budget
    (reward := reward) theta pair h root hM hreward hpair hminimum
      htheta hh hnash
  have hcollisionNonneg : 0 ≤ quittingRootCollisionMass root :=
    quittingRootCollisionMass_nonneg root
  have htermsNonneg : ∀ who ∈ (Finset.univ : Finset ι),
      0 ≤ quittingRootCoalitionMass root {who} *
        (quittingTerminalSemanticWeightedDebtSum theta pair -
          theta who * h who) := by
    intro who _
    exact mul_nonneg
      (MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg root {who})
      (sub_nonneg.mpr (hstrict who).le)
  have hsumNonneg : 0 ≤ ∑ who,
      quittingRootCoalitionMass root {who} *
        (quittingTerminalSemanticWeightedDebtSum theta pair -
          theta who * h who) := Finset.sum_nonneg htermsNonneg
  have hcollisionZero : quittingRootCollisionMass root = 0 := by
    nlinarith
  have hsumZero : ∑ who,
      quittingRootCoalitionMass root {who} *
        (quittingTerminalSemanticWeightedDebtSum theta pair -
          theta who * h who) = 0 := by
    rw [hcollisionZero, mul_zero, zero_add] at hbudget
    exact le_antisymm hbudget hsumNonneg
  have hzeroTerms :=
    (Finset.sum_eq_zero_iff_of_nonneg htermsNonneg).mp hsumZero
  have hsingletonZero : ∀ who,
      quittingRootCoalitionMass root {who} = 0 := by
    intro who
    have hproduct := hzeroTerms who (Finset.mem_univ who)
    have hcoefficient : 0 <
        quittingTerminalSemanticWeightedDebtSum theta pair -
          theta who * h who := sub_pos.mpr (hstrict who)
    nlinarith [MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg
      root {who}]
  have hsingletonSum : (∑ who,
      quittingRootCoalitionMass root {who}) = 0 :=
    Finset.sum_eq_zero fun who _ => hsingletonZero who
  have habsorption :=
    QuittingFiniteRootWindow.quittingRootAbsorptionMass_eq_sum_singletonMass_add_collisionMass
      root
  have habsorptionZero : quittingRootAbsorptionMass root = 0 := by
    rw [habsorption, hsingletonSum, hcollisionZero, zero_add]
  have hcontinue : quittingStationaryContinueMass root = 1 := by
    unfold quittingRootAbsorptionMass at habsorptionZero
    linarith
  funext who
  have hpure := eq_pure_false_of_quittingStationaryContinueMass_eq_one
    hcontinue who
  simpa [quittingAllContinueRoot] using hpure

/-- On the closed weighted moat, collision vanishes and every positive
singleton mass lies on a fully funded critical facet. -/
theorem minimumTerminalSemantic_weightedAuxiliaryNash_criticalFace
    (theta : Payoff ι) (pair : QuittingTerminalSemanticPair ι)
    (h : Payoff ι) (root : ι → PMF Bool) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticWeightedDebtSum theta pair ≤
        quittingTerminalSemanticWeightedDebtSum theta candidate)
    (hpositive : 0 < quittingTerminalSemanticWeightedDebtSum theta pair)
    (htheta : ∀ who, 0 ≤ theta who)
    (hh : ∀ who, 0 ≤ h who)
    (hle : ∀ who, theta who * h who ≤
      quittingTerminalSemanticWeightedDebtSum theta pair)
    (hnash : IsεQuittingRootNash reward (pair.2 - h) 0 root) :
    quittingRootCollisionMass root = 0 ∧
      ∀ who, 0 < quittingRootCoalitionMass root {who} →
        theta who * h who =
          quittingTerminalSemanticWeightedDebtSum theta pair := by
  have hbudget := minimumTerminalSemantic_weightedAuxiliaryNash_budget
    (reward := reward) theta pair h root hM hreward hpair hminimum
      htheta hh hnash
  have hcollisionNonneg : 0 ≤ quittingRootCollisionMass root :=
    quittingRootCollisionMass_nonneg root
  have htermsNonneg : ∀ who ∈ (Finset.univ : Finset ι),
      0 ≤ quittingRootCoalitionMass root {who} *
        (quittingTerminalSemanticWeightedDebtSum theta pair -
          theta who * h who) := by
    intro who _
    exact mul_nonneg
      (MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg root {who})
      (sub_nonneg.mpr (hle who))
  have hsumNonneg : 0 ≤ ∑ who,
      quittingRootCoalitionMass root {who} *
        (quittingTerminalSemanticWeightedDebtSum theta pair -
          theta who * h who) := Finset.sum_nonneg htermsNonneg
  have hcollisionZero : quittingRootCollisionMass root = 0 := by
    nlinarith
  have hsumZero : ∑ who,
      quittingRootCoalitionMass root {who} *
        (quittingTerminalSemanticWeightedDebtSum theta pair -
          theta who * h who) = 0 := by
    rw [hcollisionZero, mul_zero, zero_add] at hbudget
    exact le_antisymm hbudget hsumNonneg
  have hzeroTerms :=
    (Finset.sum_eq_zero_iff_of_nonneg htermsNonneg).mp hsumZero
  refine ⟨hcollisionZero, ?_⟩
  intro who hmass
  have hproduct := hzeroTerms who (Finset.mem_univ who)
  nlinarith

/-! ## Positive-costate minimum plateaus -/

/-- A positive costate gives the sharp weighted singleton margin
`m_theta ≤ theta_i * (b_i-s_i)`. -/
theorem minimumTerminalSemantic_weightedSingletonMargin
    (theta : Payoff ι) (pair : QuittingTerminalSemanticPair ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticWeightedDebtSum theta pair ≤
        quittingTerminalSemanticWeightedDebtSum theta candidate)
    (hpositive : 0 < quittingTerminalSemanticWeightedDebtSum theta pair)
    (htheta : ∀ who, 0 < theta who) (who : ι) :
    quittingTerminalSemanticWeightedDebtSum theta pair ≤
      theta who *
        (pair.2 who - reward (quittingSingletonTerminal who) who) := by
  let zeroShift : Payoff ι := fun _ => 0
  obtain ⟨zeroRoot, hzeroNash⟩ :=
    exists_isZeroQuittingRootNash (reward := reward) pair.2
  have hzeroRoot : zeroRoot =
      (quittingAllContinueRoot : ι → PMF Bool) := by
    apply minimumTerminalSemantic_weightedAuxiliaryNash_eq_allContinue
      (reward := reward) theta pair zeroShift zeroRoot hM hreward hpair
        hminimum hpositive (fun player => (htheta player).le)
    · intro player
      simp [zeroShift]
    · intro player
      simpa [zeroShift] using hpositive
    · have htail : pair.2 - zeroShift = pair.2 := by
        funext player
        simp [zeroShift]
      rw [htail]
      exact hzeroNash
  have hnashEnvelope : IsεQuittingRootNash reward pair.2 0
      (quittingAllContinueRoot : ι → PMF Bool) := by
    simpa [hzeroRoot] using hzeroNash
  have hsingletonLeEnvelope :
      reward (quittingSingletonTerminal who) who ≤ pair.2 who :=
    (isZeroQuittingRootNash_allContinue_iff_singleton_le
      reward pair.2).mp hnashEnvelope who
  by_contra hnot
  have hcostGap : theta who *
      (pair.2 who - reward (quittingSingletonTerminal who) who) <
        quittingTerminalSemanticWeightedDebtSum theta pair :=
    lt_of_not_ge hnot
  have hgapLt :
      pair.2 who - reward (quittingSingletonTerminal who) who <
        quittingTerminalSemanticWeightedDebtSum theta pair / theta who := by
    apply (lt_div_iff₀ (htheta who)).2
    simpa [mul_comm] using hcostGap
  let shift : Payoff ι := fun player =>
    if player = who then
      ((pair.2 who - reward (quittingSingletonTerminal who) who) +
        quittingTerminalSemanticWeightedDebtSum theta pair / theta who) / 2
    else 0
  have hshiftNonneg : ∀ player, 0 ≤ shift player := by
    intro player
    by_cases hplayer : player = who
    · subst player
      simp only [shift, if_pos]
      have hquotientPos : 0 <
          quittingTerminalSemanticWeightedDebtSum theta pair / theta who :=
        div_pos hpositive (htheta who)
      nlinarith
    · simp [shift, hplayer]
  have hshiftStrict : ∀ player, theta player * shift player <
      quittingTerminalSemanticWeightedDebtSum theta pair := by
    intro player
    by_cases hplayer : player = who
    · subst player
      have hmidLt :
          ((pair.2 who - reward (quittingSingletonTerminal who) who) +
            quittingTerminalSemanticWeightedDebtSum theta pair /
              theta who) / 2 <
            quittingTerminalSemanticWeightedDebtSum theta pair /
              theta who := by
        linarith
      have hcostMid := (lt_div_iff₀ (htheta who)).mp hmidLt
      simpa [shift, mul_comm] using hcostMid
    · simp [shift, hplayer, hpositive]
  obtain ⟨root, hnash⟩ := exists_isZeroQuittingRootNash
    (reward := reward) (pair.2 - shift)
  have hroot : root = (quittingAllContinueRoot : ι → PMF Bool) :=
    minimumTerminalSemantic_weightedAuxiliaryNash_eq_allContinue
      (reward := reward) theta pair shift root hM hreward hpair hminimum
        hpositive (fun player => (htheta player).le) hshiftNonneg
          hshiftStrict hnash
  have hnashAll : IsεQuittingRootNash reward (pair.2 - shift) 0
      (quittingAllContinueRoot : ι → PMF Bool) := by
    simpa [hroot] using hnash
  have hsingletonAux :=
    (isZeroQuittingRootNash_allContinue_iff_singleton_le
      reward (pair.2 - shift)).mp hnashAll who
  have hshiftWho : shift who =
      ((pair.2 who - reward (quittingSingletonTerminal who) who) +
        quittingTerminalSemanticWeightedDebtSum theta pair / theta who) / 2 :=
    by simp [shift]
  rw [Pi.sub_apply, hshiftWho] at hsingletonAux
  linarith

/-- Every positive weighted minimum for a strictly positive costate is again
an exact all-Continue Nash self-loop at its prescribed payoff. -/
theorem minimumTerminalSemantic_weightedIs_allContinuePlateau
    (theta : Payoff ι) (pair : QuittingTerminalSemanticPair ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticWeightedDebtSum theta pair ≤
        quittingTerminalSemanticWeightedDebtSum theta candidate)
    (hpositive : 0 < quittingTerminalSemanticWeightedDebtSum theta pair)
    (htheta : ∀ who, 0 < theta who) :
    IsεQuittingRootNash reward pair.1 0
        (quittingAllContinueRoot : ι → PMF Bool) ∧
      quittingTerminalSemanticPrefix reward quittingAllContinueRoot pair =
        pair := by
  have hdebtNonneg : ∀ who,
      0 ≤ quittingTerminalSemanticDebt pair who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hM hreward hpair
  have hcostNonneg : ∀ who,
      0 ≤ theta who * quittingTerminalSemanticDebt pair who :=
    fun who => mul_nonneg (htheta who).le (hdebtNonneg who)
  have hsingleton : ∀ who,
      reward (quittingSingletonTerminal who) who ≤ pair.1 who := by
    intro who
    have hmargin := minimumTerminalSemantic_weightedSingletonMargin
      (reward := reward) theta pair hM hreward hpair hminimum hpositive
        htheta who
    have hcoordinateLe : theta who *
        quittingTerminalSemanticDebt pair who ≤
          quittingTerminalSemanticWeightedDebtSum theta pair := by
      unfold quittingTerminalSemanticWeightedDebtSum
      exact Finset.single_le_sum
        (fun player _ => hcostNonneg player) (Finset.mem_univ who)
    have hdebtLeGap : quittingTerminalSemanticDebt pair who ≤
        pair.2 who - reward (quittingSingletonTerminal who) who := by
      have hscaled : theta who * quittingTerminalSemanticDebt pair who ≤
          theta who *
            (pair.2 who - reward (quittingSingletonTerminal who) who) :=
        hcoordinateLe.trans hmargin
      nlinarith [hscaled, htheta who]
    unfold quittingTerminalSemanticDebt at hdebtLeGap
    linarith
  have hnash :=
    (isZeroQuittingRootNash_allContinue_iff_singleton_le reward pair.1).mpr
      hsingleton
  exact ⟨hnash,
    quittingTerminalSemanticPrefix_allContinue_eq_of_isZeroNash
      reward pair hdebtNonneg hnash⟩

end GameTheory
