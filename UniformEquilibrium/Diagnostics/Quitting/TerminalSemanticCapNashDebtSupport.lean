/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticAuxiliaryNashBudget

/-!
# Cap--Nash debt support above the minimum semantic debt

An exact Nash root selected against an auxiliary cap need not be executable as
a common continuation.  Prefixing the original semantic pair nevertheless
gives an executable carrier point.  Comparing its debt with the minimum debt
therefore charges every absorbing part of the auxiliary root to the displayed
debt excess.

For an exact Nash root against the prescribed coordinate itself, the charge is

`D * collision + sum_i singleton_i * (D - d_i) <= D - D_min`.

Thus a near-minimum root can absorb only through an almost full-debt player;
away from the vertices of the normalized debt simplex its entire absorption
probability vanishes quantitatively.  This is a finite-dimensional support
statement.  It does not identify an absorbing label along a later chronology.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Auxiliary-cap absorption is paid for by excess above the minimum semantic
debt.  This is the non-minimal version of the auxiliary Nash budget. -/
theorem terminalSemantic_auxiliaryNash_excess_budget
    (base pair : QuittingTerminalSemanticPair ι)
    (h : Payoff ι) (root : ι → PMF Bool) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum base ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hh : ∀ who, 0 ≤ h who)
    (hnash : IsεQuittingRootNash reward (pair.2 - h) 0 root) :
    quittingTerminalSemanticDebtSum pair *
          quittingRootCollisionMass root +
        ∑ who, quittingRootCoalitionMass root {who} *
          (quittingTerminalSemanticDebtSum pair - h who) ≤
      quittingTerminalSemanticDebtSum pair -
        quittingTerminalSemanticDebtSum base := by
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
  have hbasePrefix : quittingTerminalSemanticDebtSum base ≤
      quittingTerminalSemanticDebtSum prefixed :=
    hminimum prefixed hprefixed
  have hraw : quittingTerminalSemanticDebtSum base ≤
      quittingStationaryContinueMass root *
          quittingTerminalSemanticDebtSum pair +
        ∑ who, quittingRootCoalitionMass root {who} * h who :=
    hbasePrefix.trans hsum
  have habsorption :=
    QuittingFiniteRootWindow.quittingRootAbsorptionMass_eq_sum_singletonMass_add_collisionMass
      root
  unfold quittingRootAbsorptionMass at habsorption
  calc
    quittingTerminalSemanticDebtSum pair *
          quittingRootCollisionMass root +
        ∑ who, quittingRootCoalitionMass root {who} *
          (quittingTerminalSemanticDebtSum pair - h who) =
      ((∑ who, quittingRootCoalitionMass root {who}) +
          quittingRootCollisionMass root) *
          quittingTerminalSemanticDebtSum pair -
        ∑ who, quittingRootCoalitionMass root {who} * h who := by
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
        ring
    _ = (1 - quittingStationaryContinueMass root) *
          quittingTerminalSemanticDebtSum pair -
        ∑ who, quittingRootCoalitionMass root {who} * h who := by
      rw [habsorption]
    _ =
      quittingTerminalSemanticDebtSum pair -
        (quittingStationaryContinueMass root *
            quittingTerminalSemanticDebtSum pair +
          ∑ who, quittingRootCoalitionMass root {who} * h who) := by
        ring
    _ ≤ quittingTerminalSemanticDebtSum pair -
          quittingTerminalSemanticDebtSum base :=
      sub_le_sub_left hraw _

/-- For a root which is exact Nash against the prescribed payoff, collision
and singleton absorption are charged by the complementary debt. -/
theorem terminalSemantic_exactNash_nearMinimum_support_budget
    (base pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum base ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hnash : IsεQuittingRootNash reward pair.1 0 root) :
    quittingTerminalSemanticDebtSum pair *
          quittingRootCollisionMass root +
        ∑ who, quittingRootCoalitionMass root {who} *
          (quittingTerminalSemanticDebtSum pair -
            quittingTerminalSemanticDebt pair who) ≤
      quittingTerminalSemanticDebtSum pair -
        quittingTerminalSemanticDebtSum base := by
  let debt : Payoff ι := fun who => quittingTerminalSemanticDebt pair who
  have hdebt : ∀ who, 0 ≤ debt who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hM hreward hpair
  have htail : pair.2 - debt = pair.1 := by
    funext who
    dsimp [debt, quittingTerminalSemanticDebt]
    ring
  have hnashAux : IsεQuittingRootNash reward (pair.2 - debt) 0 root := by
    rw [htail]
    exact hnash
  simpa [debt] using terminalSemantic_auxiliaryNash_excess_budget
    (reward := reward) base pair debt root hM hreward hminimum hpair
      hdebt hnashAux

/-- If every debt coordinate stays at least `kappa` away from carrying the
whole debt, the full one-stage absorption probability is bounded by debt
excess divided by `kappa`. -/
theorem kappa_mul_rootAbsorptionMass_le_debtExcess_of_exactNash
    (base pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (kappa : ℝ) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum base ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hnash : IsεQuittingRootNash reward pair.1 0 root)
    (hkappaTotal : kappa ≤ quittingTerminalSemanticDebtSum pair)
    (hkappaComplement : ∀ who,
      kappa ≤ quittingTerminalSemanticDebtSum pair -
        quittingTerminalSemanticDebt pair who) :
    kappa * quittingRootAbsorptionMass root ≤
      quittingTerminalSemanticDebtSum pair -
        quittingTerminalSemanticDebtSum base := by
  have hbudget := terminalSemantic_exactNash_nearMinimum_support_budget
    (reward := reward) base pair root hM hreward hminimum hpair hnash
  have hcollisionNonneg : 0 ≤ quittingRootCollisionMass root :=
    quittingRootCollisionMass_nonneg root
  have hcollision : kappa * quittingRootCollisionMass root ≤
      quittingTerminalSemanticDebtSum pair *
        quittingRootCollisionMass root :=
    mul_le_mul_of_nonneg_right hkappaTotal hcollisionNonneg
  have hsingleton :
      (∑ who, quittingRootCoalitionMass root {who} * kappa) ≤
        ∑ who, quittingRootCoalitionMass root {who} *
          (quittingTerminalSemanticDebtSum pair -
            quittingTerminalSemanticDebt pair who) := by
    apply Finset.sum_le_sum
    intro who _
    exact mul_le_mul_of_nonneg_left (hkappaComplement who)
      (MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg root {who})
  have habsorption :=
    QuittingFiniteRootWindow.quittingRootAbsorptionMass_eq_sum_singletonMass_add_collisionMass
      root
  calc
    kappa * quittingRootAbsorptionMass root =
        kappa * quittingRootCollisionMass root +
          ∑ who, quittingRootCoalitionMass root {who} * kappa := by
      rw [habsorption, ← Finset.sum_mul]
      ring
    _ ≤ quittingTerminalSemanticDebtSum pair *
          quittingRootCollisionMass root +
        ∑ who, quittingRootCoalitionMass root {who} *
          (quittingTerminalSemanticDebtSum pair -
            quittingTerminalSemanticDebt pair who) :=
      add_le_add hcollision hsingleton
    _ ≤ quittingTerminalSemanticDebtSum pair -
          quittingTerminalSemanticDebtSum base := hbudget

end GameTheory
