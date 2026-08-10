/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeReachableCarryTelescope
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentSupportLiftFarkas
import UniformEquilibrium.Quitting.Boundary.Repair.SureSetOwnerRepair

/-!
# A frozen-root alternative for funding the terminal singleton cap

The terminal point of a finite zero-boundary Nash--Bellman chain has payoff
zero, but its stored product root is unconstrained.  This file observes that
the global floor-admissible path potential depends only on the payoff
coordinate: the first edge of any nonempty path may be re-rooted at another
state with the same payoff.  Consequently an incoming edge to *any* boxed
zero-payoff root reserves capacity at the selected terminal point.

For a supplied product root, the frozen-root affine alternative therefore
gives either a literal incoming exact edge which funds the terminal cap, or
an explicit finite Farkas certificate for that root.  The result does not
assert that the certificate rules out every product root.  In particular,
the strict-interior support decoder does not cover the pure-Quit boundary.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Finset
open Math.ChargedPathBudget
open Math.ProbabilityMassFunction
open QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

private abbrev AdmissibleRelation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :=
  quittingPunishmentFloorAdmissibleChargedRelation reward

/-! ## The admissible potential ignores the stored root -/

private theorem chargesFrom_subset_of_payoff_eq
    (first second : QuittingPunishmentFloorAdmissibleState reward)
    (hpayoff : first.1.1.1 = second.1.1.1) :
    (AdmissibleRelation reward).chargesFrom first ⊆
      (AdmissibleRelation reward).chargesFrom second := by
  rintro charge ⟨target, segment, rfl⟩
  cases segment with
  | nil state =>
      exact (AdmissibleRelation reward).zero_mem_chargesFrom second
  | cons edge rest =>
      let rerooted : QuittingPunishmentFloorAdmissibleEdge reward :=
        { tail := second
          current := edge.current
          exactEdge := by
            constructor
            · rw [← hpayoff]
              exact edge.exactEdge.1
            · rw [← hpayoff]
              exact edge.exactEdge.2 }
      refine ⟨_, .cons rerooted rest, ?_⟩
      simp [rerooted, AdmissibleRelation,
        quittingPunishmentFloorAdmissibleChargedRelation,
        QuittingPunishmentFloorAdmissibleEdge.toBoxEdge,
        QuittingPunishmentFloorBoxEdge.absorptionCharge,
        QuittingPunishmentFloorBoxEdge.root]

/-- The full floor-admissible path potential depends only on the payoff
coordinate, not on the product root stored alongside it.  The empty path is
replaced by an empty path and a nonempty path is re-rooted at its first edge. -/
theorem quittingPunishmentFloorAdmissiblePotential_eq_of_payoff_eq
    (first second : QuittingPunishmentFloorAdmissibleState reward)
    (hpayoff : first.1.1.1 = second.1.1.1) :
    quittingPunishmentFloorAdmissiblePotential reward first =
      quittingPunishmentFloorAdmissiblePotential reward second := by
  have hsets : (AdmissibleRelation reward).chargesFrom first =
      (AdmissibleRelation reward).chargesFrom second := by
    apply Set.Subset.antisymm
    · exact chargesFrom_subset_of_payoff_eq first second hpayoff
    · exact chargesFrom_subset_of_payoff_eq second first hpayoff.symm
  unfold quittingPunishmentFloorAdmissiblePotential ChargedRelation.value
  rw [hsets]

/-! ## A canonical strictly mixed one-owner funding root -/

omit [Fintype ι] in
/-- A one-owner root with hazard strictly between zero and one has precisely
that owner as its interior support. -/
theorem isQuittingRootInteriorOnSupport_sureSetOwnerRoot_empty
    (owner : ι) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    IsQuittingRootInteriorOnSupport
      (quittingSureSetOwnerRoot ∅ owner p hp0.le hp1.le) {owner} := by
  constructor
  · intro who hwho
    have hwho' : who = owner := by simpa using hwho
    subst who
    simpa [hazardOfRoot, quittingSureSetOwnerRoot] using And.intro hp0 hp1
  · intro who hwho
    have hne : who ≠ owner := by simpa using hwho
    simp [hazardOfRoot, quittingSureSetOwnerRoot, quittingPureSetRoot,
      quittingSetAction, Function.update, hne]

/-- The literal absorption mass of the strictly mixed one-owner root is its
hazard. -/
theorem quittingRootAbsorptionMass_sureSetOwnerRoot_empty
    (owner : ι) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    quittingRootAbsorptionMass
      (quittingSureSetOwnerRoot ∅ owner p hp0 hp1) = p := by
  unfold quittingRootAbsorptionMass
  rw [stationaryContinueMass_sureSetOwnerRoot_empty]
  ring

/-- A pure singleton quitter cannot have zero Bellman target when its own
positive singleton debt cap is nonzero.  This is the exact one-stage
obstruction at the hazard-one boundary; it is independent of Nash signs. -/
theorem not_exists_zeroTarget_pureSingletonContinuation
    (owner : ι) (hcap : 0 < quittingPositiveSingletonDebtCap reward owner) :
    ¬ ∃ continuation : Payoff ι,
      (0 : Payoff ι) = quittingRootSuccessorPayoff reward continuation
        (quittingPureSetRoot {owner}) := by
  rintro ⟨continuation, hbellman⟩
  have howner := congrFun hbellman owner
  have hnonempty : ({owner} : Finset ι).Nonempty := singleton_nonempty owner
  change 0 = quittingRootExpectedPayoff reward continuation
    (quittingPureSetRoot {owner}) owner at howner
  rw [quittingRootExpectedPayoff_eq_absorbingContribution_add,
    quittingRootAbsorbingContribution_pureSetRoot,
    stationaryContinueMass_pureSetRoot_of_nonempty hnonempty,
    zero_mul, add_zero] at howner
  have hrewards : reward (quittingSingletonTerminal owner) owner = 0 := by
    simpa [quittingSetReward, quittingSingletonTerminal] using howner.symm
  rw [quittingPositiveSingletonDebtCap, hrewards, max_self] at hcap
  exact lt_irrefl 0 hcap

/-- The finite Farkas data certifying infeasibility of one supplied frozen
product-root continuation system. -/
def HasQuittingFrozenRootLiftFarkasCertificate
    (target floor : Payoff ι) (upper : ℝ) (root : ι → PMF Bool)
    (support : Finset ι) : Prop :=
  (¬ ∃ continuation,
    IsQuittingFrozenRootContinuationLift reward target floor upper
      root support continuation) ∧
    ∃ y : QuittingFrozenRootLiftEqRow ι support → ℝ,
      ∃ lambda : QuittingFrozenRootLiftIneqRow ι support → ℝ,
        IsQuittingFrozenRootLiftFarkasCertificate reward target floor upper
          root support y lambda

/-! ## Boxed states supplied by a physical frozen-root lift -/

/-- Any product root can be attached to the zero payoff as a boxed
floor-admissible state when the punishment floor is nonpositive. -/
def quittingZeroPayoffAdmissibleState
    (hpunishment : ∀ who, quittingPunishmentValue reward who ≤ 0)
    (root : ι → PMF Bool) :
    QuittingPunishmentFloorAdmissibleState reward := by
  refine ⟨⟨((0, quittingFrozenRootLiftSimplex root)), ?_⟩, hpunishment⟩
  change (0 : Payoff ι) ∈ Set.Icc
    (fun _ => -quittingRewardBound reward)
    (fun _ => quittingRewardBound reward)
  constructor
  · intro who
    exact neg_nonpos.mpr (quittingRewardBound_nonneg reward)
  · intro who
    exact quittingRewardBound_nonneg reward

/-- The continuation side of a physical frozen-root lift is a boxed
floor-admissible state. -/
def quittingFrozenRootContinuationAdmissibleState
    (target : Payoff ι) (root : ι → PMF Bool) (support : Finset ι)
    (continuation : Payoff ι)
    (hlift : IsQuittingFrozenRootContinuationLift reward target
      (quittingPunishmentValue reward) (quittingRewardBound reward)
      root support continuation)
    (tailRoot : QuittingRootSimplex ι) :
    QuittingPunishmentFloorAdmissibleState reward := by
  refine ⟨⟨((continuation, tailRoot)), ?_⟩, hlift.2.2.2.1⟩
  constructor
  · intro who
    exact (neg_quittingRewardBound_le_quittingPunishmentValue reward who).trans
      (hlift.2.2.2.1 who)
  · exact hlift.2.2.2.2

namespace QuittingFiniteDynamicDebtAdmissibleChronology

variable {cutoff : ℕ}
variable (path : QuittingFiniteNashBellmanPath ι cutoff)
variable (hpath : path ∈
  quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff)
variable (hpunishment : ∀ who, quittingPunishmentValue reward who ≤ 0)

/-- A physical frozen-root lift whose one-stage absorption charge pays the
terminal singleton debt closes the remaining far-boundary gate.  The edge
lands at a zero-payoff state carrying the supplied root; potential invariance
transfers its reserved capacity to the selected terminal root. -/
theorem debt_zero_le_aggregateCapacityAccount_zero_of_frozenRootLift
    (regime : QuittingCounterexampleRegime reward)
    (root : ι → PMF Bool) (support : Finset ι)
    (hsupport : IsQuittingRootInteriorOnSupport root support)
    (continuation : Payoff ι)
    (hlift : IsQuittingFrozenRootContinuationLift reward 0
      (quittingPunishmentValue reward) (quittingRewardBound reward)
      root support continuation)
    (tailRoot : QuittingRootSimplex ι)
    (hpays : debt (reward := reward) path cutoff ≤
      (Fintype.card ι : ℝ) * quittingRewardBound reward *
        quittingRootAbsorptionMass root) :
    debt (reward := reward) path 0 ≤
      aggregateCapacityAccount path hpath hpunishment 0 := by
  let sourceState := quittingFrozenRootContinuationAdmissibleState
    (reward := reward) 0 root support continuation hlift tailRoot
  let zeroState := quittingZeroPayoffAdmissibleState
    (reward := reward) hpunishment root
  let edge : QuittingPunishmentFloorAdmissibleEdge reward :=
    { tail := sourceState
      current := zeroState
      exactEdge := isQuittingNashBellmanEdge_of_frozenRootContinuationLift
        0 (quittingPunishmentValue reward) (quittingRewardBound reward)
        root support continuation hlift hsupport tailRoot }
  have hpotential : quittingPunishmentFloorAdmissiblePotential reward zeroState =
      quittingPunishmentFloorAdmissiblePotential reward
        (quittingFiniteDynamicDebtAdmissibleState
          path hpath hpunishment cutoff) := by
    apply quittingPunishmentFloorAdmissiblePotential_eq_of_payoff_eq
    change (0 : Payoff ι) =
      (quittingFiniteNashBellmanPathDynamicDebtPoint
        reward cutoff path cutoff).1.1
    exact (terminal_payoff_eq_zero path hpath).symm
  have hdecrement :=
    quittingPunishmentFloorAdmissiblePotential_predecessor_decrement
      regime.prefixCharge_le edge
  have hsource := admissiblePotential_le_prefixChargeBound regime sourceState
  have hcharge : edge.toBoxEdge.absorptionCharge =
      quittingRootAbsorptionMass root := by
    change quittingRootAbsorptionMass
      (quittingRootOfSimplex (quittingFrozenRootLiftSimplex root)) =
        quittingRootAbsorptionMass root
    rw [quittingRootOfSimplex_frozenRootLiftSimplex]
  apply debt_zero_le_aggregateCapacityAccount_zero_of_far
    path hpath hpunishment regime
  have hscale : 0 ≤ (Fintype.card ι : ℝ) * quittingRewardBound reward :=
    mul_nonneg (Nat.cast_nonneg _) (quittingRewardBound_nonneg reward)
  calc
    debt (reward := reward) path cutoff ≤
        (Fintype.card ι : ℝ) * quittingRewardBound reward *
          quittingRootAbsorptionMass root := hpays
    _ = (Fintype.card ι : ℝ) * quittingRewardBound reward *
          edge.toBoxEdge.absorptionCharge := by rw [hcharge]
    _ ≤ (Fintype.card ι : ℝ) * quittingRewardBound reward *
        remainingCapacity path hpath hpunishment cutoff := by
      apply mul_le_mul_of_nonneg_left _ hscale
      unfold remainingCapacity
      rw [← hpotential]
      linarith
    _ = aggregateCapacityAccount path hpath hpunishment cutoff := rfl

/-- **Incoming frozen-root alternative.**  For any supplied interior-support
product root whose literal absorption would fund the terminal cap, either
the intrinsic carry gate closes by a genuine one-edge predecessor, or finite
Farkas multipliers certify infeasibility of the continuation system for that
specific root. -/
theorem debt_zero_le_aggregateCapacityAccount_zero_or_farkas_of_fundingRoot
    (regime : QuittingCounterexampleRegime reward)
    (root : ι → PMF Bool) (support : Finset ι)
    (hsupport : IsQuittingRootInteriorOnSupport root support)
    (tailRoot : QuittingRootSimplex ι)
    (hpays : debt (reward := reward) path cutoff ≤
      (Fintype.card ι : ℝ) * quittingRewardBound reward *
        quittingRootAbsorptionMass root) :
    (debt (reward := reward) path 0 ≤
      aggregateCapacityAccount path hpath hpunishment 0 ∧
        ∃ continuation,
          IsQuittingFrozenRootContinuationLift reward 0
            (quittingPunishmentValue reward) (quittingRewardBound reward)
            root support continuation ∧
          IsQuittingNashBellmanEdge reward
            (0, quittingFrozenRootLiftSimplex root)
            (continuation, tailRoot)) ∨
      ((¬ ∃ continuation,
        IsQuittingFrozenRootContinuationLift reward 0
          (quittingPunishmentValue reward) (quittingRewardBound reward)
          root support continuation) ∧
        ∃ y : QuittingFrozenRootLiftEqRow ι support → ℝ,
          ∃ lambda : QuittingFrozenRootLiftIneqRow ι support → ℝ,
            IsQuittingFrozenRootLiftFarkasCertificate reward 0
              (quittingPunishmentValue reward) (quittingRewardBound reward)
              root support y lambda) := by
  rcases quittingFrozenRootNashBellmanEdge_or_farkas
      (reward := reward) 0 (quittingPunishmentValue reward)
      (quittingRewardBound reward) root support hsupport tailRoot with
    ⟨continuation, hlift, hedge⟩ | hfarkas
  · left
    exact ⟨debt_zero_le_aggregateCapacityAccount_zero_of_frozenRootLift
      path hpath hpunishment regime root support hsupport continuation hlift
        tailRoot hpays, continuation, hlift, hedge⟩
  · exact Or.inr hfarkas

/-- **Strict terminal-cap alternative without a funding premise.**  If the
aggregate terminal debt is positive but strictly below the universal
`card * rewardBound` scale, a canonical single-owner hazard is chosen whose
one-stage absorption charge funds that debt exactly.  Either its frozen
continuation system produces the required incoming edge and closes the carry
gate, or the returned finite multipliers certify infeasibility for this
explicit funding root.

The saturated boundary where terminal debt equals the full scale is not
covered: it would force hazard one, outside the strict-interior support
decoder used by the affine alternative. -/
theorem strict_terminalDebt_fundingEdge_or_farkas
    (regime : QuittingCounterexampleRegime reward)
    (owner : ι) (tailRoot : QuittingRootSimplex ι)
    (hpositive : 0 < debt (reward := reward) path cutoff)
    (hstrict : debt (reward := reward) path cutoff <
      (Fintype.card ι : ℝ) * quittingRewardBound reward) :
    (debt (reward := reward) path 0 ≤
        aggregateCapacityAccount path hpath hpunishment 0 ∧
      ∃ root : ι → PMF Bool, ∃ support : Finset ι, ∃ continuation,
        IsQuittingRootInteriorOnSupport root support ∧
        (Fintype.card ι : ℝ) * quittingRewardBound reward *
            quittingRootAbsorptionMass root =
          debt (reward := reward) path cutoff ∧
        IsQuittingFrozenRootContinuationLift reward 0
          (quittingPunishmentValue reward) (quittingRewardBound reward)
          root support continuation ∧
        IsQuittingNashBellmanEdge reward
          (0, quittingFrozenRootLiftSimplex root)
          (continuation, tailRoot)) ∨
      ∃ root : ι → PMF Bool, ∃ support : Finset ι,
        IsQuittingRootInteriorOnSupport root support ∧
        (Fintype.card ι : ℝ) * quittingRewardBound reward *
            quittingRootAbsorptionMass root =
          debt (reward := reward) path cutoff ∧
        HasQuittingFrozenRootLiftFarkasCertificate (reward := reward) 0
          (quittingPunishmentValue reward) (quittingRewardBound reward)
          root support := by
  let scale := (Fintype.card ι : ℝ) * quittingRewardBound reward
  let terminalDebt := debt (reward := reward) path cutoff
  have hscale : 0 < scale := by
    dsimp [scale, terminalDebt] at hstrict ⊢
    linarith
  let p := terminalDebt / scale
  have hp0 : 0 < p := div_pos (by simpa [terminalDebt] using hpositive) hscale
  have hp1 : p < 1 := (div_lt_one hscale).2 (by
    simpa [terminalDebt, scale] using hstrict)
  let root := quittingSureSetOwnerRoot ∅ owner p hp0.le hp1.le
  let support : Finset ι := {owner}
  have hsupport : IsQuittingRootInteriorOnSupport root support := by
    exact isQuittingRootInteriorOnSupport_sureSetOwnerRoot_empty owner p hp0 hp1
  have habsorption : quittingRootAbsorptionMass root = p := by
    exact quittingRootAbsorptionMass_sureSetOwnerRoot_empty
      owner p hp0.le hp1.le
  have hfunds : scale * quittingRootAbsorptionMass root = terminalDebt := by
    rw [habsorption]
    dsimp [p]
    field_simp
  have hpays : debt (reward := reward) path cutoff ≤
      (Fintype.card ι : ℝ) * quittingRewardBound reward *
        quittingRootAbsorptionMass root := by
    change terminalDebt ≤ scale * quittingRootAbsorptionMass root
    rw [hfunds]
  rcases debt_zero_le_aggregateCapacityAccount_zero_or_farkas_of_fundingRoot
      path hpath hpunishment regime root support hsupport tailRoot hpays with
    ⟨hcarry, continuation, hlift, hedge⟩ | hfarkas
  · left
    refine ⟨hcarry, root, support, continuation, hsupport, ?_, hlift, hedge⟩
    simpa [scale, terminalDebt] using hfunds
  · right
    refine ⟨root, support, hsupport, ?_, hfarkas⟩
    simpa [scale, terminalDebt] using hfunds

/-- Saturation of the universal `card * rewardBound` estimate forces every
player's positive singleton cap to attain the reward bound.  Thus, when the
scale is positive, every such cap is strictly positive. -/
theorem positiveSingletonDebtCap_pos_of_terminalDebt_eq_scale
    (hscale : 0 < (Fintype.card ι : ℝ) * quittingRewardBound reward)
    (hsaturated : debt (reward := reward) path cutoff =
      (Fintype.card ι : ℝ) * quittingRewardBound reward)
    (owner : ι) :
    0 < quittingPositiveSingletonDebtCap reward owner := by
  have hcap_le (who : ι) :
      quittingPositiveSingletonDebtCap reward who ≤
        quittingRewardBound reward :=
    (le_abs_self _).trans
      (abs_quittingPositiveSingletonDebtCap_le_rewardBound reward who)
  have hsum : (∑ who, quittingPositiveSingletonDebtCap reward who) =
      (Fintype.card ι : ℝ) * quittingRewardBound reward := by
    rw [← debt_cutoff_eq_sum_positiveSingletonDebtCap path]
    exact hsaturated
  have howner_eq : quittingPositiveSingletonDebtCap reward owner =
      quittingRewardBound reward := by
    apply le_antisymm (hcap_le owner)
    by_contra hnot
    have howner_lt : quittingPositiveSingletonDebtCap reward owner <
        quittingRewardBound reward := lt_of_not_ge hnot
    have hsum_lt : (∑ who, quittingPositiveSingletonDebtCap reward who) <
        ∑ _who : ι, quittingRewardBound reward := by
      apply Finset.sum_lt_sum
      · intro who _
        exact hcap_le who
      · exact ⟨owner, Finset.mem_univ owner, howner_lt⟩
    have : (∑ who, quittingPositiveSingletonDebtCap reward who) <
        (Fintype.card ι : ℝ) * quittingRewardBound reward := by
      simpa using hsum_lt
    linarith
  have hcard : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨owner⟩
  have hbound : 0 < quittingRewardBound reward := by
    nlinarith
  rw [howner_eq]
  exact hbound

/-- At a positive saturated terminal cap, the obvious full-charge
single-owner pure-Quit predecessor is Bellman-infeasible for every owner.
Thus the strict theorem's missing hazard-one endpoint is a genuine target
obstruction, not merely an omission in the support decoder.  This does not
exclude more complicated full-absorption product roots. -/
theorem saturated_terminalDebt_no_pureSingleton_incomingEdge
    (hscale : 0 < (Fintype.card ι : ℝ) * quittingRewardBound reward)
    (hsaturated : debt (reward := reward) path cutoff =
      (Fintype.card ι : ℝ) * quittingRewardBound reward)
    (owner : ι) (tailRoot : QuittingRootSimplex ι) :
    ¬ ∃ continuation : Payoff ι,
      IsQuittingNashBellmanEdge reward
        (0, quittingFrozenRootLiftSimplex (quittingPureSetRoot {owner}))
        (continuation, tailRoot) := by
  rintro ⟨continuation, hedge⟩
  apply not_exists_zeroTarget_pureSingletonContinuation owner
    (positiveSingletonDebtCap_pos_of_terminalDebt_eq_scale
      path hscale hsaturated owner)
  refine ⟨continuation, ?_⟩
  simpa [quittingRootOfSimplex_frozenRootLiftSimplex] using hedge.1

end QuittingFiniteDynamicDebtAdmissibleChronology

end GameTheory
