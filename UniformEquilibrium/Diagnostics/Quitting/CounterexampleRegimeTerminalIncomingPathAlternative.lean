/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeReachableCarryTelescope
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeDebtSourceDynamicAlternative
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeSmallPlayers
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

noncomputable section

namespace GameTheory

open Finset
open Math.ChargedPathBudget
open Math.LinearProgramming.FlowCostateDuality
open Math.ProbabilityMassFunction
open QuittingFiniteDynamicDebtAdmissibleChronology
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

omit [DecidableEq ι] in
/-- The aggregate positive-singleton terminal debt uses only diagonal
coordinates of singleton reward rows, so it is bounded by the canonical
sum-of-all-absolute-rewards bound itself, without a player-cardinality
factor. -/
theorem sum_positiveSingletonDebtCap_le_quittingRewardBound :
    (∑ who, quittingPositiveSingletonDebtCap reward who) ≤
      quittingRewardBound reward := by
  classical
  let row : {S : Finset ι // S.Nonempty} → ℝ :=
    fun terminal ↦ ∑ who, |reward terminal who|
  have hinjective : Function.Injective
      (quittingSingletonTerminal : ι → {S : Finset ι // S.Nonempty}) := by
    intro first second heq
    have hval : ({first} : Finset ι) = {second} :=
      congrArg Subtype.val heq
    simpa using hval
  have hdiagonal : (∑ who, quittingPositiveSingletonDebtCap reward who) ≤
      ∑ who, row (quittingSingletonTerminal who) := by
    apply Finset.sum_le_sum
    intro who _
    calc
      quittingPositiveSingletonDebtCap reward who ≤
          |reward (quittingSingletonTerminal who) who| := by
        unfold quittingPositiveSingletonDebtCap
        exact max_le (abs_nonneg _) (le_abs_self _)
      _ ≤ row (quittingSingletonTerminal who) := by
        exact Finset.single_le_sum
          (fun player _ ↦ abs_nonneg (reward (quittingSingletonTerminal who) player))
          (Finset.mem_univ who)
  have hrows : (∑ who, row (quittingSingletonTerminal who)) ≤
      ∑ terminal, row terminal := by
    rw [← Finset.sum_image (s := (Finset.univ : Finset ι))
      (f := row) hinjective.injOn]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _)
      (fun terminal _ _ ↦ Finset.sum_nonneg
        (fun who _ ↦ abs_nonneg (reward terminal who)))
  exact hdiagonal.trans (by
    simpa [quittingRewardBound, row] using hrows)

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
terminal singleton debt proves the exact terminal boundary comparison.  The
edge lands at a zero-payoff state carrying the supplied root; potential
invariance transfers its reserved capacity to the selected terminal root. -/
theorem terminal_debt_le_aggregateCapacityAccount_of_frozenRootLift
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
    debt (reward := reward) path cutoff ≤
      aggregateCapacityAccount path hpath hpunishment cutoff := by
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

/-- The terminal comparison from a physical frozen-root lift closes the
entire intrinsic carry telescope. -/
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
  apply debt_zero_le_aggregateCapacityAccount_zero_of_far
    path hpath hpunishment regime
  exact terminal_debt_le_aggregateCapacityAccount_of_frozenRootLift
    path hpath hpunishment regime root support hsupport continuation hlift
      tailRoot hpays

include hpath in
/-- Aggregate diagonal debt source is nonnegative at every displayed point. -/
theorem source_nonneg (time : ℕ) :
    0 ≤ source (reward := reward) path time := by
  unfold source
  exact Finset.sum_nonneg (fun who _ ↦
    quittingDynamicDebtSeam_nonneg
      (quittingFiniteNashBellmanPathDynamicDebtPoint
        reward cutoff path time)
      (quittingFiniteNashBellmanPathDynamicDebtPoint_mem_box
        reward cutoff path hpath time) who)

include hpath in
/-- Aggregate exact debt is nonnegative at every displayed point. -/
theorem debt_nonneg (time : ℕ) :
    0 ≤ debt (reward := reward) path time := by
  unfold debt
  exact Finset.sum_nonneg (fun who _ ↦
    (quittingFiniteNashBellmanPathDynamicDebtPoint_mem_box
      reward cutoff path hpath time).2.1 who)

/-- A terminal capacity comparison propagates to every earlier point of the
same intrinsic finite chronology. -/
theorem debt_le_aggregateCapacityAccount_of_far_at
    (regime : QuittingCounterexampleRegime reward)
    (hfar : debt (reward := reward) path cutoff ≤
      aggregateCapacityAccount path hpath hpunishment cutoff) :
    ∀ time, time ≤ cutoff →
      debt (reward := reward) path time ≤
        aggregateCapacityAccount path hpath hpunishment time := by
  intro time htime
  exact Nat.decreasingInduction (n := cutoff) (motive := fun time _ ↦
      debt (reward := reward) path time ≤
        aggregateCapacityAccount path hpath hpunishment time)
    (fun liveTime hlive ih ↦ by
      have hdebt := debt_step path hpath liveTime hlive
      have haccount := source_add_aggregateCapacityAccount_succ_le
        path hpath hpunishment regime liveTime hlive
      have hsurvival : survival (reward := reward) path liveTime ≤ 1 :=
        quittingStationaryContinueMass_le_one _
      have haccountNext : 0 ≤
          aggregateCapacityAccount path hpath hpunishment (liveTime + 1) :=
        aggregateCapacityAccount_nonneg
          path hpath hpunishment regime (liveTime + 1)
      calc
        debt (reward := reward) path liveTime =
            source (reward := reward) path liveTime +
              survival (reward := reward) path liveTime *
                debt (reward := reward) path (liveTime + 1) := hdebt
        _ ≤ source (reward := reward) path liveTime +
              survival (reward := reward) path liveTime *
                aggregateCapacityAccount path hpath hpunishment
                  (liveTime + 1) := by
            gcongr
            exact survival_nonneg path liveTime
        _ ≤ source (reward := reward) path liveTime +
              aggregateCapacityAccount path hpath hpunishment
                (liveTime + 1) := by
            gcongr
            exact mul_le_of_le_one_left haccountNext hsurvival
        _ ≤ aggregateCapacityAccount path hpath hpunishment liveTime :=
          haccount)
    hfar htime

/-- A physical frozen-root terminal lift dominates aggregate debt by the
capacity account at every point, not only at the initial point. -/
theorem debt_le_aggregateCapacityAccount_of_frozenRootLift_at
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
    ∀ time, time ≤ cutoff →
      debt (reward := reward) path time ≤
        aggregateCapacityAccount path hpath hpunishment time := by
  apply debt_le_aggregateCapacityAccount_of_far_at
    path hpath hpunishment regime
  exact terminal_debt_le_aggregateCapacityAccount_of_frozenRootLift
    path hpath hpunishment regime root support hsupport continuation hlift
      tailRoot hpays

/-- **Tight initial capacity forces immediate zero-source entry.**  Once a
physical incoming lift has paid the positive terminal boundary, the carry
comparison holds at every date.  If the initial capacity account is no
larger than exact initial debt, the two are equal.  Exact debt recursion and
the stronger additive capacity recursion then force aggregate debt source
zero at date zero, or (when the next debt itself is zero) at date one.

This is the sharp extra comparison needed to turn boundary funding into a
literal exposed-face edge.  The landed minimizer APIs provide the opposite
inequality but do not currently prove this reverse inequality. -/
theorem source_zero_or_succ_zero_of_frozenRootLift_and_initial_tight
    (regime : QuittingCounterexampleRegime reward)
    (hcutoff : 0 < cutoff)
    (hterminal : 0 < debt (reward := reward) path cutoff)
    (root : ι → PMF Bool) (support : Finset ι)
    (hsupport : IsQuittingRootInteriorOnSupport root support)
    (continuation : Payoff ι)
    (hlift : IsQuittingFrozenRootContinuationLift reward 0
      (quittingPunishmentValue reward) (quittingRewardBound reward)
      root support continuation)
    (tailRoot : QuittingRootSimplex ι)
    (hpays : debt (reward := reward) path cutoff ≤
      (Fintype.card ι : ℝ) * quittingRewardBound reward *
        quittingRootAbsorptionMass root)
    (htight : aggregateCapacityAccount path hpath hpunishment 0 ≤
      debt (reward := reward) path 0) :
    source (reward := reward) path 0 = 0 ∨
      (1 < cutoff ∧ source (reward := reward) path 1 = 0) := by
  have hdom := debt_le_aggregateCapacityAccount_of_frozenRootLift_at
    path hpath hpunishment regime root support hsupport continuation hlift
      tailRoot hpays
  have hdom0 := hdom 0 (Nat.zero_le cutoff)
  have heq0 : debt (reward := reward) path 0 =
      aggregateCapacityAccount path hpath hpunishment 0 :=
    le_antisymm hdom0 htight
  have hdom1 := hdom 1 hcutoff
  have hdebt0 := debt_step path hpath 0 hcutoff
  have haccount0 := source_add_aggregateCapacityAccount_succ_le
    path hpath hpunishment regime 0 hcutoff
  have hcarry : aggregateCapacityAccount path hpath hpunishment 1 ≤
      survival (reward := reward) path 0 *
        debt (reward := reward) path 1 := by
    rw [← heq0] at haccount0
    norm_num at hdebt0 haccount0
    linarith
  have hkilled : debt (reward := reward) path 1 ≤
      survival (reward := reward) path 0 *
        debt (reward := reward) path 1 := hdom1.trans hcarry
  by_cases hnextDebt : debt (reward := reward) path 1 = 0
  · right
    have hcutoffOne : 1 < cutoff := by
      by_contra hnot
      have : cutoff = 1 := by omega
      subst cutoff
      linarith
    refine ⟨hcutoffOne, ?_⟩
    have hdebt1 := debt_step path hpath 1 hcutoffOne
    have hsource1 := source_nonneg path hpath 1
    have hcarry1 : 0 ≤ survival (reward := reward) path 1 *
        debt (reward := reward) path (1 + 1) :=
      mul_nonneg (survival_nonneg path 1) (debt_nonneg path hpath (1 + 1))
    rw [hnextDebt] at hdebt1
    linarith
  · left
    have hnextDebtPos : 0 < debt (reward := reward) path 1 :=
      lt_of_le_of_ne (debt_nonneg path hpath 1) (Ne.symm hnextDebt)
    have hsurvivalLe : survival (reward := reward) path 0 ≤ 1 :=
      quittingStationaryContinueMass_le_one _
    have hsurvivalEq : survival (reward := reward) path 0 = 1 := by
      nlinarith
    have hcharge : charge (reward := reward) path 0 = 0 := by
      unfold charge quittingRootAbsorptionMass
      change 1 - survival (reward := reward) path 0 = 0
      linarith
    have hsourceLe := source_le_card_mul_rewardBound_mul_charge
      path hpath 0
    rw [hcharge, mul_zero] at hsourceLe
    exact le_antisymm hsourceLe (source_nonneg path hpath 0)

include hpath hpunishment in
/-- Vanishing aggregate source puts the corresponding finite exact edge in
every playerwise debt-source exposed face.  A counterexample seam witness is
used only to certify that zero is the attained supporting value of the
compact carrier. -/
theorem all_debtSourceZeroFaces_of_source_eq_zero
    {regime : QuittingCounterexampleRegime reward}
    (seam : QuittingCounterexampleSeamWitness regime)
    (time : ℕ) (htime : time < cutoff)
    (hsource : source (reward := reward) path time = 0) :
    ∀ selected,
      quittingDebtSourceObstructionFlow
          (quittingFiniteNashBellmanPathDynamicDebtPoint
              reward cutoff path time,
            quittingFiniteNashBellmanPathDynamicDebtPoint
              reward cutoff path (time + 1)) ∈
        exposedFace (quittingDebtSourceZeroFaceCostate selected)
          (quittingDebtSourceOneStageObstructionCarrier reward) := by
  let edge : QuittingDebtPoint ι × QuittingDebtPoint ι :=
    (quittingFiniteNashBellmanPathDynamicDebtPoint
        reward cutoff path time,
      quittingFiniteNashBellmanPathDynamicDebtPoint
        reward cutoff path (time + 1))
  have hedge : edge ∈ quittingFloorDynamicDebtEdgeGraph reward := by
    constructor
    · exact ⟨quittingFiniteNashBellmanPathDynamicDebtPoint_mem_box
          reward cutoff path hpath time,
        quittingFiniteNashBellmanPathDynamicDebtPoint_mem_box
          reward cutoff path hpath (time + 1),
        quittingFiniteNashBellmanPathDynamicDebtPoint_edge
          reward cutoff path hpath time htime⟩
    · intro who
      exact ⟨quittingPunishmentValue_le_finiteDynamicDebtPoint_of_nonpos
          path hpath hpunishment time who,
        quittingPunishmentValue_le_finiteDynamicDebtPoint_of_nonpos
          path hpath hpunishment (time + 1) who⟩
  have hflow : quittingDebtSourceObstructionFlow edge ∈
      quittingDebtSourceOneStageObstructionCarrier reward :=
    ⟨edge, hedge, rfl⟩
  intro selected
  apply (seam.mem_exposedFace_quittingDebtSourceZeroFaceCostate_iff
    selected (quittingDebtSourceObstructionFlow edge)).2
  refine ⟨hflow, ?_⟩
  rw [quittingDebtSourceObstructionFlow_source]
  have hcoordinateNonneg : 0 ≤ quittingDynamicDebtSeam edge.1 selected :=
    quittingDynamicDebtSeam_nonneg edge.1 hedge.1.1 selected
  have hcoordinateLe : quittingDynamicDebtSeam edge.1 selected ≤
      source (reward := reward) path time := by
    unfold source
    exact Finset.single_le_sum
      (fun who _ ↦ quittingDynamicDebtSeam_nonneg edge.1 hedge.1.1 who)
      (Finset.mem_univ selected)
  rw [hsource] at hcoordinateLe
  exact le_antisymm hcoordinateLe hcoordinateNonneg

/-- Tight initial capacity upgrades a physical terminal lift to a literal
all-player zero-source exposed face at the first or second finite edge. -/
theorem all_debtSourceZeroFaces_zero_or_one_of_frozenRootLift_and_initial_tight
    {regime : QuittingCounterexampleRegime reward}
    (seam : QuittingCounterexampleSeamWitness regime)
    (hcutoff : 0 < cutoff)
    (hterminal : 0 < debt (reward := reward) path cutoff)
    (root : ι → PMF Bool) (support : Finset ι)
    (hsupport : IsQuittingRootInteriorOnSupport root support)
    (continuation : Payoff ι)
    (hlift : IsQuittingFrozenRootContinuationLift reward 0
      (quittingPunishmentValue reward) (quittingRewardBound reward)
      root support continuation)
    (tailRoot : QuittingRootSimplex ι)
    (hpays : debt (reward := reward) path cutoff ≤
      (Fintype.card ι : ℝ) * quittingRewardBound reward *
        quittingRootAbsorptionMass root)
    (htight : aggregateCapacityAccount path hpath hpunishment 0 ≤
      debt (reward := reward) path 0) :
    (∀ selected,
      quittingDebtSourceObstructionFlow
          (quittingFiniteNashBellmanPathDynamicDebtPoint
              reward cutoff path 0,
            quittingFiniteNashBellmanPathDynamicDebtPoint
              reward cutoff path 1) ∈
        exposedFace (quittingDebtSourceZeroFaceCostate selected)
          (quittingDebtSourceOneStageObstructionCarrier reward)) ∨
      (1 < cutoff ∧ ∀ selected,
        quittingDebtSourceObstructionFlow
            (quittingFiniteNashBellmanPathDynamicDebtPoint
                reward cutoff path 1,
              quittingFiniteNashBellmanPathDynamicDebtPoint
                reward cutoff path 2) ∈
          exposedFace (quittingDebtSourceZeroFaceCostate selected)
            (quittingDebtSourceOneStageObstructionCarrier reward)) := by
  rcases source_zero_or_succ_zero_of_frozenRootLift_and_initial_tight
      path hpath hpunishment regime hcutoff hterminal root support hsupport
        continuation hlift tailRoot hpays htight with hzero | ⟨hcutoff1, hzero⟩
  · exact Or.inl
      (all_debtSourceZeroFaces_of_source_eq_zero
        path hpath hpunishment seam 0 hcutoff hzero)
  · exact Or.inr ⟨hcutoff1,
      all_debtSourceZeroFaces_of_source_eq_zero
        path hpath hpunishment seam 1 hcutoff1 hzero⟩

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

/-! ## Counterexample-regime exhaustion of the strict terminal branch -/

namespace QuittingAggregateCalibratedTerminalAnchor

/-- Enriched exact debt-source flow of one displayed finite anchor edge. -/
def debtSourceFlow
    (anchor : QuittingAggregateCalibratedTerminalAnchor reward)
    (time : ℕ) :
    RawGradedFlow QuittingObstructionGrade
      (QuittingDebtSourceObstructionCoordinate ι) :=
  quittingDebtSourceObstructionFlow
    (quittingFiniteNashBellmanPathDynamicDebtPoint
        reward (anchor.last + 1) anchor.path time,
      quittingFiniteNashBellmanPathDynamicDebtPoint
        reward (anchor.last + 1) anchor.path (time + 1))

/-- One finite anchor edge lies simultaneously in every playerwise
debt-source zero face of the exact counterexample carrier. -/
def IsAllDebtSourceZeroFace
    (anchor : QuittingAggregateCalibratedTerminalAnchor reward)
    (time : ℕ) : Prop :=
  ∀ selected, anchor.debtSourceFlow time ∈
    exposedFace (quittingDebtSourceZeroFaceCostate selected)
      (quittingDebtSourceOneStageObstructionCarrier reward)

/-- Every calibrated positive-debt anchor has strictly positive aggregate
terminal cap.  Its marked positive initial debt is already bounded by the
same player's singleton cap. -/
theorem terminalAggregateDebt_pos
    (anchor : QuittingAggregateCalibratedTerminalAnchor reward) :
    0 < ∑ who, quittingPositiveSingletonDebtCap reward who := by
  have hownerCap :
      quittingFiniteNashBellmanPathDynamicDebt
          reward (anchor.last + 1) anchor.path anchor.owner 0 ≤
        quittingPositiveSingletonDebtCap reward anchor.owner :=
    quittingFiniteNashBellmanPathDynamicDebt_le_cap
      reward (anchor.last + 1) anchor.path anchor.path_mem anchor.owner 0
        (by omega)
  have hcapPos : 0 < quittingPositiveSingletonDebtCap reward anchor.owner :=
    anchor.ownerDebt_pos.trans_le hownerCap
  exact hcapPos.trans_le
    (Finset.single_le_sum
      (fun who _ ↦ le_max_left 0 (reward (quittingSingletonTerminal who) who))
      (Finset.mem_univ anchor.owner))

/-- In a counterexample regime the terminal aggregate debt is automatically
strictly below the `card * rewardBound` funding scale.  The important sharp
estimate is `terminal debt ≤ rewardBound`; the regime supplies at least four
players, so the previously exposed saturated branch cannot occur. -/
theorem terminalAggregateDebt_lt_card_mul_rewardBound
    (regime : QuittingCounterexampleRegime reward)
    (anchor : QuittingAggregateCalibratedTerminalAnchor reward) :
    (∑ who, quittingPositiveSingletonDebtCap reward who) <
      (Fintype.card ι : ℝ) * quittingRewardBound reward := by
  have hdebtPos := anchor.terminalAggregateDebt_pos
  have hdebtLe : (∑ who, quittingPositiveSingletonDebtCap reward who) ≤
      quittingRewardBound reward :=
    sum_positiveSingletonDebtCap_le_quittingRewardBound
      (reward := reward)
  have hboundPos : 0 < quittingRewardBound reward :=
    hdebtPos.trans_le hdebtLe
  have hcard : (3 : ℝ) < Fintype.card ι := by
    exact_mod_cast regime.three_lt_card
  nlinarith

/-- **Counterexample-regime terminal boundary alternative.**  For every
calibrated positive-debt anchor in the nonpositive-floor lane, the canonical
one-owner strict funding root is available automatically.  Hence the finite
boundary is genuinely exhausted by a floor-admissible incoming edge and the
carry comparison, unless explicit finite Farkas multipliers reject that
specific game-facing continuation system.

There is no saturated residual in a counterexample regime: the sum-form
reward bound and `card ≥ 4` force strictness. -/
theorem boundaryCarry_fundingEdge_or_farkas
    (regime : QuittingCounterexampleRegime reward)
    (anchor : QuittingAggregateCalibratedTerminalAnchor reward)
    (hpunishment : ∀ who, quittingPunishmentValue reward who ≤ 0) :
    (QuittingFiniteDynamicDebtAdmissibleChronology.debt
          (reward := reward) anchor.path 0 ≤
        QuittingFiniteDynamicDebtAdmissibleChronology.aggregateCapacityAccount
          anchor.path anchor.path_mem hpunishment 0 ∧
      ∃ root : ι → PMF Bool, ∃ support : Finset ι, ∃ continuation,
        IsQuittingRootInteriorOnSupport root support ∧
        (Fintype.card ι : ℝ) * quittingRewardBound reward *
            quittingRootAbsorptionMass root =
          QuittingFiniteDynamicDebtAdmissibleChronology.debt
            (reward := reward) anchor.path (anchor.last + 1) ∧
        IsQuittingFrozenRootContinuationLift reward 0
          (quittingPunishmentValue reward) (quittingRewardBound reward)
          root support continuation ∧
        IsQuittingNashBellmanEdge reward
          (0, quittingFrozenRootLiftSimplex root)
          (continuation, quittingAllContinueSimplexRoot)) ∨
      ∃ root : ι → PMF Bool, ∃ support : Finset ι,
        IsQuittingRootInteriorOnSupport root support ∧
        (Fintype.card ι : ℝ) * quittingRewardBound reward *
            quittingRootAbsorptionMass root =
          QuittingFiniteDynamicDebtAdmissibleChronology.debt
            (reward := reward) anchor.path (anchor.last + 1) ∧
        HasQuittingFrozenRootLiftFarkasCertificate (reward := reward) 0
          (quittingPunishmentValue reward) (quittingRewardBound reward)
          root support := by
  apply QuittingFiniteDynamicDebtAdmissibleChronology.strict_terminalDebt_fundingEdge_or_farkas
    anchor.path anchor.path_mem hpunishment regime anchor.owner
      quittingAllContinueSimplexRoot
  · rw [QuittingFiniteDynamicDebtAdmissibleChronology.debt_cutoff_eq_sum_positiveSingletonDebtCap]
    exact anchor.terminalAggregateDebt_pos
  · rw [QuittingFiniteDynamicDebtAdmissibleChronology.debt_cutoff_eq_sum_positiveSingletonDebtCap]
    exact anchor.terminalAggregateDebt_lt_card_mul_rewardBound regime

/-- **Unconditional finite boundary-exhaustion trichotomy.**  In the
counterexample-regime nonpositive-floor lane, every calibrated anchor has
one of three game-facing outcomes:

* the first or second exact finite edge lies in every debt-source zero face;
* the initial admissible capacity account has strict positive slack over
  exact aggregate debt;
* explicit finite Farkas multipliers reject the canonical strictly mixed
  terminal-funding root.

Thus persistent positive debt source is priced by a literal, strictly
positive initial capacity slack.  Eliminating that slack requires the still
missing reverse objective comparison; terminal boundary domination alone
cannot do it. -/
theorem zeroFace_zero_or_one_or_initialCapacitySlack_or_farkas
    (regime : QuittingCounterexampleRegime reward)
    (seam : QuittingCounterexampleSeamWitness regime)
    (anchor : QuittingAggregateCalibratedTerminalAnchor reward)
    (hpunishment : ∀ who, quittingPunishmentValue reward who ≤ 0) :
    anchor.IsAllDebtSourceZeroFace 0 ∨
      (1 < anchor.last + 1 ∧ anchor.IsAllDebtSourceZeroFace 1) ∨
      QuittingFiniteDynamicDebtAdmissibleChronology.debt
          (reward := reward) anchor.path 0 <
        QuittingFiniteDynamicDebtAdmissibleChronology.aggregateCapacityAccount
          anchor.path anchor.path_mem hpunishment 0 ∨
      ∃ root : ι → PMF Bool, ∃ support : Finset ι,
        IsQuittingRootInteriorOnSupport root support ∧
        (Fintype.card ι : ℝ) * quittingRewardBound reward *
            quittingRootAbsorptionMass root =
          QuittingFiniteDynamicDebtAdmissibleChronology.debt
            (reward := reward) anchor.path (anchor.last + 1) ∧
        HasQuittingFrozenRootLiftFarkasCertificate (reward := reward) 0
          (quittingPunishmentValue reward) (quittingRewardBound reward)
          root support := by
  rcases anchor.boundaryCarry_fundingEdge_or_farkas regime hpunishment with
    ⟨hcarry, root, support, continuation, hsupport, hfunds, hlift, _hedge⟩ |
      ⟨root, support, hsupport, hfunds, hfarkas⟩
  · by_cases htight :
      QuittingFiniteDynamicDebtAdmissibleChronology.aggregateCapacityAccount
          anchor.path anchor.path_mem hpunishment 0 ≤
        QuittingFiniteDynamicDebtAdmissibleChronology.debt
          (reward := reward) anchor.path 0
    · have hterminal : 0 <
          QuittingFiniteDynamicDebtAdmissibleChronology.debt
            (reward := reward) anchor.path (anchor.last + 1) := by
        rw [debt_cutoff_eq_sum_positiveSingletonDebtCap]
        exact anchor.terminalAggregateDebt_pos
      have hpays :
          QuittingFiniteDynamicDebtAdmissibleChronology.debt
              (reward := reward) anchor.path (anchor.last + 1) ≤
            (Fintype.card ι : ℝ) * quittingRewardBound reward *
              quittingRootAbsorptionMass root := by
        rw [hfunds]
      rcases
          all_debtSourceZeroFaces_zero_or_one_of_frozenRootLift_and_initial_tight
            anchor.path anchor.path_mem hpunishment seam (by omega) hterminal
              root support hsupport continuation hlift
                quittingAllContinueSimplexRoot hpays htight with hzero | hnext
      · exact Or.inl (by
          simpa [IsAllDebtSourceZeroFace, debtSourceFlow] using hzero)
      · exact Or.inr (Or.inl ⟨hnext.1, by
          simpa [IsAllDebtSourceZeroFace, debtSourceFlow] using hnext.2⟩)
    · exact Or.inr (Or.inr (Or.inl (lt_of_not_ge htight)))
  · exact Or.inr (Or.inr (Or.inr
      ⟨root, support, hsupport, hfunds, hfarkas⟩))

end QuittingAggregateCalibratedTerminalAnchor

/-! ## Sharp scalar regression for the remaining initial slack -/

/-- Terminal domination plus exact killed debt recursion and the stronger
additive capacity recursion do not force a zero source.  This one-edge
finite regression has a tightly funded terminal boundary, but positive
initial capacity slack absorbs a strictly positive source.  It targets the
precise scalar implication used above; it is not asserted to instantiate a
quitting counterexample regime. -/
theorem fundedTerminalBoundary_does_not_force_zeroSource_regression :
    let survival : ℝ := 1 / 2
    let source : ℝ := 1
    let terminalDebt : ℝ := 1
    let initialDebt : ℝ := 3 / 2
    let terminalAccount : ℝ := 1
    let initialAccount : ℝ := 2
    0 ≤ survival ∧ survival ≤ 1 ∧
      initialDebt = source + survival * terminalDebt ∧
      initialAccount = source + terminalAccount ∧
      terminalDebt ≤ terminalAccount ∧
      initialDebt < initialAccount ∧ 0 < source := by
  norm_num

end GameTheory
