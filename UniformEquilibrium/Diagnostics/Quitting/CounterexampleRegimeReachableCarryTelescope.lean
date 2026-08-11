/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeAggregatePrefixConsumption
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTailBridge
import UniformEquilibrium.Quitting.Bellman.Finite.PunishmentFloorAdmissibleChargedRelation
import Math.Probability.KilledTailPotential

/-!
# Reachable-prefix capacity telescope for carried dynamic debt

A chronological sequence of literally attached punishment-floor reachable
prepends runs opposite the charged relation: its current predecessor is
followed by the edge's tail.  The canonical reachable potential therefore
increases along chronological time.  Subtracting it from the regime's prefix
charge bound produces a nonnegative remaining capacity that decreases by at
least the edge's joint absorption charge.

When the same sequence carries coherent exact dynamic-debt annotations, the
aggregate diagonal seam is at most `card * rewardBound` times that charge.
Scaling remaining capacity by this constant gives an excessive killed
account for aggregate debt.  Finite telescoping consumes every seam, but it
retains one survival-weighted far-end debt boundary.  The final theorem makes
domination of that boundary the exact remaining premise; reachability and
capacity alone do not provide it.
-/

noncomputable section

namespace GameTheory

open Math.ChargedPathBudget Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {regime : QuittingCounterexampleRegime reward}

/-! ## The literal-reachability constructor gate -/

/-- Floor domination propagates along every boxed exact-predecessor path.
This is the state-level necessary condition hidden by the existential
reachable subtype. -/
private theorem quittingPunishmentFloor_le_boxPathTarget
    {source target : QuittingPunishmentFloorBoxState reward}
    (hsource : ∀ who, quittingPunishmentValue reward who ≤ source.1.1 who) :
    (quittingPunishmentFloorBoxChargedRelation reward).Path source target →
      ∀ who, quittingPunishmentValue reward who ≤ target.1.1 who
  | .nil _ => hsource
  | .cons edge rest =>
      quittingPunishmentFloor_le_boxPathTarget
        ((QuittingPunishmentFloorAdmissibleEdge.ofExactEdge
          ⟨edge.tail, hsource⟩ edge.current edge.exactEdge).current.2)
        rest

/-- Every literally punishment-floor reachable boxed state dominates the
punishment floor coordinatewise.  Therefore a calibrated zero-boundary
minimizer can enter the reachable chronology only after this additional
endpoint inequality has been proved. -/
theorem quittingPunishmentFloor_le_reachableState
    (state : QuittingPunishmentFloorReachableState reward) (who : ι) :
    quittingPunishmentValue reward who ≤ state.1.1.1 who := by
  rcases state.2 with ⟨path⟩
  exact quittingPunishmentFloor_le_boxPathTarget
    (fun _ ↦ le_rfl) path who

/-- A boxed state violating the punishment floor cannot be identified with
any literally reachable state.  This isolates the first constructor
obstruction independently of dynamic-debt annotations. -/
theorem not_exists_reachableState_eq_of_lt_punishmentFloor
    (state : QuittingPunishmentFloorBoxState reward) (who : ι)
    (hbelow : state.1.1 who < quittingPunishmentValue reward who) :
    ¬ ∃ reachable : QuittingPunishmentFloorReachableState reward,
        reachable.1 = state := by
  rintro ⟨reachable, rfl⟩
  exact (not_le_of_gt hbelow)
    (quittingPunishmentFloor_le_reachableState reachable who)

/-- In particular, literal reachability of an aggregate-calibrated
zero-boundary minimizer's initial point forces an inequality not present in
the minimizer or calibration APIs. -/
theorem aggregateCalibratedAnchor_initial_punishmentFloor_le_of_reachable
    (anchor : QuittingAggregateCalibratedTerminalAnchor reward)
    (hreachable : IsQuittingPunishmentFloorReachable reward
      ⟨anchor.path 0, anchor.path_mem.1 0⟩)
    (who : ι) :
    quittingPunishmentValue reward who ≤ (anchor.path 0).1 who := by
  exact quittingPunishmentFloor_le_reachableState
    ⟨⟨anchor.path 0, anchor.path_mem.1 0⟩, hreachable⟩ who

/-- A floor violation at the selected aggregate minimizer's initial point is
an exact obstruction to using that point as a literal reachable endpoint.
Objective minimality and the calibrated prepend inequality do not rule out
this obstruction. -/
theorem aggregateCalibratedAnchor_initial_not_reachable_of_lt_punishmentFloor
    (anchor : QuittingAggregateCalibratedTerminalAnchor reward) (who : ι)
    (hbelow : (anchor.path 0).1 who < quittingPunishmentValue reward who) :
    ¬ IsQuittingPunishmentFloorReachable reward
      ⟨anchor.path 0, anchor.path_mem.1 0⟩ := by
  intro hreachable
  exact (not_le_of_gt hbelow)
    (aggregateCalibratedAnchor_initial_punishmentFloor_le_of_reachable
      anchor hreachable who)

/-! ## Nonpositive floors and intrinsic finite-chain attachment -/

variable {cutoff : ℕ}

/-- Every exact-D annotation of a zero-boundary chain dominates a
coordinatewise nonpositive punishment floor.  This applies to the aggregate
minimizer as well as to arbitrary admissible zero-boundary chains. -/
theorem quittingPunishmentValue_le_finiteDynamicDebtPoint_of_nonpos
    (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff)
    (hpunishment : ∀ who, quittingPunishmentValue reward who ≤ 0)
    (time : ℕ) (who : ι) :
    quittingPunishmentValue reward who ≤
      (quittingFiniteNashBellmanPathDynamicDebtPoint
        reward cutoff path time).1.1 who := by
  let tail := fun point ↦
    quittingFiniteNashBellmanPathDynamicDebtPoint reward cutoff path point
  have hterminal : (tail cutoff).1.1 = 0 := by
    simp only [tail, quittingFiniteNashBellmanPathDynamicDebtPoint,
      dif_pos le_rfl]
    have hindex :
        (⟨cutoff, Nat.lt_succ_self cutoff⟩ : Fin (cutoff + 1)) =
          Fin.last cutoff := by
      apply Fin.ext
      rfl
    rw [hindex]
    exact hpath.2.1
  by_cases htime : time ≤ cutoff
  · apply quittingPunishmentValue_le_dynamicDebtTailValue_of_endpoint_floor
      (reward := reward) tail cutoff
      (fun point _ ↦
        quittingFiniteNashBellmanPathDynamicDebtPoint_mem_box
          reward cutoff path hpath point)
      (fun point hpoint ↦
        quittingFiniteNashBellmanPathDynamicDebtPoint_edge
          reward cutoff path hpath point hpoint)
      (fun player ↦ by rw [hterminal]; exact hpunishment player)
      time htime who
  · unfold quittingFiniteNashBellmanPathDynamicDebtPoint
    rw [dif_neg htime]
    rw [congrFun hpath.2.1 who]
    exact hpunishment who

/-- Aggregate-calibrated specialization: every displayed payoff of the
selected aggregate minimizer is floor-admissible under a nonpositive
punishment vector. -/
theorem aggregateCalibratedAnchor_point_punishmentFloor_le_of_nonpos
    (anchor : QuittingAggregateCalibratedTerminalAnchor reward)
    (hpunishment : ∀ who, quittingPunishmentValue reward who ≤ 0)
    (time : ℕ) (htime : time ≤ anchor.last + 1) (who : ι) :
    quittingPunishmentValue reward who ≤ (anchor.path
      ⟨time, Nat.lt_succ_of_le htime⟩).1 who := by
  simpa [quittingFiniteNashBellmanPathDynamicDebtPoint,
    dif_pos htime] using
    (quittingPunishmentValue_le_finiteDynamicDebtPoint_of_nonpos
      anchor.path anchor.path_mem hpunishment time who)

/-- The full floor-admissible charged state carried by one displayed point
of a finite zero-boundary exact-D chain. -/
def quittingFiniteDynamicDebtAdmissibleState
    (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff)
    (hpunishment : ∀ who, quittingPunishmentValue reward who ≤ 0)
    (time : ℕ) : QuittingPunishmentFloorAdmissibleState reward :=
  ⟨⟨(quittingFiniteNashBellmanPathDynamicDebtPoint
      reward cutoff path time).1,
    (quittingFiniteNashBellmanPathDynamicDebtPoint_mem_box
      reward cutoff path hpath time).1⟩,
    quittingPunishmentValue_le_finiteDynamicDebtPoint_of_nonpos
      path hpath hpunishment time⟩

/-- Each preterminal exact-D edge is literally an edge in the global
floor-admissible charged relation. -/
def quittingFiniteDynamicDebtAdmissibleEdge
    (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff)
    (hpunishment : ∀ who, quittingPunishmentValue reward who ≤ 0)
    (time : ℕ) (htime : time < cutoff) :
    QuittingPunishmentFloorAdmissibleEdge reward where
  tail := quittingFiniteDynamicDebtAdmissibleState
    path hpath hpunishment (time + 1)
  current := quittingFiniteDynamicDebtAdmissibleState
    path hpath hpunishment time
  exactEdge :=
    (quittingFiniteNashBellmanPathDynamicDebtPoint_edge
      reward cutoff path hpath time htime).1

/-- Reversing any finite subsegment of one selected zero-boundary chain gives
a literal path in the full floor-admissible charged relation. -/
def quittingFiniteDynamicDebtAdmissibleReverseSegment
    (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff)
    (hpunishment : ∀ who, quittingPunishmentValue reward who ≤ 0) :
    (start fuel : ℕ) → start + fuel ≤ cutoff →
      (quittingPunishmentFloorAdmissibleChargedRelation reward).Path
        (quittingFiniteDynamicDebtAdmissibleState
          path hpath hpunishment (start + fuel))
        (quittingFiniteDynamicDebtAdmissibleState
          path hpath hpunishment start)
  | start, 0, _ => .nil _
  | start, fuel + 1, hend => by
      let edge := quittingFiniteDynamicDebtAdmissibleEdge
        path hpath hpunishment (start + fuel) (by omega)
      let rest := quittingFiniteDynamicDebtAdmissibleReverseSegment
        path hpath hpunishment start fuel (by omega)
      exact .cons edge rest

/-- In particular, the zero-boundary terminal state has an intrinsic
admissible path to every earlier displayed point of the same chain.  The
source is the chain's terminal zero state, not the literal punishment-floor
anchor. -/
def quittingFiniteDynamicDebtAdmissibleTerminalPathTo
    (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff)
    (hpunishment : ∀ who, quittingPunishmentValue reward who ≤ 0)
    (time : ℕ) (htime : time ≤ cutoff) :
    (quittingPunishmentFloorAdmissibleChargedRelation reward).Path
      (quittingFiniteDynamicDebtAdmissibleState
        path hpath hpunishment cutoff)
      (quittingFiniteDynamicDebtAdmissibleState
        path hpath hpunishment time) := by
  simpa [Nat.add_sub_of_le htime] using
    (quittingFiniteDynamicDebtAdmissibleReverseSegment
      path hpath hpunishment time (cutoff - time) (by omega))

/-- Reachability of the single terminal zero state propagates through the
intrinsic reversed chain to every earlier point.  Nonpositive punishment
proves floor admissibility, but does not itself supply `hterminal`; the
terminal simplex coordinate is unconstrained and need not be the literal
punishment-floor anchor. -/
theorem isQuittingPunishmentFloorReachable_finiteDynamicDebtPoint_of_terminal
    (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff)
    (hpunishment : ∀ who, quittingPunishmentValue reward who ≤ 0)
    (hterminal : IsQuittingPunishmentFloorReachable reward
      (quittingFiniteDynamicDebtAdmissibleState
        path hpath hpunishment cutoff).1)
    (time : ℕ) (htime : time ≤ cutoff) :
    IsQuittingPunishmentFloorReachable reward
      (quittingFiniteDynamicDebtAdmissibleState
        path hpath hpunishment time).1 := by
  rcases hterminal with ⟨anchorPath⟩
  let segment := quittingFiniteDynamicDebtAdmissibleTerminalPathTo
    path hpath hpunishment time htime
  let boxSegment :=
    QuittingPunishmentFloorAdmissibleChargedRelation.pathToBoxPath segment
  exact ⟨anchorPath.append boxSegment⟩

/-- Aggregate-calibrated specialization of the single-terminal bridge. -/
theorem aggregateCalibratedAnchor_point_reachable_of_terminal_reachable
    (anchor : QuittingAggregateCalibratedTerminalAnchor reward)
    (hpunishment : ∀ who, quittingPunishmentValue reward who ≤ 0)
    (hterminal : IsQuittingPunishmentFloorReachable reward
      (quittingFiniteDynamicDebtAdmissibleState
        anchor.path anchor.path_mem hpunishment (anchor.last + 1)).1)
    (time : ℕ) (htime : time ≤ anchor.last + 1) :
    IsQuittingPunishmentFloorReachable reward
      (quittingFiniteDynamicDebtAdmissibleState
        anchor.path anchor.path_mem hpunishment time).1 :=
  isQuittingPunishmentFloorReachable_finiteDynamicDebtPoint_of_terminal
    anchor.path anchor.path_mem hpunishment hterminal time htime

namespace QuittingFiniteDynamicDebtAdmissibleChronology

variable (path : QuittingFiniteNashBellmanPath ι cutoff)
variable (hpath : path ∈
  quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff)
variable (hpunishment : ∀ who, quittingPunishmentValue reward who ≤ 0)

/-- Joint survival on the intrinsic chronological reading of one finite
zero-boundary chain. -/
def survival (time : ℕ) : ℝ :=
  quittingStationaryContinueMass
    (quittingRootOfSimplex
      (quittingFiniteNashBellmanPathDynamicDebtPoint
        reward cutoff path time).1.2)

/-- Aggregate exact diagonal seam on one finite chain. -/
def source (time : ℕ) : ℝ :=
  ∑ who, quittingDynamicDebtSeam
    (quittingFiniteNashBellmanPathDynamicDebtPoint
      reward cutoff path time) who

/-- Aggregate carried exact debt on one finite chain. -/
def debt (time : ℕ) : ℝ :=
  ∑ who, (quittingFiniteNashBellmanPathDynamicDebtPoint
    reward cutoff path time).2 who

/-- Literal one-stage absorption charge on one finite chain. -/
def charge (time : ℕ) : ℝ :=
  quittingRootAbsorptionMass
    (quittingRootOfSimplex
      (quittingFiniteNashBellmanPathDynamicDebtPoint
        reward cutoff path time).1.2)

/-- Remaining global floor-admissible prefix capacity at a displayed state.
Unlike the reachable potential, this potential is defined on every state of
the intrinsic chain once the floor is nonpositive. -/
def remainingCapacity (time : ℕ) : ℝ :=
  quittingPunishmentFloorPrefixChargeBound reward -
    quittingPunishmentFloorAdmissiblePotential reward
      (quittingFiniteDynamicDebtAdmissibleState
        path hpath hpunishment time)

/-- The aggregate capacity account at the singleton-debt scale. -/
def aggregateCapacityAccount (time : ℕ) : ℝ :=
  (Fintype.card ι : ℝ) * quittingRewardBound reward *
    remainingCapacity path hpath hpunishment time

include hpath in
/-- The terminal displayed payoff is literally the zero boundary. -/
theorem terminal_payoff_eq_zero :
    (quittingFiniteNashBellmanPathDynamicDebtPoint
      reward cutoff path cutoff).1.1 = 0 := by
  simp only [quittingFiniteNashBellmanPathDynamicDebtPoint, dif_pos le_rfl]
  have hindex :
      (⟨cutoff, Nat.lt_succ_self cutoff⟩ : Fin (cutoff + 1)) =
        Fin.last cutoff := by
    apply Fin.ext
    rfl
  rw [hindex]
  exact hpath.2.1

/-- The terminal exact-D annotation is the fixed positive-singleton cap,
independently of the selected path and of its unconstrained terminal root. -/
theorem terminal_debt_eq_positiveSingletonDebtCap (who : ι) :
    (quittingFiniteNashBellmanPathDynamicDebtPoint
      reward cutoff path cutoff).2 who =
        quittingPositiveSingletonDebtCap reward who := by
  simp [quittingFiniteNashBellmanPathDynamicDebtPoint,
    quittingFiniteNashBellmanPathDynamicDebt,
    quittingFiniteDynamicDebt_zero]

/-- Exact aggregate terminal debt. -/
theorem debt_cutoff_eq_sum_positiveSingletonDebtCap :
    debt (reward := reward) path cutoff =
      ∑ who, quittingPositiveSingletonDebtCap reward who := by
  unfold debt
  apply Finset.sum_congr rfl
  intro who _
  exact terminal_debt_eq_positiveSingletonDebtCap path who

/-- The canonical global admissible potential is bounded by the regime's
least prefix-charge capacity at every admissible source. -/
theorem admissiblePotential_le_prefixChargeBound
    (regime : QuittingCounterexampleRegime reward)
    (state : QuittingPunishmentFloorAdmissibleState reward) :
    quittingPunishmentFloorAdmissiblePotential reward state ≤
      quittingPunishmentFloorPrefixChargeBound reward := by
  unfold quittingPunishmentFloorAdmissiblePotential
  apply (quittingPunishmentFloorAdmissibleChargedRelation reward).value_le
    (quittingPunishmentFloorPrefixChargeBound_nonneg reward)
  intro target segment
  rw [← QuittingPunishmentFloorAdmissibleChargedRelation.pathToFinitePrefix_charge
    segment]
  exact regime.prefixCharge_le
    (QuittingPunishmentFloorAdmissibleChargedRelation.pathToFinitePrefix segment)

/-- Remaining global admissible capacity is nonnegative. -/
theorem remainingCapacity_nonneg
    (regime : QuittingCounterexampleRegime reward) (time : ℕ) :
    0 ≤ remainingCapacity path hpath hpunishment time := by
  unfold remainingCapacity
  exact sub_nonneg.mpr
    (admissiblePotential_le_prefixChargeBound regime _)

/-- The scaled global admissible capacity account is nonnegative. -/
theorem aggregateCapacityAccount_nonneg
    (regime : QuittingCounterexampleRegime reward) (time : ℕ) :
    0 ≤ aggregateCapacityAccount path hpath hpunishment time :=
  mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (quittingRewardBound_nonneg reward))
    (remainingCapacity_nonneg path hpath hpunishment regime time)

/-- Any admissible predecessor path ending at a displayed chain state reserves
at least its own charge in the remaining global capacity of that state.  This
is the useful orientation for paying the terminal debt. -/
theorem incomingPath_charge_le_remainingCapacity
    (regime : QuittingCounterexampleRegime reward)
    {sourceState : QuittingPunishmentFloorAdmissibleState reward}
    (time : ℕ)
    (segment : (quittingPunishmentFloorAdmissibleChargedRelation reward).Path
      sourceState
      (quittingFiniteDynamicDebtAdmissibleState
        path hpath hpunishment time)) :
    segment.chargeSum ≤ remainingCapacity path hpath hpunishment time := by
  have hdrop :=
    (quittingPunishmentFloorAdmissiblePotential_isBoundedPotential
      regime.prefixCharge_le).isPotential.chargeSum_le segment
  have hsource := admissiblePotential_le_prefixChargeBound regime sourceState
  unfold remainingCapacity
  linarith

/-- The chain's intrinsic reversed path has the opposite orientation: it
spends terminal remaining capacity on the way to an earlier state.  Thus it
cannot by itself lower-bound the terminal slack required by the carry gate. -/
theorem terminal_remainingCapacity_add_intrinsicCharge_le
    (regime : QuittingCounterexampleRegime reward)
    (time : ℕ) (htime : time ≤ cutoff) :
    remainingCapacity path hpath hpunishment cutoff +
        (quittingFiniteDynamicDebtAdmissibleTerminalPathTo
          path hpath hpunishment time htime).chargeSum ≤
      remainingCapacity path hpath hpunishment time := by
  let segment := quittingFiniteDynamicDebtAdmissibleTerminalPathTo
    path hpath hpunishment time htime
  have hdrop :=
    (quittingPunishmentFloorAdmissiblePotential_isBoundedPotential
      regime.prefixCharge_le).isPotential.chargeSum_le segment
  unfold remainingCapacity
  linarith

omit hpath hpunishment in
theorem survival_nonneg (time : ℕ) :
    0 ≤ survival (reward := reward) path time :=
  quittingStationaryContinueMass_nonneg _

include hpath in
/-- The exact-D recursion holds at every preterminal time. -/
theorem debt_step (time : ℕ) (htime : time < cutoff) :
    debt (reward := reward) path time = source (reward := reward) path time +
      survival (reward := reward) path time *
        debt (reward := reward) path (time + 1) := by
  let current := quittingFiniteNashBellmanPathDynamicDebtPoint
    reward cutoff path time
  let successor := quittingFiniteNashBellmanPathDynamicDebtPoint
    reward cutoff path (time + 1)
  have hedge : IsQuittingDynamicDebtEdge reward current successor :=
    quittingFiniteNashBellmanPathDynamicDebtPoint_edge
      reward cutoff path hpath time htime
  have hcoordinate (who : ι) :=
    quittingDynamicDebt_eq_continueMass_mul_add_seam
      current successor hedge
      (quittingFiniteNashBellmanPathDynamicDebtPoint_mem_box
        reward cutoff path hpath (time + 1)).2.1 who
  unfold debt source survival
  calc
    (∑ who, current.2 who) =
        ∑ who, (quittingDynamicDebtSeam current who +
          quittingStationaryContinueMass
              (quittingRootOfSimplex current.1.2) * successor.2 who) := by
      apply Finset.sum_congr rfl
      intro who _
      linarith [hcoordinate who]
    _ = (∑ who, quittingDynamicDebtSeam current who) +
        quittingStationaryContinueMass
            (quittingRootOfSimplex current.1.2) * ∑ who, successor.2 who := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]

include hpath in
/-- Aggregate diagonal debt is paid by the uniformly scaled literal charge. -/
theorem source_le_card_mul_rewardBound_mul_charge (time : ℕ) :
    source (reward := reward) path time ≤
      (Fintype.card ι : ℝ) * quittingRewardBound reward *
        charge (reward := reward) path time := by
  let point := quittingFiniteNashBellmanPathDynamicDebtPoint
    reward cutoff path time
  have hpoint (who : ι) :
      quittingDynamicDebtSeam point who ≤
        quittingRewardBound reward * charge (reward := reward) path time := by
    have hraw := quittingDynamicDebtSeam_le_cap_mul_absorptionMass
      point (quittingFiniteNashBellmanPathDynamicDebtPoint_mem_box
        reward cutoff path hpath time) who
    have hcap : quittingPositiveSingletonDebtCap reward who ≤
        quittingRewardBound reward :=
      (le_abs_self _).trans
        (abs_quittingPositiveSingletonDebtCap_le_rewardBound reward who)
    have hcharge : 0 ≤ charge (reward := reward) path time := by
      unfold charge quittingRootAbsorptionMass
      exact sub_nonneg.mpr (quittingStationaryContinueMass_le_one _)
    exact hraw.trans (mul_le_mul_of_nonneg_right hcap hcharge)
  unfold source
  calc
    (∑ who, quittingDynamicDebtSeam point who) ≤
        ∑ _who : ι,
          quittingRewardBound reward * charge (reward := reward) path time := by
      apply Finset.sum_le_sum
      intro who _
      exact hpoint who
    _ = (Fintype.card ι : ℝ) * quittingRewardBound reward *
        charge (reward := reward) path time := by simp [mul_assoc]

/-- Remaining global admissible capacity decreases by at least the literal
charge of each intrinsic preterminal edge. -/
theorem charge_add_remainingCapacity_succ_le
    (regime : QuittingCounterexampleRegime reward)
    (time : ℕ) (htime : time < cutoff) :
    charge (reward := reward) path time +
        remainingCapacity path hpath hpunishment (time + 1) ≤
      remainingCapacity path hpath hpunishment time := by
  have hdecrement :=
    quittingPunishmentFloorAdmissiblePotential_predecessor_decrement
      regime.prefixCharge_le
      (quittingFiniteDynamicDebtAdmissibleEdge
        path hpath hpunishment time htime)
  change quittingPunishmentFloorAdmissiblePotential reward
          (quittingFiniteDynamicDebtAdmissibleState
            path hpath hpunishment time) +
        charge (reward := reward) path time ≤
      quittingPunishmentFloorAdmissiblePotential reward
        (quittingFiniteDynamicDebtAdmissibleState
          path hpath hpunishment (time + 1)) at hdecrement
  unfold remainingCapacity
  linarith [hdecrement]

/-- The global admissible capacity account is excessive along every
preterminal edge of this one finite chain. -/
theorem source_add_aggregateCapacityAccount_succ_le
    (regime : QuittingCounterexampleRegime reward)
    (time : ℕ) (htime : time < cutoff) :
    source (reward := reward) path time +
        aggregateCapacityAccount path hpath hpunishment (time + 1) ≤
      aggregateCapacityAccount path hpath hpunishment time := by
  let scale := (Fintype.card ι : ℝ) * quittingRewardBound reward
  have hscale : 0 ≤ scale :=
    mul_nonneg (Nat.cast_nonneg _) (quittingRewardBound_nonneg reward)
  have hsource := source_le_card_mul_rewardBound_mul_charge
    path hpath time
  have hremaining := charge_add_remainingCapacity_succ_le
    path hpath hpunishment regime time htime
  calc
    source (reward := reward) path time +
        aggregateCapacityAccount path hpath hpunishment (time + 1) ≤
      scale * charge (reward := reward) path time +
        aggregateCapacityAccount path hpath hpunishment (time + 1) :=
      add_le_add_left hsource _
    _ = scale * (charge (reward := reward) path time +
        remainingCapacity path hpath hpunishment (time + 1)) := by
      simp [aggregateCapacityAccount, scale]
      ring
    _ ≤ scale * remainingCapacity path hpath hpunishment time :=
      mul_le_mul_of_nonneg_left hremaining hscale
    _ = aggregateCapacityAccount path hpath hpunishment time := rfl

private theorem finiteReference_le_excessive_of_far
    (survival source debt account : ℕ → ℝ) (horizon : ℕ)
    (hsurvival : ∀ time, 0 ≤ survival time)
    (hdebt : ∀ time, time < horizon →
      debt time = source time + survival time * debt (time + 1))
    (haccount : ∀ time, time < horizon →
      source time + survival time * account (time + 1) ≤ account time) :
    ∀ (start fuel : ℕ), start + fuel ≤ horizon →
      debt (start + fuel) ≤ account (start + fuel) →
      debt start ≤ account start
  | start, 0, _, hfar => by simpa using hfar
  | start, fuel + 1, hwindow, hfar => by
      have hstart : start < horizon := by omega
      have hfar' : debt ((start + 1) + fuel) ≤
          account ((start + 1) + fuel) := by
        rw [show (start + 1) + fuel = start + (fuel + 1) by omega]
        exact hfar
      have htail : debt (start + 1) ≤ account (start + 1) :=
        finiteReference_le_excessive_of_far survival source debt account horizon
          hsurvival hdebt haccount (start + 1) fuel (by omega) hfar'
      calc
        debt start = source start + survival start * debt (start + 1) :=
          hdebt start hstart
        _ ≤ source start + survival start * account (start + 1) := by
          have hmul := mul_le_mul_of_nonneg_left htail (hsurvival start)
          linarith
        _ ≤ account start := haccount start hstart

/-- **Intrinsic finite-chain carry telescope.**  Nonpositive punishment is
enough to run the capacity/debt telescope along each selected zero-boundary
chain separately.  No equality or nesting between minimizers at different
cutoffs is used.  The same-state far-boundary domination remains explicit. -/
theorem debt_zero_le_aggregateCapacityAccount_zero_of_far
    (regime : QuittingCounterexampleRegime reward)
    (hfar : debt (reward := reward) path cutoff ≤
      aggregateCapacityAccount path hpath hpunishment cutoff) :
    debt (reward := reward) path 0 ≤
      aggregateCapacityAccount path hpath hpunishment 0 := by
  apply finiteReference_le_excessive_of_far
    (survival (reward := reward) path) (source (reward := reward) path)
    (debt (reward := reward) path)
    (aggregateCapacityAccount path hpath hpunishment) cutoff
    (survival_nonneg path)
    (debt_step path hpath)
    (fun time htime ↦ by
      have hadditive := source_add_aggregateCapacityAccount_succ_le
        path hpath hpunishment regime time htime
      have hsurvival : survival (reward := reward) path time ≤ 1 :=
        quittingStationaryContinueMass_le_one _
      have haccount_nonneg :
          0 ≤ aggregateCapacityAccount path hpath hpunishment (time + 1) :=
        aggregateCapacityAccount_nonneg
          path hpath hpunishment regime (time + 1)
      calc
        source (reward := reward) path time +
            survival (reward := reward) path time *
            aggregateCapacityAccount path hpath hpunishment (time + 1) ≤
          source (reward := reward) path time +
            aggregateCapacityAccount path hpath hpunishment (time + 1) := by
          have hmul := mul_le_of_le_one_left haccount_nonneg hsurvival
          linarith
        _ ≤ aggregateCapacityAccount path hpath hpunishment time := hadditive)
    0 cutoff (by omega)
  simpa using hfar

/-- The strict zero-singleton-cap subclass closes the terminal gate
automatically.  This is exactly the previously solved zero-solo class; the
weaker hypothesis `punishmentValue ≤ 0` does not imply these cap equalities. -/
theorem debt_zero_le_aggregateCapacityAccount_zero_of_terminalCap_eq_zero
    (regime : QuittingCounterexampleRegime reward)
    (hterminalCap : ∀ who,
      quittingPositiveSingletonDebtCap reward who = 0) :
    debt (reward := reward) path 0 ≤
      aggregateCapacityAccount path hpath hpunishment 0 := by
  apply debt_zero_le_aggregateCapacityAccount_zero_of_far
    path hpath hpunishment regime
  rw [debt_cutoff_eq_sum_positiveSingletonDebtCap path]
  have hsum : (∑ who, quittingPositiveSingletonDebtCap reward who) = 0 := by
    apply Finset.sum_eq_zero
    intro who _
    exact hterminalCap who
  rw [hsum]
  exact aggregateCapacityAccount_nonneg
    path hpath hpunishment regime cutoff

/-- A quantitative incoming predecessor path is sufficient to pay the
terminal cap and hence close the intrinsic carry telescope.  This is the
sharp constructive orientation: paths leaving the zero boundary spend
capacity, whereas a path ending there reserves its charge in the terminal
remaining-capacity slack. -/
theorem debt_zero_le_aggregateCapacityAccount_zero_of_incomingPath
    (regime : QuittingCounterexampleRegime reward)
    {sourceState : QuittingPunishmentFloorAdmissibleState reward}
    (segment : (quittingPunishmentFloorAdmissibleChargedRelation reward).Path
      sourceState
      (quittingFiniteDynamicDebtAdmissibleState
        path hpath hpunishment cutoff))
    (hpays : debt (reward := reward) path cutoff ≤
      (Fintype.card ι : ℝ) * quittingRewardBound reward *
        segment.chargeSum) :
    debt (reward := reward) path 0 ≤
      aggregateCapacityAccount path hpath hpunishment 0 := by
  have hreserved := incomingPath_charge_le_remainingCapacity
    path hpath hpunishment regime cutoff segment
  have hscale : 0 ≤
      (Fintype.card ι : ℝ) * quittingRewardBound reward :=
    mul_nonneg (Nat.cast_nonneg _) (quittingRewardBound_nonneg reward)
  apply debt_zero_le_aggregateCapacityAccount_zero_of_far
    path hpath hpunishment regime
  calc
    debt (reward := reward) path cutoff ≤
        (Fintype.card ι : ℝ) * quittingRewardBound reward *
          segment.chargeSum := hpays
    _ ≤ (Fintype.card ι : ℝ) * quittingRewardBound reward *
        remainingCapacity path hpath hpunishment cutoff :=
      mul_le_mul_of_nonneg_left hreserved hscale
    _ = aggregateCapacityAccount path hpath hpunishment cutoff := rfl

end QuittingFiniteDynamicDebtAdmissibleChronology

open QuittingFiniteDynamicDebtAdmissibleChronology

/-- Aggregate-calibrated specialization of the intrinsic finite-chain carry
telescope.  Each cutoff is handled on its own selected minimizer, so no
cross-cutoff nesting is needed.  The terminal exact-D cap must still be paid
by the global admissible remaining-capacity account at that same terminal
state. -/
theorem aggregateCalibratedAnchor_initialDebt_le_admissibleCapacity_of_far
    (regime : QuittingCounterexampleRegime reward)
    (anchor : QuittingAggregateCalibratedTerminalAnchor reward)
    (hpunishment : ∀ who, quittingPunishmentValue reward who ≤ 0)
    (hfar :
      QuittingFiniteDynamicDebtAdmissibleChronology.debt
          (reward := reward) anchor.path (anchor.last + 1) ≤
        QuittingFiniteDynamicDebtAdmissibleChronology.aggregateCapacityAccount
          anchor.path anchor.path_mem hpunishment (anchor.last + 1)) :
    QuittingFiniteDynamicDebtAdmissibleChronology.debt
        (reward := reward) anchor.path 0 ≤
      QuittingFiniteDynamicDebtAdmissibleChronology.aggregateCapacityAccount
        anchor.path anchor.path_mem hpunishment 0 :=
  QuittingFiniteDynamicDebtAdmissibleChronology.debt_zero_le_aggregateCapacityAccount_zero_of_far
      anchor.path anchor.path_mem hpunishment regime hfar

/-- Aggregate-calibrated zero-cap specialization. -/
theorem aggregateCalibratedAnchor_initialDebt_le_admissibleCapacity_of_terminalCap_eq_zero
    (regime : QuittingCounterexampleRegime reward)
    (anchor : QuittingAggregateCalibratedTerminalAnchor reward)
    (hpunishment : ∀ who, quittingPunishmentValue reward who ≤ 0)
    (hterminalCap : ∀ who,
      quittingPositiveSingletonDebtCap reward who = 0) :
    QuittingFiniteDynamicDebtAdmissibleChronology.debt
        (reward := reward) anchor.path 0 ≤
      QuittingFiniteDynamicDebtAdmissibleChronology.aggregateCapacityAccount
        anchor.path anchor.path_mem hpunishment 0 :=
  debt_zero_le_aggregateCapacityAccount_zero_of_terminalCap_eq_zero
      anchor.path anchor.path_mem hpunishment regime hterminalCap

/-- Aggregate-calibrated incoming-path consumer. -/
theorem aggregateCalibratedAnchor_initialDebt_le_admissibleCapacity_of_incomingPath
    (regime : QuittingCounterexampleRegime reward)
    (anchor : QuittingAggregateCalibratedTerminalAnchor reward)
    (hpunishment : ∀ who, quittingPunishmentValue reward who ≤ 0)
    {sourceState : QuittingPunishmentFloorAdmissibleState reward}
    (segment : (quittingPunishmentFloorAdmissibleChargedRelation reward).Path
      sourceState
      (quittingFiniteDynamicDebtAdmissibleState anchor.path anchor.path_mem
        hpunishment (anchor.last + 1)))
    (hpays :
      QuittingFiniteDynamicDebtAdmissibleChronology.debt
          (reward := reward) anchor.path (anchor.last + 1) ≤
        (Fintype.card ι : ℝ) * quittingRewardBound reward *
          segment.chargeSum) :
    QuittingFiniteDynamicDebtAdmissibleChronology.debt
        (reward := reward) anchor.path 0 ≤
      QuittingFiniteDynamicDebtAdmissibleChronology.aggregateCapacityAccount
        anchor.path anchor.path_mem hpunishment 0 :=
  debt_zero_le_aggregateCapacityAccount_zero_of_incomingPath
      anchor.path anchor.path_mem hpunishment regime segment hpays

/-- A chronological reachable predecessor sequence equipped with literal
exact dynamic-debt states over exactly the same Nash--Bellman points. -/
structure QuittingReachableDynamicDebtChronology
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  state : ℕ → QuittingPunishmentFloorReachableState reward
  edge : ℕ → QuittingPunishmentFloorReachableEdge reward
  edge_current : ∀ time, (edge time).current = state time
  edge_tail : ∀ time, (edge time).tail = state (time + 1)
  debtState : ℕ → QuittingDebtPoint ι
  debtPoint : ∀ time, (debtState time).1 = (state time).1.1
  debt_mem : ∀ time, debtState time ∈ quittingDebtBox reward
  debt_edge : ∀ time,
    IsQuittingDynamicDebtEdge reward (debtState time) (debtState (time + 1))

namespace QuittingReachableDynamicDebtChronology

variable (chain : QuittingReachableDynamicDebtChronology reward)

/-- Joint survival coefficient at one chronological debt edge. -/
def survival (time : ℕ) : ℝ :=
  quittingStationaryContinueMass
    (quittingRootOfSimplex (chain.debtState time).1.2)

/-- Aggregate diagonal debt seam at one chronological edge. -/
def source (time : ℕ) : ℝ :=
  ∑ who, quittingDynamicDebtSeam (chain.debtState time) who

/-- Aggregate exact dynamic debt carried by one chronological state. -/
def debt (time : ℕ) : ℝ :=
  ∑ who, (chain.debtState time).2 who

/-- Literal joint absorption charge of the corresponding reachable edge. -/
def charge (time : ℕ) : ℝ :=
  (chain.edge time).toBoxEdge.absorptionCharge

/-- Canonical reachable budget still available after the chronological
state. -/
def remainingCapacity (time : ℕ) : ℝ :=
  quittingPunishmentFloorPrefixChargeBound reward -
    quittingPunishmentFloorReachablePotential reward (chain.state time)

/-- Aggregate capacity account at the uniform singleton-debt scale. -/
def aggregateCapacityAccount (time : ℕ) : ℝ :=
  (Fintype.card ι : ℝ) * quittingRewardBound reward *
    chain.remainingCapacity time

private theorem anchoredChargeBound
    (regime : QuittingCounterexampleRegime reward) :
    HasQuittingPunishmentFloorAnchoredChargeBound reward
      (quittingPunishmentFloorPrefixChargeBound reward) :=
  QuittingCounterexampleRegime.hasAnchoredChargeBound regime

include regime

theorem remainingCapacity_nonneg (time : ℕ) :
    0 ≤ chain.remainingCapacity time := by
  unfold remainingCapacity
  have hle := quittingPunishmentFloorReachablePotential_le_chargeBound
    (anchoredChargeBound regime) (chain.state time)
  linarith

/-- Remaining capacity telescopes one reachable chronological edge. -/
theorem charge_add_remainingCapacity_succ_le (time : ℕ) :
    chain.charge time + chain.remainingCapacity (time + 1) ≤
      chain.remainingCapacity time := by
  have hdecrement :=
    quittingPunishmentFloorReachablePotential_predecessor_decrement
      (anchoredChargeBound regime) (chain.edge time)
  rw [chain.edge_current time, chain.edge_tail time] at hdecrement
  unfold charge remainingCapacity
  linarith

theorem aggregateCapacityAccount_nonneg (time : ℕ) :
    0 ≤ chain.aggregateCapacityAccount time := by
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (quittingRewardBound_nonneg reward))
    (chain.remainingCapacity_nonneg (regime := regime) time)

omit regime in
/-- Aggregate diagonal seam is paid by the uniformly scaled legal charge. -/
theorem source_le_card_mul_rewardBound_mul_charge (time : ℕ) :
    chain.source time ≤
      (Fintype.card ι : ℝ) * quittingRewardBound reward *
        chain.charge time := by
  have hroot : quittingRootOfSimplex (chain.debtState time).1.2 =
      (chain.edge time).toBoxEdge.root := by
    unfold QuittingPunishmentFloorReachableEdge.toBoxEdge
      QuittingPunishmentFloorBoxEdge.root
    rw [chain.debtPoint time, ← chain.edge_current time]
  have hpoint (who : ι) :
      quittingDynamicDebtSeam (chain.debtState time) who ≤
        quittingRewardBound reward * chain.charge time := by
    have hraw := quittingDynamicDebtSeam_le_cap_mul_absorptionMass
      (chain.debtState time) (chain.debt_mem time) who
    have hcap : quittingPositiveSingletonDebtCap reward who ≤
        quittingRewardBound reward :=
      (le_abs_self _).trans
        (abs_quittingPositiveSingletonDebtCap_le_rewardBound reward who)
    have hcharge0 : 0 ≤ chain.charge time :=
      (chain.edge time).toBoxEdge.absorptionCharge_nonneg
    rw [hroot] at hraw
    exact hraw.trans (mul_le_mul_of_nonneg_right hcap hcharge0)
  unfold source
  calc
    (∑ who, quittingDynamicDebtSeam (chain.debtState time) who) ≤
        ∑ _who : ι,
          (quittingRewardBound reward * chain.charge time) := by
      apply Finset.sum_le_sum
      intro who _
      exact hpoint who
    _ = (Fintype.card ι : ℝ) * quittingRewardBound reward *
        chain.charge time := by simp [mul_assoc]

/-- The scaled remaining capacity pays the aggregate seam and retains its
successor account. -/
theorem source_add_aggregateCapacityAccount_succ_le (time : ℕ) :
    chain.source time + chain.aggregateCapacityAccount (time + 1) ≤
      chain.aggregateCapacityAccount time := by
  let scale := (Fintype.card ι : ℝ) * quittingRewardBound reward
  have hscale : 0 ≤ scale :=
    mul_nonneg (Nat.cast_nonneg _) (quittingRewardBound_nonneg reward)
  have hsource := chain.source_le_card_mul_rewardBound_mul_charge time
  have hremaining :=
    chain.charge_add_remainingCapacity_succ_le (regime := regime) time
  calc
    chain.source time + chain.aggregateCapacityAccount (time + 1) ≤
        scale * chain.charge time +
          chain.aggregateCapacityAccount (time + 1) :=
      add_le_add_left hsource _
    _ = scale *
        (chain.charge time + chain.remainingCapacity (time + 1)) := by
      simp [aggregateCapacityAccount, scale]
      ring
    _ ≤ scale * chain.remainingCapacity time :=
      mul_le_mul_of_nonneg_left hremaining hscale
    _ = chain.aggregateCapacityAccount time := rfl

omit regime in
/-- Exact aggregate dynamic debt obeys the killed reference recursion. -/
theorem debt_step (time : ℕ) :
    chain.debt time = chain.source time +
      chain.survival time * chain.debt (time + 1) := by
  have hcoordinate (who : ι) :=
    quittingDynamicDebt_eq_continueMass_mul_add_seam
      (chain.debtState time) (chain.debtState (time + 1))
      (chain.debt_edge time) (chain.debt_mem (time + 1)).2.1 who
  unfold debt source survival
  calc
    (∑ who, (chain.debtState time).2 who) =
        ∑ who,
          (quittingDynamicDebtSeam (chain.debtState time) who +
            quittingStationaryContinueMass
                (quittingRootOfSimplex (chain.debtState time).1.2) *
              (chain.debtState (time + 1)).2 who) := by
      apply Finset.sum_congr rfl
      intro who _
      linarith [hcoordinate who]
    _ = (∑ who, quittingDynamicDebtSeam (chain.debtState time) who) +
        quittingStationaryContinueMass
            (quittingRootOfSimplex (chain.debtState time).1.2) *
          ∑ who, (chain.debtState (time + 1)).2 who := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]

omit regime in
theorem survival_nonneg (time : ℕ) : 0 ≤ chain.survival time :=
  quittingStationaryContinueMass_nonneg _

/-- The aggregate remaining-capacity account is excessive for exact debt. -/
theorem aggregateCapacityAccount_isKilledExcessive :
    IsKilledExcessive chain.survival chain.source
      chain.aggregateCapacityAccount := by
  intro time
  have hadditive :=
    chain.source_add_aggregateCapacityAccount_succ_le
      (regime := regime) time
  have hsurvival : chain.survival time ≤ 1 :=
    quittingStationaryContinueMass_le_one _
  have haccount :=
    chain.aggregateCapacityAccount_nonneg (regime := regime) (time + 1)
  calc
    chain.source time + chain.survival time *
        chain.aggregateCapacityAccount (time + 1) ≤
      chain.source time + chain.aggregateCapacityAccount (time + 1) := by
        exact add_le_add_right
          (mul_le_of_le_one_left haccount hsurvival) _
    _ ≤ chain.aggregateCapacityAccount time := hadditive

/-- **Finite carried-debt telescope.**  Once the one surviving far-end exact
debt boundary is dominated by the capacity account's boundary, all earlier
carried debt and diagonal seams are bounded by initial remaining capacity.

This boundary comparison is the precise premise not implied by reachable
attachment, exact edges, or finite prefix-charge capacity. -/
theorem debt_le_aggregateCapacityAccount_of_boundary
    (start fuel : ℕ)
    (hboundary :
      killedBoundaryRemainder chain.survival chain.debt start fuel ≤
        killedBoundaryRemainder chain.survival
          chain.aggregateCapacityAccount start fuel) :
    chain.debt start ≤ chain.aggregateCapacityAccount start := by
  have href : chain.debt start =
      killedTailAccount chain.survival chain.source chain.debt start fuel :=
    potential_eq_killedTailAccount chain.survival chain.source chain.debt
      chain.debt_step start fuel
  have haccount := killedTailAccount_le_of_excessive
    chain.survival chain.source chain.aggregateCapacityAccount
      chain.survival_nonneg
      (chain.aggregateCapacityAccount_isKilledExcessive (regime := regime))
      start fuel
  unfold killedTailAccount at href haccount
  linarith

/-- Pointwise domination at the far endpoint is sufficient for the exact
survival-weighted boundary comparison.  This is the minimal direct
co-realization premise: it compares debt and remaining charge capacity on
the *same* reachable state. -/
theorem debt_le_aggregateCapacityAccount_of_far_value
    (start fuel : ℕ)
    (hfar : chain.debt (start + fuel) ≤
      chain.aggregateCapacityAccount (start + fuel)) :
    chain.debt start ≤ chain.aggregateCapacityAccount start := by
  apply chain.debt_le_aggregateCapacityAccount_of_boundary
    (regime := regime) start fuel
  unfold killedBoundaryRemainder
  exact mul_le_mul_of_nonneg_left hfar
    (killedPrefixWeight_nonneg chain.survival chain.survival_nonneg start fuel)

/-- If the chronological window is already killed before its far boundary,
the carried term vanishes and the capacity telescope closes without any
endpoint comparison.  This is the exact finite special branch available
without projective boundary provenance. -/
theorem debt_le_aggregateCapacityAccount_of_prefixWeight_eq_zero
    (start fuel : ℕ)
    (hkilled : killedPrefixWeight chain.survival start fuel = 0) :
    chain.debt start ≤ chain.aggregateCapacityAccount start := by
  apply chain.debt_le_aggregateCapacityAccount_of_boundary
    (regime := regime) start fuel
  simp [killedBoundaryRemainder, hkilled]

/-- Without a far-boundary comparison, the exact telescope leaves only the
survival-weighted debt boundary as an additive error.  Thus a cofinal
subsequence can close the initial inequality if it makes this precise
remainder tend to zero; fixed-coordinate convergence of prescribed values
alone does not mention this term. -/
theorem debt_le_aggregateCapacityAccount_add_boundary
    (start fuel : ℕ) :
    chain.debt start ≤ chain.aggregateCapacityAccount start +
      killedBoundaryRemainder chain.survival chain.debt start fuel := by
  have href : chain.debt start =
      killedTailAccount chain.survival chain.source chain.debt start fuel :=
    potential_eq_killedTailAccount chain.survival chain.source chain.debt
      chain.debt_step start fuel
  have haccount := killedTailAccount_le_of_excessive
    chain.survival chain.source chain.aggregateCapacityAccount
      chain.survival_nonneg
      (chain.aggregateCapacityAccount_isKilledExcessive (regime := regime))
      start fuel
  have hboundary_nonneg :
      0 ≤ killedBoundaryRemainder chain.survival
        chain.aggregateCapacityAccount start fuel :=
    killedBoundaryRemainder_nonneg chain.survival
      chain.aggregateCapacityAccount chain.survival_nonneg
      (chain.aggregateCapacityAccount_nonneg (regime := regime)) start fuel
  unfold killedTailAccount at href haccount
  linarith

/-- Quantitative cofinal form of the remaining provenance gate. -/
theorem debt_le_aggregateCapacityAccount_add_of_boundary_le
    (start fuel : ℕ) {error : ℝ}
    (hboundary :
      killedBoundaryRemainder chain.survival chain.debt start fuel ≤ error) :
    chain.debt start ≤ chain.aggregateCapacityAccount start + error := by
  linarith [chain.debt_le_aggregateCapacityAccount_add_boundary
    (regime := regime) start fuel]

end QuittingReachableDynamicDebtChronology

end GameTheory
