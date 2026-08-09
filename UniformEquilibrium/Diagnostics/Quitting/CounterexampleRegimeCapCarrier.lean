/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeDebtConservation
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTailBridge
import UniformEquilibrium.Quitting.Debt.Dynamic.FiniteDynamicDebtCapCarrier

/-!
# The optimized tail's augmented caps in the floor carrier

Each finite optimized exact-D annotation is the cap of a zero-boundary finite
stopping problem, hence lies in the canonical reward box and dominates the
complete behavioral punishment floor.  Both conditions are closed.  The
projective limit therefore retains them at every finite date, and the joint
value/debt limit retains them at the all-Continue boundary.

The limiting augmented cap is itself an exact all-Continue Nash--Bellman
self-loop with zero absorption charge.  This places it literally in the
global floor-admissible charged state space.  The chronological dynamic-debt
tail does not thereby become a path in that relation: its finite transitions
still carry the exact diagonal seam proved in `DynamicDebtCapBridge`.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.ProbabilityMassFunction
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {regime : QuittingCounterexampleRegime reward}

namespace QuittingCounterexampleSeamWitness

variable (seam : QuittingCounterexampleSeamWitness regime)

/-- Every augmented cap of the optimized projective tail lies in the
canonical reward carrier and dominates the behavioral punishment floor. -/
theorem tailDynamicDebtCap_mem_and_floor (time : ℕ) :
    quittingDynamicDebtCap (seam.tail time) ∈
        quittingPunishmentFloorForwardCarrier reward ∧
      ∀ who, quittingPunishmentValue reward who ≤
        quittingDynamicDebtCap (seam.tail time) who := by
  letI : Nonempty ι := regime.nonempty_players
  have hpoint : Tendsto (fun family ↦
      quittingFiniteMinMaxDynamicDebtTail reward (seam.subseq family) time)
      atTop (nhds (seam.tail time)) := by
    exact ((continuous_apply time).tendsto seam.tail).comp
      seam.projective_limit
  have hcap : Tendsto (fun family ↦ quittingDynamicDebtCap
      (quittingFiniteMinMaxDynamicDebtTail reward
        (seam.subseq family) time)) atTop
      (nhds (quittingDynamicDebtCap (seam.tail time))) :=
    (continuous_quittingDynamicDebtCap.tendsto (seam.tail time)).comp hpoint
  have hcutoff : ∀ᶠ family in atTop, time ≤ seam.subseq family :=
    (seam.subseq_strict.tendsto_atTop.eventually_ge_atTop time)
  have hfinite : ∀ᶠ family in atTop,
      quittingDynamicDebtCap
          (quittingFiniteMinMaxDynamicDebtTail reward
            (seam.subseq family) time) ∈
          quittingPunishmentFloorForwardCarrier reward ∧
        ∀ who, quittingPunishmentValue reward who ≤
          quittingDynamicDebtCap
            (quittingFiniteMinMaxDynamicDebtTail reward
              (seam.subseq family) time) who := by
    filter_upwards [hcutoff] with family htime
    exact quittingFiniteNashBellmanPathDynamicDebtCap_mem_and_floor
      reward (seam.subseq family)
        (quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer
          reward (seam.subseq family))
        (quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer_mem
          reward (seam.subseq family)) time htime
  constructor
  · exact isClosed_Icc.mem_of_tendsto hcap (hfinite.mono fun _ h ↦ h.1)
  · intro who
    have hcoordinate : Tendsto (fun family ↦
        quittingDynamicDebtCap
          (quittingFiniteMinMaxDynamicDebtTail reward
            (seam.subseq family) time) who) atTop
        (nhds (quittingDynamicDebtCap (seam.tail time) who)) :=
      ((continuous_apply who).tendsto
        (quittingDynamicDebtCap (seam.tail time))).comp hcap
    exact ge_of_tendsto hcoordinate
      (hfinite.mono fun _ h ↦ h.2 who)

/-- **All-date punishment rationality of the unaugmented optimized tail.**
Every prescribed value of the selected exact-D tail already dominates the
complete behavioral punishment floor.  If the displayed debt is zero this
is the augmented-cap inequality with the augmentation removed; if it is
positive, exact-debt persistence and the limiting self-loop remove it. -/
theorem punishmentValue_le_tailValue (time : ℕ) (who : ι) :
    quittingPunishmentValue reward who ≤ (seam.tail time).1.1 who := by
  letI : Nonempty ι := regime.nonempty_players
  by_cases hdebt : (seam.tail time).2 who = 0
  · have hfloor := (seam.tailDynamicDebtCap_mem_and_floor time).2 who
    simpa [quittingDynamicDebtCap_apply, hdebt] using hfloor
  · have hdebtNonneg := (seam.tail_mem time).2.1 who
    exact seam.punishmentValue_le_tailValue_of_debt_pos who time
      (lt_of_le_of_ne hdebtNonneg (Ne.symm hdebt))

/-- Every finite chronological segment of the optimized exact-D tail,
reversed from its far endpoint, is a literal punishment-floor predecessor
prefix.  No endpoint-floor hypothesis remains for this selected tail. -/
def tailSegmentPunishmentFloorPrefix (horizon : ℕ) :
    QuittingPunishmentFloorFinitePrefix reward := by
  letI : Nonempty ι := regime.nonempty_players
  exact quittingDynamicDebtSegmentToPunishmentFloorPrefix seam.tail horizon
    (fun time _ ↦ seam.tail_mem time)
    (fun time _ ↦ seam.tail_edge time)
    (seam.punishmentValue_le_tailValue horizon)

/-- Reversing the optimized segment preserves its literal joint absorption
charge exactly. -/
theorem tailSegmentPunishmentFloorPrefix_charge (horizon : ℕ) :
    (seam.tailSegmentPunishmentFloorPrefix horizon).charge =
      ∑ time ∈ Finset.range horizon,
        quittingDynamicDebtTailAbsorptionCharge seam.tail time := by
  letI : Nonempty ι := regime.nonempty_players
  exact quittingDynamicDebtSegmentToPunishmentFloorPrefix_charge seam.tail
    horizon (fun time _ ↦ seam.tail_mem time)
      (fun time _ ↦ seam.tail_edge time)
      (seam.punishmentValue_le_tailValue horizon)

/-- The all-Continue limiting augmented cap. -/
def limitDynamicDebtCap : Payoff ι :=
  seam.limit.value + seam.limit.debt

@[simp]
theorem limitDynamicDebtCap_apply (who : ι) :
    seam.limitDynamicDebtCap who =
      seam.limit.value who + seam.limit.debt who := by
  rfl

/-- Tail caps converge coordinatewise to the limiting augmented cap. -/
theorem tailDynamicDebtCap_tendsto (who : ι) :
    Tendsto (fun time ↦ quittingDynamicDebtCap (seam.tail time) who)
      atTop (nhds (seam.limitDynamicDebtCap who)) := by
  simpa [quittingDynamicDebtCap_apply, limitDynamicDebtCap_apply] using
    (seam.value_tendsto who).add (seam.debt_tendsto who)

/-- The limiting augmented cap remains boxed and floor-admissible. -/
theorem limitDynamicDebtCap_mem_and_floor :
    seam.limitDynamicDebtCap ∈
        quittingPunishmentFloorForwardCarrier reward ∧
      ∀ who, quittingPunishmentValue reward who ≤
        seam.limitDynamicDebtCap who := by
  constructor
  · constructor
    · intro who
      exact ge_of_tendsto' (seam.tailDynamicDebtCap_tendsto who)
        (fun time ↦ (seam.tailDynamicDebtCap_mem_and_floor time).1.1 who)
    · intro who
      exact le_of_tendsto' (seam.tailDynamicDebtCap_tendsto who)
        (fun time ↦ (seam.tailDynamicDebtCap_mem_and_floor time).1.2 who)
  · intro who
    exact ge_of_tendsto' (seam.tailDynamicDebtCap_tendsto who)
      (fun time ↦ (seam.tailDynamicDebtCap_mem_and_floor time).2 who)

/-- The limiting augmented cap and all-Continue marker as a literal state of
the global boxed floor-admissible carrier. -/
def limitDynamicDebtCapAdmissibleState :
    QuittingPunishmentFloorAdmissibleState reward :=
  ⟨⟨(seam.limitDynamicDebtCap, quittingAllContinueSimplexRoot),
      seam.limitDynamicDebtCap_mem_and_floor.1⟩,
    seam.limitDynamicDebtCap_mem_and_floor.2⟩

/-- The limiting augmented cap is an exact all-Continue Nash--Bellman
self-loop. -/
theorem limitDynamicDebtCap_exactSelfLoop :
    IsQuittingNashBellmanEdge reward
      (seam.limitDynamicDebtCap, quittingAllContinueSimplexRoot)
      (seam.limitDynamicDebtCap, quittingAllContinueSimplexRoot) := by
  constructor
  · change seam.limitDynamicDebtCap =
      quittingRootSuccessorPayoff reward seam.limitDynamicDebtCap
        (quittingRootOfSimplex quittingAllContinueSimplexRoot)
    rw [quittingRootOfSimplex_allContinueSimplexRoot,
      quittingRootSuccessorPayoff_allContinueRoot_eq]
  · change IsεQuittingRootEndpointNash reward seam.limitDynamicDebtCap 0
      (quittingRootOfSimplex quittingAllContinueSimplexRoot)
    rw [quittingRootOfSimplex_allContinueSimplexRoot,
      isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash]
    apply quittingAllContinueRoot_isZeroNash_of_singleton_le
    intro who
    have hquit :=
      quittingRootQuitPayoff_le_currentValue_of_nashBellmanEdge
        reward (seam.limit.value, quittingAllContinueSimplexRoot)
          (seam.limit.value, quittingAllContinueSimplexRoot)
          seam.limit.exactSelfLoop.1 who
    have hsolo : reward (quittingSingletonTerminal who) who ≤
        seam.limit.value who := by
      simpa [quittingRootOfSimplex_allContinueSimplexRoot] using hquit
    exact hsolo.trans (le_add_of_nonneg_right
      (seam.limit.state_mem.2.1 who))

/-- The limiting augmented cap's self-loop as an edge of the global
floor-admissible charged relation. -/
def limitDynamicDebtCapAdmissibleSelfLoop :
    QuittingPunishmentFloorAdmissibleEdge reward where
  tail := seam.limitDynamicDebtCapAdmissibleState
  current := seam.limitDynamicDebtCapAdmissibleState
  exactEdge := seam.limitDynamicDebtCap_exactSelfLoop

/-- The limiting cap self-loop has literal zero absorption charge. -/
@[simp]
theorem limitDynamicDebtCapAdmissibleSelfLoop_charge_eq_zero :
    seam.limitDynamicDebtCapAdmissibleSelfLoop.toBoxEdge.absorptionCharge = 0 := by
  change quittingRootAbsorptionMass
    (quittingRootOfSimplex quittingAllContinueSimplexRoot) = 0
  rw [quittingRootOfSimplex_allContinueSimplexRoot]
  exact quittingRootAbsorptionMass_allContinueRoot

end QuittingCounterexampleSeamWitness

end GameTheory
