/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Debt.Dynamic.DebtProjectiveTail
import UniformEquilibrium.Quitting.Debt.Dynamic.DynamicDebtAugmentedEdge
import UniformEquilibrium.Quitting.Paths.OpponentClockDichotomy

/-!
# Projective chronological limits of exact dynamic-debt tails

This file repeats the projective compactness passage for the exact Bellman
debt, rather than the coarser multiplicative terminal-debt envelope.  Genuine
residual-horizon escape yields one chronological infinite path in the compact
exact dynamic-debt graph.

Along any such path, exact debt is nondecreasing forward and is bounded by
the positive singleton cap.  Consequently a divergent opponent clock forces
the corresponding debt coordinate to vanish at every fixed start.  Thus a
positive exact debt selects the summable-clock branch.  This is a structural
tail restriction, not an equilibrium or recurrence theorem.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.ProbabilityMassFunction
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Coordinatewise continuity of total exact dynamic-debt loss. -/
theorem continuous_quittingDynamicDebtEdgeLoss :
    Continuous (fun edge : QuittingDebtPoint ι × QuittingDebtPoint ι ↦
      quittingDynamicDebtEdgeLoss edge.1 edge.2) := by
  unfold quittingDynamicDebtEdgeLoss quittingDynamicDebtCoordinateLoss
  fun_prop

/-- Every fixed adjacent pair eventually lies in the exact dynamic-debt graph
when residual depth tends to infinity. -/
theorem eventually_projective_adjacentPair_mem_dynamicDebtEdgeGraph
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (depth : ℕ → ℕ)
    (tail : ℕ → ℕ → QuittingDebtPoint ι)
    (hbox : ∀ family time, tail family time ∈ quittingDebtBox reward)
    (hedge : ∀ family time, time < depth family →
      IsQuittingDynamicDebtEdge reward
        (tail family time) (tail family (time + 1)))
    (hdepth : Tendsto depth atTop atTop)
    (subseq : ℕ → ℕ) (hsubseq : StrictMono subseq) (time : ℕ) :
    ∀ᶠ family in atTop,
      (tail (subseq family) time, tail (subseq family) (time + 1)) ∈
        quittingDynamicDebtEdgeGraph reward := by
  have hdepthSubseq : Tendsto (depth ∘ subseq) atTop atTop :=
    hdepth.comp hsubseq.tendsto_atTop
  filter_upwards [tendsto_atTop.1 hdepthSubseq (time + 1)] with family hfamily
  change time + 1 ≤ depth (subseq family) at hfamily
  exact ⟨hbox (subseq family) time, hbox (subseq family) (time + 1),
    hedge (subseq family) time (by omega)⟩

/-- Genuine residual-horizon escape extracts one projectively compatible
infinite tail from finite exact dynamic-debt tails. -/
theorem exists_projective_quittingDynamicDebtTail_of_residualDepth_tendsto
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (depth : ℕ → ℕ)
    (tail : ℕ → ℕ → QuittingDebtPoint ι)
    (hbox : ∀ family time, tail family time ∈ quittingDebtBox reward)
    (hedge : ∀ family time, time < depth family →
      IsQuittingDynamicDebtEdge reward
        (tail family time) (tail family (time + 1)))
    (hdepth : Tendsto depth atTop atTop) :
    ∃ (limit : ℕ → QuittingDebtPoint ι) (subseq : ℕ → ℕ),
      StrictMono subseq ∧
      Tendsto ((fun family ↦ tail family) ∘ subseq) atTop (nhds limit) ∧
      (∀ time, limit time ∈ quittingDebtBox reward) ∧
      ∀ time,
        IsQuittingDynamicDebtEdge reward
          (limit time) (limit (time + 1)) := by
  obtain ⟨limit, subseq, hsubseq, hlimit, hlimitBox⟩ :=
    exists_projective_quittingDebtTail_limit
      (reward := reward) (tail := tail) hbox
  refine ⟨limit, subseq, hsubseq, hlimit, hlimitBox, ?_⟩
  intro time
  exact isQuittingDynamicDebtEdge_of_tendsto_edgeGraph
    (edge := (limit time, limit (time + 1)))
    (candidate := fun family ↦
      (tail (subseq family) time, tail (subseq family) (time + 1)))
    reward (tendsto_projective_adjacentPair tail limit subseq hlimit time)
    (eventually_projective_adjacentPair_mem_dynamicDebtEdgeGraph
      reward depth tail hbox hedge hdepth subseq hsubseq time)

omit [DecidableEq ι] in
/-- Vanishing dynamic-debt loss along a convergent projective subsequence
passes to each fixed adjacent pair. -/
theorem quittingDynamicDebtEdgeLoss_eq_zero_of_projective_limit
    (tail : ℕ → ℕ → QuittingDebtPoint ι)
    (limit : ℕ → QuittingDebtPoint ι) (subseq : ℕ → ℕ)
    (hsubseq : StrictMono subseq)
    (hlimit : Tendsto ((fun family ↦ tail family) ∘ subseq)
      atTop (nhds limit))
    (hloss : ∀ time, Tendsto
      (fun family ↦ quittingDynamicDebtEdgeLoss
        (tail family time) (tail family (time + 1))) atTop (nhds 0))
    (time : ℕ) :
    quittingDynamicDebtEdgeLoss (limit time) (limit (time + 1)) = 0 := by
  have hpairs := tendsto_projective_adjacentPair tail limit subseq hlimit time
  have hlimitLoss := (continuous_quittingDynamicDebtEdgeLoss.tendsto
    (limit time, limit (time + 1))).comp hpairs
  have hzeroLoss := (hloss time).comp hsubseq.tendsto_atTop
  exact tendsto_nhds_unique hlimitLoss hzeroLoss

/-- Vanishing fixed-edge exact-debt loss is retained by the projective
limit.  This hypothesis is deliberately explicit: minimum-value convergence
alone does not supply it. -/
theorem exists_projective_zeroLoss_quittingDynamicDebtTail
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (depth : ℕ → ℕ)
    (tail : ℕ → ℕ → QuittingDebtPoint ι)
    (hbox : ∀ family time, tail family time ∈ quittingDebtBox reward)
    (hedge : ∀ family time, time < depth family →
      IsQuittingDynamicDebtEdge reward
        (tail family time) (tail family (time + 1)))
    (hdepth : Tendsto depth atTop atTop)
    (hloss : ∀ time, Tendsto
      (fun family ↦ quittingDynamicDebtEdgeLoss
        (tail family time) (tail family (time + 1)))
      atTop (nhds 0)) :
    ∃ (limit : ℕ → QuittingDebtPoint ι) (subseq : ℕ → ℕ),
      StrictMono subseq ∧
      Tendsto ((fun family ↦ tail family) ∘ subseq) atTop (nhds limit) ∧
      (∀ time, limit time ∈ quittingDebtBox reward) ∧
      (∀ time,
        IsQuittingDynamicDebtEdge reward
          (limit time) (limit (time + 1))) ∧
      ∀ time,
        quittingDynamicDebtEdgeLoss (limit time) (limit (time + 1)) = 0 := by
  obtain ⟨limit, subseq, hsubseq, hlimit, hlimitBox, hedgeLimit⟩ :=
    exists_projective_quittingDynamicDebtTail_of_residualDepth_tendsto
      reward depth tail hbox hedge hdepth
  refine ⟨limit, subseq, hsubseq, hlimit, hlimitBox, hedgeLimit, ?_⟩
  intro time
  exact quittingDynamicDebtEdgeLoss_eq_zero_of_projective_limit
    tail limit subseq hsubseq hlimit hloss time

/-! ## The divergent-clock branch -/

/-- Operational roots displayed by an exact dynamic-debt tail. -/
def quittingDynamicDebtTailRoots
    (path : ℕ → QuittingDebtPoint ι) (time : ℕ) : ι → PMF Bool :=
  quittingRootOfSimplex (path time).1.2

/-- The path's simplex opponent mass is exactly its operational fixed-
opponents Continue mass. -/
theorem quittingFixedOpponentsContinueMass_dynamicDebtTailRoots_eq
    (path : ℕ → QuittingDebtPoint ι) (who : ι) (time : ℕ) :
    quittingFixedOpponentsContinueMass
        (quittingDynamicDebtTailRoots path) who time =
      quittingDebtOpponentContinueMass (path time) who := by
  unfold quittingFixedOpponentsContinueMass quittingDynamicDebtTailRoots
  exact (quittingDebtOpponentContinueMass_eq_stationary
    (path time) who).symm

/-- Exact debt along an infinite exact-D path is bounded by the product of
the intervening opponent Continue masses times the later debt. -/
theorem quittingDynamicDebtTail_le_survival_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (path : ℕ → QuittingDebtPoint ι)
    (hbox : ∀ time, path time ∈ quittingDebtBox reward)
    (hedge : ∀ time,
      IsQuittingDynamicDebtEdge reward (path time) (path (time + 1)))
    (who : ι) :
    ∀ start fuel,
      (path start).2 who ≤
        quittingOpponentSurvivalWeight
            (quittingDynamicDebtTailRoots path) who start fuel *
          (path (start + fuel)).2 who := by
  intro start fuel
  induction fuel with
  | zero =>
      simp [quittingOpponentSurvivalWeight]
  | succ fuel ih =>
      have hstep := quittingDynamicDebtUpdate_le_mul reward
        (path (start + fuel)) (path (start + fuel + 1))
        (hedge (start + fuel)).1 (hbox (start + fuel + 1)).2.1 who
      rw [← (hedge (start + fuel)).2 who,
        ← quittingFixedOpponentsContinueMass_dynamicDebtTailRoots_eq]
        at hstep
      have hsurvival : 0 ≤ quittingOpponentSurvivalWeight
          (quittingDynamicDebtTailRoots path) who start fuel :=
        quittingOpponentSurvivalWeight_nonneg _ who start fuel
      calc
        (path start).2 who ≤
            quittingOpponentSurvivalWeight
                (quittingDynamicDebtTailRoots path) who start fuel *
              (path (start + fuel)).2 who := ih
        _ ≤ quittingOpponentSurvivalWeight
                (quittingDynamicDebtTailRoots path) who start fuel *
              (quittingFixedOpponentsContinueMass
                  (quittingDynamicDebtTailRoots path) who (start + fuel) *
                (path (start + fuel + 1)).2 who) :=
          mul_le_mul_of_nonneg_left hstep hsurvival
        _ = quittingOpponentSurvivalWeight
                (quittingDynamicDebtTailRoots path) who start (fuel + 1) *
              (path (start + (fuel + 1))).2 who := by
          rw [quittingOpponentSurvivalWeight_succ]
          have hindex : start + fuel + 1 = start + (fuel + 1) := by omega
          rw [hindex]
          ring

/-- A divergent opponent clock discharges the corresponding exact debt at
every fixed point of an infinite bounded exact-D path. -/
theorem quittingDynamicDebtTail_eq_zero_of_not_summable_clock
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (path : ℕ → QuittingDebtPoint ι)
    (hbox : ∀ time, path time ∈ quittingDebtBox reward)
    (hedge : ∀ time,
      IsQuittingDynamicDebtEdge reward (path time) (path (time + 1)))
    (who : ι)
    (hclock : ¬Summable (quittingOpponentClockCharge
      (quittingDynamicDebtTailRoots path) who)) :
    ∀ start, (path start).2 who = 0 := by
  intro start
  have hclockSuffix : ¬Summable (fun offset ↦
      quittingOpponentClockCharge
        (quittingDynamicDebtTailRoots path) who (start + offset)) := by
    intro hsuffix
    have hshift : Summable (fun offset ↦
        quittingOpponentClockCharge
          (quittingDynamicDebtTailRoots path) who (offset + start)) := by
      simpa [Nat.add_comm] using hsuffix
    exact hclock ((summable_nat_add_iff start).1 hshift)
  have hsurvival : Tendsto
      (quittingOpponentSurvivalWeight
        (quittingDynamicDebtTailRoots path) who start)
      atTop (nhds 0) :=
    tendsto_zero_quittingOpponentSurvivalWeight_of_not_summable_charge
      (quittingDynamicDebtTailRoots path) who start hclockSuffix
  let cap := quittingPositiveSingletonDebtCap reward who
  have hcap0 : 0 ≤ cap := le_max_left _ _
  have hscaled : Tendsto
      (fun fuel ↦ quittingOpponentSurvivalWeight
        (quittingDynamicDebtTailRoots path) who start fuel * cap)
      atTop (nhds 0) := by
    simpa using hsurvival.mul_const cap
  have hupper : ∀ fuel,
      (path start).2 who ≤
        quittingOpponentSurvivalWeight
          (quittingDynamicDebtTailRoots path) who start fuel * cap := by
    intro fuel
    exact (quittingDynamicDebtTail_le_survival_mul
      reward path hbox hedge who start fuel).trans
        (mul_le_mul_of_nonneg_left
          ((hbox (start + fuel)).2.2 who)
          (quittingOpponentSurvivalWeight_nonneg _ who start fuel))
  have hle : (path start).2 who ≤ 0 := ge_of_tendsto' hscaled hupper
  exact le_antisymm hle ((hbox start).2.1 who)

/-- Contrapositive form: a positive exact debt coordinate selects the
summable opponent-clock branch. -/
theorem summable_clock_of_quittingDynamicDebtTail_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (path : ℕ → QuittingDebtPoint ι)
    (hbox : ∀ time, path time ∈ quittingDebtBox reward)
    (hedge : ∀ time,
      IsQuittingDynamicDebtEdge reward (path time) (path (time + 1)))
    (who : ι) (start : ℕ) (hdebt : 0 < (path start).2 who) :
    Summable (quittingOpponentClockCharge
      (quittingDynamicDebtTailRoots path) who) := by
  by_contra hclock
  have hzero := quittingDynamicDebtTail_eq_zero_of_not_summable_clock
    reward path hbox hedge who hclock start
  linarith

end GameTheory
