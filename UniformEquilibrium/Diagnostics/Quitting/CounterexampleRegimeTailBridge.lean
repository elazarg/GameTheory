/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeQuantitative

/-!
# The exact-debt tail / punishment-prefix bridge

An exact dynamic-debt tail is chronological: its edge at time `t` runs from
the current Nash--Bellman state to its continuation at `t + 1`.  A
punishment-floor prefix has the opposite orientation: it grows outward from
an individually rational terminal anchor by choosing exact predecessors.

Consequently a finite dynamic-debt segment can be reversed into a
punishment-floor prefix whenever its far endpoint dominates the punishment
floor.  This is the generic bridge between the two carriers, and it records
the consequence that cofinally floor-dominating endpoints force summable
joint absorption.  For the optimized counterexample tail, the endpoint premise
is discharged downstream by all-date punishment rationality in
`CounterexampleRegimeCapCarrier`; the generic conditional interface remains
useful for arbitrary exact-D tails.

The endpoint hypothesis cannot be dropped merely by translating payoffs.
The quitting game's nonabsorbing payoff is fixed at zero, so a coordinatewise
translation changes the never-absorbed outcome and is not a harmless
normalization of the uniform-equilibrium problem.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-! ## Reversing one exact-debt segment -/

/-- Payoffs of a chronological exact-debt segment, read backward from its
far endpoint. -/
def quittingDynamicDebtReverseValue
    (tail : ℕ → QuittingDebtPoint ι) (horizon time : ℕ) : Payoff ι :=
  (tail (horizon - time)).1.1

/-- The predecessor root of a chronological exact-debt segment, read in the
matching backward order. -/
def quittingDynamicDebtReverseRoot
    (tail : ℕ → QuittingDebtPoint ι) (horizon time : ℕ) : ι → PMF Bool :=
  quittingRootOfSimplex (tail (horizon - (time + 1))).1.2

/-- Reverse a boxed exact dynamic-debt segment whose far endpoint dominates
the punishment floor into an exact punishment-floor prefix.  The debt
coordinates are forgotten; the Nash--Bellman edge and its literal root are
retained exactly. -/
def quittingDynamicDebtSegmentToPunishmentFloorPrefix
    (tail : ℕ → QuittingDebtPoint ι) (horizon : ℕ)
    (hbox : ∀ time, time ≤ horizon → tail time ∈ quittingDebtBox reward)
    (hedge : ∀ time, time < horizon →
      IsQuittingDynamicDebtEdge reward (tail time) (tail (time + 1)))
    (hfloor : ∀ who,
      quittingPunishmentValue reward who ≤ (tail horizon).1.1 who) :
    QuittingPunishmentFloorFinitePrefix reward where
  roots := quittingDynamicDebtReverseRoot tail horizon
  value := quittingDynamicDebtReverseValue tail horizon
  horizon := horizon
  value_mem := by
    intro time htime
    exact (hbox (horizon - time) (Nat.sub_le _ _)).1
  anchor_floor := by
    simpa [quittingDynamicDebtReverseValue] using hfloor
  policy := by
    intro time htime
    have hindex : horizon - (time + 1) < horizon := by omega
    have hstep := (hedge (horizon - (time + 1)) hindex).1.1
    have hsucc : horizon - (time + 1) + 1 = horizon - time := by omega
    simpa [quittingDynamicDebtReverseValue,
      quittingDynamicDebtReverseRoot, hsucc] using hstep
  exactNash := by
    intro time htime
    have hindex : horizon - (time + 1) < horizon := by omega
    have hsucc : horizon - (time + 1) + 1 = horizon - time := by omega
    have hnashEndpoint :=
      (hedge (horizon - (time + 1)) hindex).1.2
    rw [hsucc] at hnashEndpoint
    have hnash :=
      (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
        reward (tail (horizon - time)).1.1
          (quittingRootOfSimplex
            (tail (horizon - (time + 1))).1.2)).1
        hnashEndpoint
    simpa [quittingDynamicDebtReverseValue,
      quittingDynamicDebtReverseRoot, hsucc] using hnash

omit [Nonempty ι] in
/-- Floor dominance at the far endpoint propagates backward through the
underlying Nash--Bellman values of the whole exact-D segment. -/
theorem quittingPunishmentValue_le_dynamicDebtTailValue_of_endpoint_floor
    (tail : ℕ → QuittingDebtPoint ι) (horizon : ℕ)
    (hbox : ∀ time, time ≤ horizon → tail time ∈ quittingDebtBox reward)
    (hedge : ∀ time, time < horizon →
      IsQuittingDynamicDebtEdge reward (tail time) (tail (time + 1)))
    (hfloor : ∀ who,
      quittingPunishmentValue reward who ≤ (tail horizon).1.1 who)
    (time : ℕ) (htime : time ≤ horizon) (who : ι) :
    quittingPunishmentValue reward who ≤ (tail time).1.1 who := by
  let cert := quittingDynamicDebtSegmentToPunishmentFloorPrefix tail horizon
    hbox hedge hfloor
  have hvalue := quittingPunishmentValue_le_finitePrefixValue cert
    (horizon - time) (Nat.sub_le _ _) who
  change quittingPunishmentValue reward who ≤
    (tail (horizon - (horizon - time))).1.1 who at hvalue
  rwa [Nat.sub_sub_self htime] at hvalue

/-! ## The zero-boundary specialization -/

/-- If the punishment vector is coordinatewise nonpositive, then every
displayed value of every selected finite min-max exact-D annotation dominates
the punishment floor.  Before the cutoff this follows by reversing the exact
segment from its zero endpoint; after the cutoff the annotation is padded by
that same zero endpoint. -/
theorem quittingPunishmentValue_le_finiteMinMaxDynamicDebtTail_of_nonpos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hpunishment : ∀ who, quittingPunishmentValue reward who ≤ 0)
    (cutoff time : ℕ) (who : ι) :
    quittingPunishmentValue reward who ≤
      (quittingFiniteMinMaxDynamicDebtTail reward cutoff time).1.1 who := by
  let path :=
    quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer reward cutoff
  have hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff :=
    quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer_mem
      reward cutoff
  have hterminal :
      (quittingFiniteMinMaxDynamicDebtTail reward cutoff cutoff).1.1 = 0 := by
    simp only [quittingFiniteMinMaxDynamicDebtTail,
      quittingFiniteNashBellmanPathDynamicDebtPoint, dif_pos le_rfl]
    have hindex :
        (⟨cutoff, Nat.lt_succ_self cutoff⟩ : Fin (cutoff + 1)) =
          Fin.last cutoff := by
      apply Fin.ext
      rfl
    rw [hindex]
    exact hpath.2.1
  by_cases htime : time ≤ cutoff
  · apply
      quittingPunishmentValue_le_dynamicDebtTailValue_of_endpoint_floor
        (reward := reward)
        (quittingFiniteMinMaxDynamicDebtTail reward cutoff) cutoff
        (fun point _ ↦
          quittingFiniteMinMaxDynamicDebtTail_mem_box reward cutoff point)
        (fun point hpoint ↦
          quittingFiniteMinMaxDynamicDebtTail_edge reward cutoff point hpoint)
        (fun player ↦ by rw [hterminal]; exact hpunishment player)
        time htime who
  · unfold quittingFiniteMinMaxDynamicDebtTail
      quittingFiniteNashBellmanPathDynamicDebtPoint
    rw [dif_neg htime]
    change quittingPunishmentValue reward who ≤
      (path (Fin.last cutoff)).1 who
    rw [congrFun hpath.2.1 who]
    exact hpunishment who

/-- Floor dominance of the finite zero-boundary annotations passes to every
coordinate of any projective limit.  This uses the actual product-topology
convergence supplied by projective extraction, not a heuristic closure
argument. -/
theorem quittingPunishmentValue_le_projectiveDynamicDebtTail_of_nonpos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hpunishment : ∀ who, quittingPunishmentValue reward who ≤ 0)
    (subseq : ℕ → ℕ) (limit : ℕ → QuittingDebtPoint ι)
    (hlimit : Tendsto
      ((fun cutoff ↦ quittingFiniteMinMaxDynamicDebtTail reward cutoff) ∘
        subseq) atTop (nhds limit))
    (time : ℕ) (who : ι) :
    quittingPunishmentValue reward who ≤ (limit time).1.1 who := by
  have hpoint : Tendsto
      (fun family ↦ quittingFiniteMinMaxDynamicDebtTail reward
        (subseq family) time)
      atTop (nhds (limit time)) :=
    ((continuous_apply time).tendsto limit).comp hlimit
  have hcoordinate : Continuous
      (fun point : QuittingDebtPoint ι ↦ point.1.1 who) := by
    fun_prop
  have htend : Tendsto
      (fun family ↦ (quittingFiniteMinMaxDynamicDebtTail reward
        (subseq family) time).1.1 who)
      atTop (nhds ((limit time).1.1 who)) :=
    (hcoordinate.tendsto (limit time)).comp hpoint
  exact ge_of_tendsto' htend fun family ↦
    quittingPunishmentValue_le_finiteMinMaxDynamicDebtTail_of_nonpos
      reward hpunishment (subseq family) time who

/-- Literal joint absorption charge along a chronological exact-debt tail. -/
def quittingDynamicDebtTailAbsorptionCharge
    (tail : ℕ → QuittingDebtPoint ι) (time : ℕ) : ℝ :=
  quittingRootAbsorptionMass
    (quittingRootOfSimplex (tail time).1.2)

omit [DecidableEq ι] [Nonempty ι] in
theorem quittingDynamicDebtTailAbsorptionCharge_nonneg
    (tail : ℕ → QuittingDebtPoint ι) (time : ℕ) :
    0 ≤ quittingDynamicDebtTailAbsorptionCharge tail time := by
  unfold quittingDynamicDebtTailAbsorptionCharge
    quittingRootAbsorptionMass
  exact sub_nonneg.mpr
    (quittingStationaryContinueMass_le_one
      (quittingRootOfSimplex (tail time).1.2))

omit [Nonempty ι] in
/-- Reversal changes chronology but not total joint absorption charge. -/
theorem quittingDynamicDebtSegmentToPunishmentFloorPrefix_charge
    (tail : ℕ → QuittingDebtPoint ι) (horizon : ℕ)
    (hbox : ∀ time, time ≤ horizon → tail time ∈ quittingDebtBox reward)
    (hedge : ∀ time, time < horizon →
      IsQuittingDynamicDebtEdge reward (tail time) (tail (time + 1)))
    (hfloor : ∀ who,
      quittingPunishmentValue reward who ≤ (tail horizon).1.1 who) :
    (quittingDynamicDebtSegmentToPunishmentFloorPrefix tail horizon
        hbox hedge hfloor).charge =
      ∑ time ∈ Finset.range horizon,
        quittingDynamicDebtTailAbsorptionCharge tail time := by
  change
    (∑ time ∈ Finset.range horizon,
      quittingDynamicDebtTailAbsorptionCharge tail
        (horizon - (time + 1))) = _
  calc
    (∑ time ∈ Finset.range horizon,
        quittingDynamicDebtTailAbsorptionCharge tail
          (horizon - (time + 1))) =
        ∑ time ∈ Finset.range horizon,
          quittingDynamicDebtTailAbsorptionCharge tail
            (horizon - 1 - time) := by
          apply Finset.sum_congr rfl
          intro time _
          congr 1
          omega
    _ = _ := Finset.sum_range_reflect
      (quittingDynamicDebtTailAbsorptionCharge tail) horizon

/-! ## The sharp conditional connection -/

/-- Floor-dominating endpoints occur cofinally along a tail.  This is weaker
than requiring every tail value to be individually rational. -/
def HasCofinalQuittingPunishmentFloorEndpoints
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : ℕ → QuittingDebtPoint ι) : Prop :=
  ∀ start, ∃ horizon, start ≤ horizon ∧
    ∀ who, quittingPunishmentValue reward who ≤ (tail horizon).1.1 who

namespace QuittingCounterexampleRegime

omit [Nonempty ι] in
/-- Every floor-anchorable exact-debt segment inherits the regime's common
prefix-charge bound. -/
theorem dynamicDebtTail_sum_absorptionCharge_le_of_endpoint_floor
    (regime : QuittingCounterexampleRegime reward)
    (tail : ℕ → QuittingDebtPoint ι)
    (hbox : ∀ time, tail time ∈ quittingDebtBox reward)
    (hedge : ∀ time,
      IsQuittingDynamicDebtEdge reward (tail time) (tail (time + 1)))
    (horizon : ℕ)
    (hfloor : ∀ who,
      quittingPunishmentValue reward who ≤ (tail horizon).1.1 who) :
    (∑ time ∈ Finset.range horizon,
        quittingDynamicDebtTailAbsorptionCharge tail time) ≤
      quittingPunishmentFloorPrefixChargeBound reward := by
  let cert := quittingDynamicDebtSegmentToPunishmentFloorPrefix tail horizon
    (fun time _ ↦ hbox time) (fun time _ ↦ hedge time) hfloor
  rw [← quittingDynamicDebtSegmentToPunishmentFloorPrefix_charge tail horizon
    (fun time _ ↦ hbox time) (fun time _ ↦ hedge time) hfloor]
  exact regime.prefixCharge_le cert

omit [Nonempty ι] in
/-- **Tail/prefix bridge.**  If the positive exact-debt tail returns
cofinally to the coordinatewise punishment-floor region, then its full joint
absorption charge is summable.  Thus any nonsummable counterexample tail must
eventually avoid that region at every date. -/
theorem summable_dynamicDebtTailAbsorptionCharge_of_cofinal_floor
    (regime : QuittingCounterexampleRegime reward)
    (tail : ℕ → QuittingDebtPoint ι)
    (hbox : ∀ time, tail time ∈ quittingDebtBox reward)
    (hedge : ∀ time,
      IsQuittingDynamicDebtEdge reward (tail time) (tail (time + 1)))
    (hcofinal : HasCofinalQuittingPunishmentFloorEndpoints reward tail) :
    Summable (quittingDynamicDebtTailAbsorptionCharge tail) := by
  apply summable_of_sum_range_le
    (c := quittingPunishmentFloorPrefixChargeBound reward)
    (quittingDynamicDebtTailAbsorptionCharge_nonneg tail)
  intro cutoff
  obtain ⟨horizon, hcutoff, hfloor⟩ := hcofinal cutoff
  calc
    (∑ time ∈ Finset.range cutoff,
        quittingDynamicDebtTailAbsorptionCharge tail time) ≤
        ∑ time ∈ Finset.range horizon,
          quittingDynamicDebtTailAbsorptionCharge tail time := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.range_mono hcutoff
      · intro time _ _
        exact quittingDynamicDebtTailAbsorptionCharge_nonneg tail time
    _ ≤ quittingPunishmentFloorPrefixChargeBound reward :=
      regime.dynamicDebtTail_sum_absorptionCharge_le_of_endpoint_floor
        tail hbox hedge horizon hfloor

omit [Nonempty ι] in
/-- Every boxed exact-debt tail in a counterexample regime satisfies a sharp
carrier alternative: either its joint absorption is summable, or from some
date onward every endpoint violates the punishment floor in at least one
coordinate.  The violating player may depend on the date. -/
theorem summable_dynamicDebtTailAbsorptionCharge_or_eventually_floorViolation
    (regime : QuittingCounterexampleRegime reward)
    (tail : ℕ → QuittingDebtPoint ι)
    (hbox : ∀ time, tail time ∈ quittingDebtBox reward)
    (hedge : ∀ time,
      IsQuittingDynamicDebtEdge reward (tail time) (tail (time + 1))) :
    Summable (quittingDynamicDebtTailAbsorptionCharge tail) ∨
      ∃ start, ∀ horizon, start ≤ horizon →
        ∃ who, (tail horizon).1.1 who <
          quittingPunishmentValue reward who := by
  by_cases hcofinal :
      HasCofinalQuittingPunishmentFloorEndpoints reward tail
  · exact Or.inl
      (regime.summable_dynamicDebtTailAbsorptionCharge_of_cofinal_floor
        tail hbox hedge hcofinal)
  · right
    unfold HasCofinalQuittingPunishmentFloorEndpoints at hcofinal
    push Not at hcofinal
    exact hcofinal

/-- The projectively extracted positive-debt obstruction can be chosen with
the carrier alternative above attached.  Thus a counterexample's optimized
tail has a positive debt owner and either globally summable absorption, or
an eventual coordinatewise failure of individual rationality at every
date. -/
theorem exists_positiveDynamicDebtTail_with_absorptionAlternative
    (regime : QuittingCounterexampleRegime reward) :
    ∃ (limit : ℕ → QuittingDebtPoint ι) (subseq : ℕ → ℕ) (who : ι),
      StrictMono subseq ∧
      Tendsto
        ((fun cutoff ↦ quittingFiniteMinMaxDynamicDebtTail reward cutoff) ∘
          subseq) atTop (nhds limit) ∧
      (∀ time, limit time ∈ quittingDebtBox reward) ∧
      (∀ time, IsQuittingDynamicDebtEdge reward
        (limit time) (limit (time + 1))) ∧
      regime.terminalGap ≤ (limit 0).2 who ∧
      Summable (quittingOpponentClockCharge
        (quittingDynamicDebtTailRoots limit) who) ∧
      (Summable (quittingDynamicDebtTailAbsorptionCharge limit) ∨
        ∃ start, ∀ horizon, start ≤ horizon →
          ∃ player, (limit horizon).1.1 player <
            quittingPunishmentValue reward player) := by
  obtain ⟨limit, subseq, who, hsubseq, hlimit, hbox, hedge,
      hdebt, hclock⟩ := regime.exists_terminalGapDynamicDebtTail
  have halternative :=
    regime.summable_dynamicDebtTailAbsorptionCharge_or_eventually_floorViolation
      limit hbox hedge
  exact ⟨limit, subseq, who, hsubseq, hlimit, hbox, hedge, hdebt, hclock,
    halternative⟩

/-- **Nonpositive-punishment counterexample normal form.**  When the
behavioral punishment vector is coordinatewise nonpositive, the optimized
projective tail inherits individual rationality from its zero-boundary finite
approximants.  The tail/prefix bridge then upgrades the owner's summable
opponent clock to summability of the full joint absorption charge, while
retaining the quantitative terminal-gap lower bound on initial debt. -/
theorem exists_terminalGapDynamicDebtTail_with_summableAbsorption_of_nonpos
    (regime : QuittingCounterexampleRegime reward)
    (hpunishment : ∀ who, quittingPunishmentValue reward who ≤ 0) :
    ∃ (limit : ℕ → QuittingDebtPoint ι) (subseq : ℕ → ℕ) (who : ι),
      StrictMono subseq ∧
      Tendsto
        ((fun cutoff ↦ quittingFiniteMinMaxDynamicDebtTail reward cutoff) ∘
          subseq) atTop (nhds limit) ∧
      (∀ time, limit time ∈ quittingDebtBox reward) ∧
      (∀ time, IsQuittingDynamicDebtEdge reward
        (limit time) (limit (time + 1))) ∧
      regime.terminalGap ≤ (limit 0).2 who ∧
      Summable (quittingOpponentClockCharge
        (quittingDynamicDebtTailRoots limit) who) ∧
      (∀ time player, quittingPunishmentValue reward player ≤
        (limit time).1.1 player) ∧
      Summable (quittingDynamicDebtTailAbsorptionCharge limit) := by
  obtain ⟨limit, subseq, who, hsubseq, hlimit, hbox, hedge,
      hdebt, hclock⟩ := regime.exists_terminalGapDynamicDebtTail
  have hfloor : ∀ time player, quittingPunishmentValue reward player ≤
      (limit time).1.1 player := by
    intro time player
    exact quittingPunishmentValue_le_projectiveDynamicDebtTail_of_nonpos
      reward hpunishment subseq limit hlimit time player
  have hcofinal :
      HasCofinalQuittingPunishmentFloorEndpoints reward limit := by
    intro start
    exact ⟨start, le_rfl, hfloor start⟩
  have hsummable :=
    regime.summable_dynamicDebtTailAbsorptionCharge_of_cofinal_floor
      limit hbox hedge hcofinal
  exact ⟨limit, subseq, who, hsubseq, hlimit, hbox, hedge, hdebt, hclock,
    hfloor, hsummable⟩

end QuittingCounterexampleRegime

end GameTheory
