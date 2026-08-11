/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeStatePreservingChronologyCapacity
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentPacket
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeToggles
import UniformEquilibrium.Quitting.Punishment.BlockerIntervalCover

/-!
# The eventual all-Continue counterexample plateau

The eventual all-Continue branch of an exact dynamic-debt tail contains no
hidden chronological motion.  Two consecutive all-Continue roots force the
entire augmented state -- prescribed value, simplex root, and exact debt --
to be equal.  Hence a tail which is eventually literally all-Continue is
eventually a constant positive-debt phantom boundary, equal to its extracted
value/debt limit.

The constant boundary is not by itself a realized payoff: playing
all-Continue forever delivers zero, while its positive debt records a
profitable solo exit.  What survives as genuine strategic information is a
finite reward-table restriction.  The distinguished debt owner has positive
solo reward at least the counterexample gap.  No stationary solo quitting
rate can be certified, since such a rate would produce a uniform-equilibrium
payoff.  Thus every rate in `(0,1]` has a strict opponent joining obstruction.
For a finite player set these affine obstructions reduce to either one
universal joiner or two distinct opponents whose blocking intervals overlap.

This closes the internal dynamics of the eventual all-Continue branch; it
does not identify the phantom annotation with terminal semantics or rule out
the resulting finite blocker pattern.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-! ## Exact collapse of an all-Continue tail -/

/-- Two consecutive literal all-Continue roots on an exact dynamic-debt tail
force equality of the complete augmented states. -/
theorem quittingDynamicDebtPoint_eq_successor_of_two_allContinue
    (current successor : QuittingDebtPoint ι)
    (hsuccessorDebt : 0 ≤ successor.2)
    (hedge : IsQuittingDynamicDebtEdge reward current successor)
    (hcurrent : quittingRootOfSimplex current.1.2 =
      (quittingAllContinueRoot : ι → PMF Bool))
    (hsuccessor : quittingRootOfSimplex successor.1.2 =
      (quittingAllContinueRoot : ι → PMF Bool)) :
    current = successor := by
  have hzero : quittingRootAbsorptionMass
      (quittingRootOfSimplex current.1.2) = 0 := by
    rw [hcurrent]
    exact quittingRootAbsorptionMass_allContinueRoot
  obtain ⟨hvalue, hdebt, _⟩ :=
    zeroAbsorption_dynamicDebtEdge_plateau
      current successor hsuccessorDebt hedge hzero
  have hroot : current.1.2 = successor.1.2 := by
    funext who
    apply (stdSimplexEquiv (α := Bool)).symm.injective
    exact congrFun (hcurrent.trans hsuccessor.symm) who
  apply Prod.ext
  · exact Prod.ext hvalue hroot
  · exact hdebt

/-- An exact dynamic-debt tail which is literally all-Continue from a
threshold onward is a constant augmented state from that threshold onward. -/
theorem quittingDynamicDebtTail_eq_threshold_of_eventually_allContinue
    (tail : ℕ → QuittingDebtPoint ι)
    (hbox : ∀ time, tail time ∈ quittingDebtBox reward)
    (hedge : ∀ time,
      IsQuittingDynamicDebtEdge reward (tail time) (tail (time + 1)))
    (threshold : ℕ)
    (hroot : ∀ time, threshold ≤ time →
      quittingRootOfSimplex (tail time).1.2 =
        (quittingAllContinueRoot : ι → PMF Bool)) :
    ∀ time, threshold ≤ time → tail time = tail threshold := by
  intro time htime
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le htime
  induction offset with
  | zero => rfl
  | succ offset ih =>
      have hstep : tail (threshold + offset) =
          tail (threshold + offset + 1) :=
        quittingDynamicDebtPoint_eq_successor_of_two_allContinue
          (tail (threshold + offset)) (tail (threshold + offset + 1))
          ((hbox (threshold + offset + 1)).2.1)
          (hedge (threshold + offset))
          (hroot (threshold + offset) (Nat.le_add_right _ _))
          (hroot (threshold + offset + 1) (by omega))
      rw [Nat.add_succ, ← hstep]
      exact ih (Nat.le_add_right _ _)

/-! ## Identification with the extracted phantom boundary -/

namespace QuittingCounterexampleSeamWitness

variable {regime : QuittingCounterexampleRegime reward}

/-- If the optimized tail is eventually all-Continue, it is eventually
exactly its extracted positive-debt boundary state, not merely convergent to
it coordinatewise. -/
theorem tail_eq_limitDebtPoint_of_eventually_allContinue
    (seam : QuittingCounterexampleSeamWitness regime)
    (hplateau : ∃ threshold, ∀ time, threshold ≤ time →
      quittingDynamicDebtTailRoots seam.tail time =
        (quittingAllContinueRoot : ι → PMF Bool)) :
    ∃ threshold, ∀ time, threshold ≤ time →
      seam.tail time =
        (((seam.limit.value, quittingAllContinueSimplexRoot),
          seam.limit.debt) : QuittingDebtPoint ι) := by
  obtain ⟨threshold, hroot⟩ := hplateau
  have hconstant : ∀ time, threshold ≤ time →
      seam.tail time = seam.tail threshold :=
    quittingDynamicDebtTail_eq_threshold_of_eventually_allContinue
      seam.tail seam.tail_mem seam.tail_edge threshold hroot
  have hvalue : (seam.tail threshold).1.1 = seam.limit.value := by
    funext who
    have hconst : Tendsto (fun _ : ℕ ↦
        (seam.tail threshold).1.1 who) atTop
        (nhds ((seam.tail threshold).1.1 who)) := tendsto_const_nhds
    have hevent : (fun time ↦ (seam.tail time).1.1 who) =ᶠ[atTop]
        (fun _ ↦ (seam.tail threshold).1.1 who) := by
      filter_upwards [eventually_ge_atTop threshold] with time htime
      rw [hconstant time htime]
    exact (tendsto_nhds_unique (seam.value_tendsto who)
      (hconst.congr' hevent.symm)).symm
  have hdebt : (seam.tail threshold).2 = seam.limit.debt := by
    funext who
    have hconst : Tendsto (fun _ : ℕ ↦
        (seam.tail threshold).2 who) atTop
        (nhds ((seam.tail threshold).2 who)) := tendsto_const_nhds
    have hevent : (fun time ↦ (seam.tail time).2 who) =ᶠ[atTop]
        (fun _ ↦ (seam.tail threshold).2 who) := by
      filter_upwards [eventually_ge_atTop threshold] with time htime
      rw [hconstant time htime]
    exact (tendsto_nhds_unique (seam.debt_tendsto who)
      (hconst.congr' hevent.symm)).symm
  have hsimplex : (seam.tail threshold).1.2 =
      (quittingAllContinueSimplexRoot : QuittingRootSimplex ι) := by
    funext who
    apply (stdSimplexEquiv (α := Bool)).symm.injective
    exact congrFun (hroot threshold le_rfl |>.trans
      quittingRootOfSimplex_allContinueSimplexRoot.symm) who
  refine ⟨threshold, fun time htime ↦ ?_⟩
  rw [hconstant time htime]
  apply Prod.ext
  · exact Prod.ext hvalue hsimplex
  · exact hdebt

/-- In the eventual all-Continue branch, every sufficiently late start has
literal terminal payoff zero, while its prescribed annotation is exactly the
positive-debt boundary value.  Thus the late semantic discrepancy is the
whole boundary vector, not an asymptotic error term. -/
theorem exists_exact_late_phantomSemantics_of_eventually_allContinue
    (seam : QuittingCounterexampleSeamWitness regime)
    (hplateau : ∃ threshold, ∀ time, threshold ≤ time →
      quittingDynamicDebtTailRoots seam.tail time =
        (quittingAllContinueRoot : ι → PMF Bool)) :
    ∃ threshold, ∀ start, threshold ≤ start → ∀ who,
      quittingRootSequenceTerminalValue reward
          (quittingDynamicDebtTailRoots seam.tail) who start = 0 ∧
        (seam.tail start).1.1 who = seam.limit.value who ∧
        (seam.tail start).1.1 who -
            quittingRootSequenceTerminalValue reward
              (quittingDynamicDebtTailRoots seam.tail) who start =
          seam.limit.value who := by
  obtain ⟨threshold, hstate⟩ :=
    seam.tail_eq_limitDebtPoint_of_eventually_allContinue hplateau
  obtain ⟨rootThreshold, hroot⟩ := hplateau
  refine ⟨max threshold rootThreshold, fun start hstart who ↦ ?_⟩
  have hthreshold : threshold ≤ start :=
    (Nat.le_max_left threshold rootThreshold).trans hstart
  have hrootThreshold : rootThreshold ≤ start :=
    (Nat.le_max_right threshold rootThreshold).trans hstart
  have hterminal : quittingRootSequenceTerminalValue reward
      (quittingDynamicDebtTailRoots seam.tail) who start = 0 :=
    quittingRootSequenceTerminalValue_eq_zero_of_allContinue_from
      reward (quittingDynamicDebtTailRoots seam.tail) who start
        (fun time htime ↦ hroot time (hrootThreshold.trans htime))
  have hvalue : (seam.tail start).1.1 who = seam.limit.value who := by
    have := congrArg (fun point : QuittingDebtPoint ι ↦ point.1.1 who)
      (hstate start hthreshold)
    exact this
  exact ⟨hterminal, hvalue, by rw [hterminal, sub_zero, hvalue]⟩

/-! ## Finite strategic residue of the positive-debt owner -/

/-- The selected positive-debt owner carries the counterexample gap through
debt and solo reward into the phantom prescribed value. -/
theorem terminalGap_le_limitDebt_le_soloReward_le_limitValue
    (seam : QuittingCounterexampleSeamWitness regime) :
    regime.terminalGap ≤ seam.limit.debt seam.limit.owner ∧
      seam.limit.debt seam.limit.owner ≤
        quittingSoloReward reward seam.limit.owner seam.limit.owner ∧
      quittingSoloReward reward seam.limit.owner seam.limit.owner ≤
        seam.limit.value seam.limit.owner := by
  refine ⟨seam.terminalGap_le_limitDebt, ?_, ?_⟩
  · simpa [quittingSoloReward, quittingSingletonTerminal] using
      seam.limit.debt_le_soloReward_of_debt_pos seam.limit.owner
        seam.limit.ownerDebt_pos
  · simpa [quittingSoloReward, quittingSingletonTerminal] using
      seam.limit.soloReward_le_value seam.limit.owner

/-- No positive stationary solo rate of the selected debt owner can satisfy
all inactive-player inequalities in a counterexample.  Otherwise the
positive solo payoff would be a uniform-equilibrium payoff. -/
theorem limitOwner_forall_quittingSoloJoiningObstruction
    (seam : QuittingCounterexampleSeamWitness regime) :
    ∀ p : ℝ, 0 < p → p ≤ 1 →
      QuittingSoloJoiningObstruction reward seam.limit.owner p := by
  have hsolo : 0 <
      quittingSoloReward reward seam.limit.owner seam.limit.owner :=
    regime.terminalGap_pos.trans_le
      (seam.terminalGap_le_limitDebt_le_soloReward_le_limitValue.1.trans
        seam.terminalGap_le_limitDebt_le_soloReward_le_limitValue.2.1)
  rcases soloCertification_or_universalJoining reward seam.limit.owner with
    ⟨p, hp0, hp1, hinactive⟩ | hobstruction
  · have huniform := isUniformEquilibriumPayoff_soloReward_of_inactive
      reward seam.limit.owner (quittingHazardCoin p hp0.le hp1)
        (by simpa using hp0) hsolo.le (by
          intro other hother
          rw [quittingHazardCoin_true_toReal,
            quittingHazardCoin_false_toReal]
          exact hinactive other hother)
    exact (regime.not_exists_uniformEquilibriumPayoff
      ⟨quittingSoloReward reward seam.limit.owner, huniform⟩).elim
  · exact hobstruction

/-- Expanded search-facing form: every owner rate has some strict opponent
whose mixture of preemption and collision beats waiting for the owner's solo
exit. -/
theorem limitOwner_forall_exists_strictJoiningOpponent
    (seam : QuittingCounterexampleSeamWitness regime) :
    ∀ p : ℝ, 0 < p → p ≤ 1 →
      ∃ other, other ≠ seam.limit.owner ∧
        quittingSoloReward reward seam.limit.owner other <
          (1 - p) * quittingSoloReward reward other other +
            p * quittingSingletonCollisionReward reward
              seam.limit.owner other :=
  seam.limitOwner_forall_quittingSoloJoiningObstruction

/-- Every positive owner rate has a literal positive inactive-coordinate
endpoint difference at the corresponding solo row.  The blocker condition
therefore certifies failure of singleton-support exact Nash, rather than an
exact return row. -/
theorem limitOwner_exists_positiveEndpointDifference_at_soloRate
    (seam : QuittingCounterexampleSeamWitness regime)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ∃ other, other ≠ seam.limit.owner ∧
      0 < quittingRootEndpointDifference reward
        (quittingSoloReward reward seam.limit.owner)
        (quittingSoloStationaryRoot seam.limit.owner
          (quittingHazardCoin p hp0.le hp1)) other := by
  obtain ⟨other, hother, hjoining⟩ :=
    seam.limitOwner_forall_exists_strictJoiningOpponent p hp0 hp1
  refine ⟨other, hother, ?_⟩
  rw [quittingRootEndpointDifference_soloStationaryRoot_other
      reward hother,
    quittingHazardCoin_true_toReal, quittingHazardCoin_false_toReal]
  linarith

/-- Consequently no literal singleton-support row owned by the positive-debt
player is exact endpoint Nash against the owner's singleton payoff vector. -/
theorem limitOwner_soloRate_not_endpointNash
    (seam : QuittingCounterexampleSeamWitness regime)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ¬ IsεQuittingRootEndpointNash reward
      (quittingSoloReward reward seam.limit.owner) 0
      (quittingSoloStationaryRoot seam.limit.owner
        (quittingHazardCoin p hp0.le hp1)) := by
  intro hnash
  have hinactive :=
    (isεQuittingRootEndpointNash_soloStationaryRoot_iff reward
      seam.limit.owner (quittingHazardCoin p hp0.le hp1)).1 hnash
  obtain ⟨other, hother, hjoining⟩ :=
    seam.limitOwner_forall_exists_strictJoiningOpponent p hp0 hp1
  have hle := hinactive other hother
  rw [quittingHazardCoin_true_toReal,
    quittingHazardCoin_false_toReal] at hle
  linarith

/-- **Support-enlargement bridge.**  Any exact endpoint-Nash root against the
positive-debt owner's singleton payoff which gives that owner positive quit
probability must also give positive quit probability to some distinct
opponent.  The blocker classification thus forces multi-owner support, but
does not choose the additional rate or establish Bellman return. -/
theorem limitOwner_endpointNash_requires_second_quitter
    (seam : QuittingCounterexampleSeamWitness regime)
    (root : ι → PMF Bool)
    (howner : 0 < (root seam.limit.owner true).toReal)
    (hnash : IsεQuittingRootEndpointNash reward
      (quittingSoloReward reward seam.limit.owner) 0 root) :
    ∃ other, other ≠ seam.limit.owner ∧
      0 < (root other true).toReal := by
  by_contra hnot
  push Not at hnot
  have hothers : ∀ other, other ≠ seam.limit.owner →
      root other = PMF.pure false := by
    intro other hother
    apply pmf_eq_pure_false_of_apply_true_toReal_eq_zero
    exact le_antisymm (hnot other hother) ENNReal.toReal_nonneg
  have hroot : root = quittingSoloStationaryRoot seam.limit.owner
      (root seam.limit.owner) :=
    eq_quittingSoloStationaryRoot_of_others_continue hothers
  have hownerLe : (root seam.limit.owner true).toReal ≤ 1 := by
    have hsum := quittingRoot_continueProbability_add_quitProbability
      root seam.limit.owner
    have hcontinueNonneg : 0 ≤
        (root seam.limit.owner false).toReal := ENNReal.toReal_nonneg
    linarith
  rw [hroot] at hnash
  obtain ⟨other, hother, hjoining⟩ :=
    seam.limitOwner_forall_exists_strictJoiningOpponent
      (root seam.limit.owner true).toReal howner hownerLe
  have hinactive :=
    (isεQuittingRootEndpointNash_soloStationaryRoot_iff reward
      seam.limit.owner (root seam.limit.owner)).1 hnash
  have hle := hinactive other hother
  have hsum := quittingRoot_continueProbability_add_quitProbability
    root seam.limit.owner
  have hfalse : (root seam.limit.owner false).toReal =
      1 - (root seam.limit.owner true).toReal := by linarith
  rw [hfalse] at hle
  linarith

/-- At the sure-solo endpoint, the counterexample gap forces a distinct
opponent to gain the full gap by joining the positive-debt owner. -/
theorem exists_limitOwner_collisionGain
    (seam : QuittingCounterexampleSeamWitness regime) :
    ∃ other, other ≠ seam.limit.owner ∧
      quittingSoloReward reward seam.limit.owner other + regime.terminalGap ≤
        quittingSingletonCollisionReward reward seam.limit.owner other := by
  have hsolo : -regime.terminalGap <
      quittingSoloReward reward seam.limit.owner seam.limit.owner := by
    have hgap :=
      seam.terminalGap_le_limitDebt_le_soloReward_le_limitValue.1.trans
        seam.terminalGap_le_limitDebt_le_soloReward_le_limitValue.2.1
    linarith [regime.terminalGap_pos]
  exact regime.exists_collision_gain hsolo

/-- The complete affine blocker classification for the positive-debt owner:
either one opponent blocks every solo rate, or two distinct opponents cover
the rate interval with overlapping initial and terminal blocking segments. -/
theorem limitOwner_exists_universalJoiner_or_switchingPair
    (seam : QuittingCounterexampleSeamWitness regime) :
    (∃ other, other ≠ seam.limit.owner ∧
        quittingSoloReward reward seam.limit.owner other ≤
            quittingSoloReward reward other other ∧
          quittingSoloReward reward seam.limit.owner other <
            quittingSingletonCollisionReward reward seam.limit.owner other) ∨
      ∃ a, a ≠ seam.limit.owner ∧
        ∃ b, b ≠ seam.limit.owner ∧ a ≠ b ∧
          ∃ α β : ℝ, 0 < β ∧ β < α ∧ α ≤ 1 ∧
            IsInitialRateBlocker
              (quittingJoiningGain reward seam.limit.owner a) α ∧
            IsTerminalRateBlocker
              (quittingJoiningGain reward seam.limit.owner b) β :=
  exists_universalJoiner_or_switchingPair_of_universalJoining
    reward seam.limit.owner
      seam.limitOwner_forall_quittingSoloJoiningObstruction

end QuittingCounterexampleSeamWitness

end GameTheory
