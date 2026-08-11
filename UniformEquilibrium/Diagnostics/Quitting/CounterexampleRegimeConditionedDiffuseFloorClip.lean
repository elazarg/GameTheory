/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeConditionedDiffuseReset
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeToggles
import UniformEquilibrium.Quitting.Boundary.Repair.FixedTailUniformAbsorption

/-!
# Punishment-floor clipping of diffuse reset targets

The fixed outsider in a diffuse counterexample seam has conditioned value
uniformly below its singleton reward.  Clipping every coordinate of that
conditioned target upward to its punishment value preserves a uniform
singleton gap whenever the outsider's punishment value is strictly below its
singleton reward.  Fixed-tail Nash existence then supplies a
positive-absorption exact endpoint root against the clipped, floor-admissible
target.

Thus the viability issue has a scalar alternative: either floor-admissible
positive-absorption reset roots occur cofinally, or the fixed outsider's
singleton reward is no larger than its punishment value.  The roots remain
fixed-target objects; no Bellman predecessor match or chronological splice is
asserted.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {regime : QuittingCounterexampleRegime reward}

/-- Coordinatewise clipping of a target at the behavioral punishment floor. -/
def quittingPunishmentFloorClip
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι) : Payoff ι :=
  fun who => max (quittingPunishmentValue reward who) (target who)

@[simp] theorem quittingPunishmentFloorClip_apply
    (target : Payoff ι) (who : ι) :
    quittingPunishmentFloorClip reward target who =
      max (quittingPunishmentValue reward who) (target who) := rfl

/-- The clipped target dominates every punishment coordinate. -/
theorem punishmentValue_le_quittingPunishmentFloorClip
    (target : Payoff ι) (who : ι) :
    quittingPunishmentValue reward who ≤
      quittingPunishmentFloorClip reward target who := by
  exact le_max_left _ _

/-- A strict punishment-to-singleton gap and a uniform target deficit leave a
strict uniform gap after floor clipping. -/
theorem exists_pos_gap_quittingPunishmentFloorClip_le_singleton_sub
    (target : Payoff ι) (who : ι) (eta : ℝ)
    (heta : 0 < eta)
    (htarget : target who ≤
      reward (quittingSingletonTerminal who) who - eta)
    (hpunishment : quittingPunishmentValue reward who <
      reward (quittingSingletonTerminal who) who) :
    ∃ gap : ℝ, 0 < gap ∧
      quittingPunishmentFloorClip reward target who ≤
        reward (quittingSingletonTerminal who) who - gap := by
  let solo := reward (quittingSingletonTerminal who) who
  let floor := quittingPunishmentValue reward who
  let gap := min eta ((solo - floor) / 2)
  have hgap : 0 < gap := by
    exact lt_min heta (half_pos (sub_pos.mpr hpunishment))
  have hgapEta : gap ≤ eta := min_le_left _ _
  have hgapSlack : gap ≤ (solo - floor) / 2 := min_le_right _ _
  have htarget' : target who ≤ solo - gap := by
    dsimp only [solo]
    linarith
  have hfloor' : floor ≤ solo - gap := by
    linarith
  exact ⟨gap, hgap, by
    rw [quittingPunishmentFloorClip_apply, max_le_iff]
    exact ⟨hfloor', htarget'⟩⟩

/-- If a singleton reward fails to strictly dominate its punishment value,
then either the singleton reward is negative or the two values coincide. -/
theorem singletonReward_neg_or_punishmentValue_eq_of_singleton_le
    (who : ι)
    (hreverse : reward (quittingSingletonTerminal who) who ≤
      quittingPunishmentValue reward who) :
    reward (quittingSingletonTerminal who) who < 0 ∨
      quittingPunishmentValue reward who =
        reward (quittingSingletonTerminal who) who := by
  by_cases hsolo : reward (quittingSingletonTerminal who) who < 0
  · exact Or.inl hsolo
  · right
    have hsoloNonneg : 0 ≤ reward (quittingSingletonTerminal who) who :=
      le_of_not_gt hsolo
    have hupper := quittingPunishmentValue_le_max_solo reward who
    rw [QuittingSureSetOwnerRepair.quittingSetReward_of_nonempty reward
      (Finset.singleton_nonempty who) who] at hupper
    change quittingPunishmentValue reward who ≤
      max (reward (quittingSingletonTerminal who) who) 0 at hupper
    rw [max_eq_left hsoloNonneg] at hupper
    exact le_antisymm hupper hreverse

namespace QuittingCounterexampleSeamWitness

/-- The diffuse reset viability fork expressed by one scalar sign.

If the fixed outsider's singleton reward strictly dominates its punishment
value, coordinatewise clipping produces cofinally many floor-admissible
targets with a uniform singleton gap and a positive-absorption exact
endpoint-Nash root.  Otherwise that outsider itself satisfies the opposite
punishment/singleton inequality. -/
theorem exists_fixedOutsider_punishment_ge_singleton_or_cofinal_floorClippedReset
    (seam : QuittingCounterexampleSeamWitness regime)
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption
      (quittingDynamicDebtTailRoots seam.tail) time)
    (hmesh : Tendsto (quittingTailConditionedAbsorptionWeight
      (quittingDynamicDebtTailRoots seam.tail)) atTop (nhds 0)) :
    ∃ who : ι,
      reward (quittingSingletonTerminal who) who ≤
          quittingPunishmentValue reward who ∨
        ∃ gap : ℝ, 0 < gap ∧ ∀ start, ∃ time,
          ∃ root : QuittingRootSimplex ι,
            start ≤ time ∧
            quittingDynamicDebtTailRoots seam.tail time who = PMF.pure false ∧
            (∀ player, quittingPunishmentValue reward player ≤
              quittingPunishmentFloorClip reward
                (quittingTailConditionedValue
                  (quittingDynamicDebtTailRoots seam.tail)
                  (fun date => (seam.tail date).1.1)
                  seam.limit.value time) player) ∧
            quittingPunishmentFloorClip reward
                (quittingTailConditionedValue
                  (quittingDynamicDebtTailRoots seam.tail)
                  (fun date => (seam.tail date).1.1)
                  seam.limit.value time) who ≤
              reward (quittingSingletonTerminal who) who - gap ∧
            IsεQuittingRootEndpointNash reward
              (quittingPunishmentFloorClip reward
                (quittingTailConditionedValue
                  (quittingDynamicDebtTailRoots seam.tail)
                  (fun date => (seam.tail date).1.1)
                  seam.limit.value time))
              0 (quittingRootOfSimplex root) ∧
            (∀ player, quittingPunishmentValue reward player ≤
              quittingRootSuccessorPayoff reward
                (quittingPunishmentFloorClip reward
                  (quittingTailConditionedValue
                    (quittingDynamicDebtTailRoots seam.tail)
                    (fun date => (seam.tail date).1.1)
                    seam.limit.value time))
                (quittingRootOfSimplex root) player) ∧
            IsQuittingNashBellmanEdge reward
              (quittingRootSuccessorPayoff reward
                  (quittingPunishmentFloorClip reward
                    (quittingTailConditionedValue
                      (quittingDynamicDebtTailRoots seam.tail)
                      (fun date => (seam.tail date).1.1)
                      seam.limit.value time))
                  (quittingRootOfSimplex root), root)
              (quittingPunishmentFloorClip reward
                  (quittingTailConditionedValue
                    (quittingDynamicDebtTailRoots seam.tail)
                    (fun date => (seam.tail date).1.1)
                    seam.limit.value time),
                quittingAllContinueSimplexRoot) ∧
            gap / (gap + 2 * quittingRewardBound reward) ≤
              quittingRootAbsorptionMass (quittingRootOfSimplex root) ∧
            0 < quittingRootAbsorptionMass (quittingRootOfSimplex root) := by
  obtain ⟨who, eta, heta, hdates⟩ :=
    seam.exists_fixed_inactive_rescaledQuitDefect_of_diffuse hpositive hmesh
  by_cases hpunishment : quittingPunishmentValue reward who <
      reward (quittingSingletonTerminal who) who
  · let gap := min eta
      ((reward (quittingSingletonTerminal who) who -
        quittingPunishmentValue reward who) / 2)
    have hgap : 0 < gap :=
      lt_min heta (half_pos (sub_pos.mpr hpunishment))
    refine ⟨who, Or.inr ⟨gap, hgap, ?_⟩⟩
    intro start
    obtain ⟨time, htime, hinactive, _, htarget⟩ := hdates start
    let target : Payoff ι := quittingTailConditionedValue
      (quittingDynamicDebtTailRoots seam.tail)
      (fun date => (seam.tail date).1.1) seam.limit.value time
    let clipped := quittingPunishmentFloorClip reward target
    have hclipped : clipped who ≤
        reward (quittingSingletonTerminal who) who - gap := by
      have hgapEta : gap ≤ eta := min_le_left _ _
      have hgapSlack : gap ≤
          (reward (quittingSingletonTerminal who) who -
            quittingPunishmentValue reward who) / 2 := min_le_right _ _
      rw [show clipped who = max (quittingPunishmentValue reward who)
          (target who) by rfl, max_le_iff]
      constructor
      · linarith
      · dsimp only [target]
        linarith
    obtain ⟨root, hnash, habsorption⟩ :=
      exists_isZeroQuittingRootEndpointNash_simplex_with_positive_absorption_of_singleton_gap
        reward clipped who (by linarith)
    have hnashRoot : IsεQuittingRootNash reward clipped 0
        (quittingRootOfSimplex root) :=
      (isεQuittingRootEndpointNash_iff_isεQuittingRootNash
        reward clipped 0 (quittingRootOfSimplex root)).mp hnash
    have hpredecessorFloor : ∀ player,
        quittingPunishmentValue reward player ≤
          quittingRootSuccessorPayoff reward clipped
            (quittingRootOfSimplex root) player := by
      intro player
      exact quittingPunishmentValue_le_rootSuccessorPayoff_of_tail_ge
        reward clipped (quittingRootOfSimplex root) player
        (punishmentValue_le_quittingPunishmentFloorClip
          (reward := reward) target player) hnashRoot
    have hexactEdge : IsQuittingNashBellmanEdge reward
        (quittingRootSuccessorPayoff reward clipped
            (quittingRootOfSimplex root), root)
        (clipped, quittingAllContinueSimplexRoot) := by
      exact ⟨rfl, hnash⟩
    have huniformCharge : gap / (gap + 2 * quittingRewardBound reward) ≤
        quittingRootAbsorptionMass (quittingRootOfSimplex root) := by
      exact gap_div_le_quittingRootAbsorptionMass_of_isZeroEndpointNash
        reward clipped (quittingRootOfSimplex root) who
        (quittingRewardBound_nonneg reward) hgap
        (abs_reward_le_quittingRewardBound reward) hclipped hnash
    exact ⟨time, root, htime, hinactive,
      fun player => punishmentValue_le_quittingPunishmentFloorClip
        (reward := reward) target player,
      hclipped, hnash, hpredecessorFloor, hexactEdge,
      huniformCharge, habsorption⟩
  · exact ⟨who, Or.inl (le_of_not_gt hpunishment)⟩

/-! ## Global positive-solo compatibility -/

/-- A diffuse seam has a positive singleton owner somewhere in the game.  At
the selected fixed outsider, the scalar floor fork is therefore sharpened to
one of three alternatives: a distinct negative singleton, punishment
equality, or the cofinal floor-clipped reset family.

The distinctness in the negative branch is substantive: the positive-solo
toggle cannot be the same coordinate as a negative singleton.  This is a
search-facing form of the scalar residual; it does not assert that the
positive owner and negative outsider can be chronologically matched. -/
theorem exists_positiveSolo_owner_and_scalar_diffuse_alternative
    (seam : QuittingCounterexampleSeamWitness regime)
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption
      (quittingDynamicDebtTailRoots seam.tail) time)
    (hmesh : Tendsto (quittingTailConditionedAbsorptionWeight
      (quittingDynamicDebtTailRoots seam.tail)) atTop (nhds 0)) :
    ∃ owner who : ι,
      regime.terminalGap ≤ quittingSoloReward reward owner owner ∧
      ((who ≠ owner ∧ quittingSoloReward reward who who < 0) ∨
        quittingPunishmentValue reward who = quittingSoloReward reward who who ∨
        (∃ gap : ℝ, 0 < gap ∧ ∀ start, ∃ time,
          ∃ root : QuittingRootSimplex ι,
            start ≤ time ∧
            quittingDynamicDebtTailRoots seam.tail time who = PMF.pure false ∧
            (∀ player, quittingPunishmentValue reward player ≤
              quittingPunishmentFloorClip reward
                (quittingTailConditionedValue
                  (quittingDynamicDebtTailRoots seam.tail)
                  (fun date => (seam.tail date).1.1)
                  seam.limit.value time) player) ∧
            quittingPunishmentFloorClip reward
                (quittingTailConditionedValue
                  (quittingDynamicDebtTailRoots seam.tail)
                  (fun date => (seam.tail date).1.1)
                  seam.limit.value time) who ≤
              reward (quittingSingletonTerminal who) who - gap ∧
            IsεQuittingRootEndpointNash reward
              (quittingPunishmentFloorClip reward
                (quittingTailConditionedValue
                  (quittingDynamicDebtTailRoots seam.tail)
                  (fun date => (seam.tail date).1.1)
                  seam.limit.value time))
              0 (quittingRootOfSimplex root) ∧
            (∀ player, quittingPunishmentValue reward player ≤
              quittingRootSuccessorPayoff reward
                (quittingPunishmentFloorClip reward
                  (quittingTailConditionedValue
                    (quittingDynamicDebtTailRoots seam.tail)
                    (fun date => (seam.tail date).1.1)
                    seam.limit.value time))
                (quittingRootOfSimplex root) player) ∧
            IsQuittingNashBellmanEdge reward
              (quittingRootSuccessorPayoff reward
                  (quittingPunishmentFloorClip reward
                    (quittingTailConditionedValue
                      (quittingDynamicDebtTailRoots seam.tail)
                      (fun date => (seam.tail date).1.1)
                      seam.limit.value time))
                  (quittingRootOfSimplex root), root)
              (quittingPunishmentFloorClip reward
                  (quittingTailConditionedValue
                    (quittingDynamicDebtTailRoots seam.tail)
                    (fun date => (seam.tail date).1.1)
                    seam.limit.value time),
                quittingAllContinueSimplexRoot) ∧
            gap / (gap + 2 * quittingRewardBound reward) ≤
              quittingRootAbsorptionMass (quittingRootOfSimplex root) ∧
            0 < quittingRootAbsorptionMass (quittingRootOfSimplex root))) := by
  obtain ⟨owner, howner⟩ := regime.exists_terminalGap_le_soloReward
  obtain ⟨who, hscalar⟩ :=
    seam.exists_fixedOutsider_punishment_ge_singleton_or_cofinal_floorClippedReset
      hpositive hmesh
  refine ⟨owner, who, howner, ?_⟩
  rcases hscalar with hreverse | hreset
  · rcases singletonReward_neg_or_punishmentValue_eq_of_singleton_le
      (reward := reward) who hreverse with hnegative | heq
    · left
      constructor
      · intro hsame
        subst who
        have howner' : regime.terminalGap ≤
            reward (quittingSingletonTerminal owner) owner := by
          simpa [quittingSoloReward, quittingSingletonTerminal] using howner
        linarith [regime.terminalGap_pos, howner']
      · exact hnegative
    · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hreset)

end QuittingCounterexampleSeamWitness

end GameTheory
