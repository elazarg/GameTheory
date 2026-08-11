/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticRareHazardPunishmentScalingRegression
import UniformEquilibrium.Quitting.Cycles.PhaseSwitchProfile

/-!
# Nonstationary product phases cannot diffuse collision punishment

The collision-punishment regression is not a peculiarity of stationary
coordinatewise scaling.  In the same three-player reward table, let the owner
Continue while the two opponents use arbitrary time-dependent independent
Quit probabilities `p_t` and `q_t`.  Put

`a_t = p_t + q_t - p_t q_t`

for the stage absorption probability and `k_t = p_t q_t` for the collision
probability.  If `a_t <= eta`, then

`k_t <= eta * a_t`.

After weighting by live survival and summing over any finite window, total
collision mass is therefore at most `eta` times total absorbed mass.  The
owner's Never payoff is singleton mass minus collision mass, hence exactly
absorbed mass minus twice collision mass.  It is at least

`(1 - 2 * eta) * absorbedMass`.

Thus deterministic calendars and arbitrary nonstationary product rows do not
repair the rare-scaling failure.  A completely absorbing phase with vanishing
mesh gives the owner payoff tending to `1`, not the punishment value `-1`.
Any near-optimal implementation must retain a macroscopic absorption atom or
leave macroscopic survival for a later tail.  Since Never is itself a legal
behavioral deviation, this already fences arbitrary stopping-time compilers;
no restriction to stationary deviations is used.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.PMFProduct

namespace QuittingNonstationaryCollisionPunishmentNoGo

abbrev Player := QuittingRareHazardPunishmentScalingRegression.Player
abbrev owner : Player := QuittingRareHazardPunishmentScalingRegression.owner
abbrev left : Player := QuittingRareHazardPunishmentScalingRegression.left
abbrev right : Player := QuittingRareHazardPunishmentScalingRegression.right

abbrev reward := QuittingRareHazardPunishmentScalingRegression.reward

/-- A legal nonstationary product plan: the owner always Continues and the
two opponents use arbitrary Boolean marginals at every live date. -/
def collisionPhaseRoots (leftPlan rightPlan : ℕ → PMF Bool) :
    ℕ → Player → PMF Bool :=
  fun time who =>
    if who = left then leftPlan time
    else if who = right then rightPlan time
    else PMF.pure false

/-- Left opponent Quit probability at a live date. -/
def leftHazard (leftPlan : ℕ → PMF Bool) (time : ℕ) : ℝ :=
  (leftPlan time true).toReal

/-- Right opponent Quit probability at a live date. -/
def rightHazard (rightPlan : ℕ → PMF Bool) (time : ℕ) : ℝ :=
  (rightPlan time true).toReal

/-- Probability that at least one opponent Quits at the date. -/
def stageAbsorption (leftPlan rightPlan : ℕ → PMF Bool) (time : ℕ) : ℝ :=
  leftHazard leftPlan time + rightHazard rightPlan time -
    leftHazard leftPlan time * rightHazard rightPlan time

/-- Probability that both opponents Quit at the date. -/
def stageCollision (leftPlan rightPlan : ℕ → PMF Bool) (time : ℕ) : ℝ :=
  leftHazard leftPlan time * rightHazard rightPlan time

theorem leftHazard_nonneg (leftPlan : ℕ → PMF Bool) (time : ℕ) :
    0 ≤ leftHazard leftPlan time :=
  ENNReal.toReal_nonneg

theorem rightHazard_nonneg (rightPlan : ℕ → PMF Bool) (time : ℕ) :
    0 ≤ rightHazard rightPlan time :=
  ENNReal.toReal_nonneg

theorem leftHazard_le_one (leftPlan : ℕ → PMF Bool) (time : ℕ) :
    leftHazard leftPlan time ≤ 1 := by
  unfold leftHazard
  exact (ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _)).trans_eq
    (by norm_num)

theorem rightHazard_le_one (rightPlan : ℕ → PMF Bool) (time : ℕ) :
    rightHazard rightPlan time ≤ 1 := by
  unfold rightHazard
  exact (ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _)).trans_eq
    (by norm_num)

theorem reward_abs_le_one (terminal player) :
    |reward terminal player| ≤ (1 : ℝ) := by
  simp [QuittingRareHazardPunishmentScalingRegression.reward]
  split_ifs <;> norm_num

theorem stageAbsorption_nonneg
    (leftPlan rightPlan : ℕ → PMF Bool) (time : ℕ) :
    0 ≤ stageAbsorption leftPlan rightPlan time := by
  have hp0 := leftHazard_nonneg leftPlan time
  have hp1 := leftHazard_le_one leftPlan time
  have hq0 := rightHazard_nonneg rightPlan time
  have hq1 := rightHazard_le_one rightPlan time
  unfold stageAbsorption
  nlinarith [mul_nonneg (sub_nonneg.mpr hp1) hq0]

theorem leftHazard_le_stageAbsorption
    (leftPlan rightPlan : ℕ → PMF Bool) (time : ℕ) :
    leftHazard leftPlan time ≤ stageAbsorption leftPlan rightPlan time := by
  have hp1 := leftHazard_le_one leftPlan time
  have hq0 := rightHazard_nonneg rightPlan time
  unfold stageAbsorption
  nlinarith [mul_nonneg (sub_nonneg.mpr hp1) hq0]

theorem rightHazard_le_stageAbsorption
    (leftPlan rightPlan : ℕ → PMF Bool) (time : ℕ) :
    rightHazard rightPlan time ≤ stageAbsorption leftPlan rightPlan time := by
  have hp0 := leftHazard_nonneg leftPlan time
  have hq1 := rightHazard_le_one rightPlan time
  unfold stageAbsorption
  nlinarith [mul_nonneg hp0 (sub_nonneg.mpr hq1)]

/-- Pointwise collision is at most mesh times absorption. -/
theorem stageCollision_le_mesh_mul_stageAbsorption
    (leftPlan rightPlan : ℕ → PMF Bool) (time : ℕ) {mesh : ℝ}
    (hmesh0 : 0 ≤ mesh)
    (hmesh : stageAbsorption leftPlan rightPlan time ≤ mesh) :
    stageCollision leftPlan rightPlan time ≤
      mesh * stageAbsorption leftPlan rightPlan time := by
  have hp0 := leftHazard_nonneg leftPlan time
  have hpAbs := leftHazard_le_stageAbsorption leftPlan rightPlan time
  have hqMesh :=
    (rightHazard_le_stageAbsorption leftPlan rightPlan time).trans hmesh
  unfold stageCollision
  calc
    leftHazard leftPlan time * rightHazard rightPlan time ≤
        leftHazard leftPlan time * mesh :=
      mul_le_mul_of_nonneg_left hqMesh hp0
    _ ≤ stageAbsorption leftPlan rightPlan time * mesh :=
      mul_le_mul_of_nonneg_right hpAbs hmesh0
    _ = mesh * stageAbsorption leftPlan rightPlan time := by ring

theorem collisionPhaseRoots_continueMass
    (leftPlan rightPlan : ℕ → PMF Bool) (time : ℕ) :
    quittingStationaryContinueMass
        (collisionPhaseRoots leftPlan rightPlan time) =
      1 - stageAbsorption leftPlan rightPlan time := by
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  rw [show (Finset.univ : Finset Player) = {owner, left, right} by decide]
  simp [collisionPhaseRoots, stageAbsorption, leftHazard, rightHazard,
    Math.PMFProduct.pmfBool_false_toReal, owner, left, right]
  ring

/-- At each date the owner's Never absorbing contribution is absorption
minus twice collision. -/
theorem collisionPhaseRoots_owner_absorbingContribution
    (leftPlan rightPlan : ℕ → PMF Bool) (time : ℕ) :
    quittingRootAbsorbingContribution reward
        (collisionPhaseRoots leftPlan rightPlan time) owner =
      stageAbsorption leftPlan rightPlan time -
        2 * stageCollision leftPlan rightPlan time := by
  unfold quittingRootAbsorbingContribution quittingRootExpectedPayoff
  rw [QuittingFixedTableDiffuseIncidenceRegression.expect_pmfPi_fin3]
  simp [expect_eq_sum, quittingRootPayoff,
    QuittingRareHazardPunishmentScalingRegression.reward,
    collisionPhaseRoots, stageAbsorption, stageCollision,
    leftHazard, rightHazard, Math.PMFProduct.pmfBool_false_toReal,
    owner, left, right]
  ring

/-- Exact finite-window collision charge. -/
def finiteCollisionCharge (leftPlan rightPlan : ℕ → PMF Bool)
    (cutoff : ℕ) : ℝ :=
  ∑ time ∈ Finset.range cutoff,
    quittingJointSurvivalWeight
        (collisionPhaseRoots leftPlan rightPlan) 0 time *
      stageCollision leftPlan rightPlan time

/-- Arbitrary time variation does not evade the collision-order loss: total
collision charge is at most mesh times total absorbed mass. -/
theorem finiteCollisionCharge_le_mesh_mul_absorbedMass
    (leftPlan rightPlan : ℕ → PMF Bool) (cutoff : ℕ) {mesh : ℝ}
    (hmesh0 : 0 ≤ mesh)
    (hmesh : ∀ time < cutoff,
      stageAbsorption leftPlan rightPlan time ≤ mesh) :
    finiteCollisionCharge leftPlan rightPlan cutoff ≤
      mesh * (1 - quittingJointSurvivalWeight
        (collisionPhaseRoots leftPlan rightPlan) 0 cutoff) := by
  unfold finiteCollisionCharge
  calc
    (∑ time ∈ Finset.range cutoff,
        quittingJointSurvivalWeight
            (collisionPhaseRoots leftPlan rightPlan) 0 time *
          stageCollision leftPlan rightPlan time) ≤
      ∑ time ∈ Finset.range cutoff,
        quittingJointSurvivalWeight
            (collisionPhaseRoots leftPlan rightPlan) 0 time *
          (mesh * stageAbsorption leftPlan rightPlan time) := by
        apply Finset.sum_le_sum
        intro time htime
        exact mul_le_mul_of_nonneg_left
          (stageCollision_le_mesh_mul_stageAbsorption leftPlan rightPlan time
            hmesh0 (hmesh time (Finset.mem_range.mp htime)))
          (quittingJointSurvivalWeight_nonneg _ 0 time)
    _ = mesh * ∑ time ∈ Finset.range cutoff,
        quittingJointSurvivalWeight
            (collisionPhaseRoots leftPlan rightPlan) 0 time *
          (1 - quittingStationaryContinueMass
            (collisionPhaseRoots leftPlan rightPlan time)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro time _
        rw [collisionPhaseRoots_continueMass]
        ring_nf
    _ = mesh * (1 - quittingJointSurvivalWeight
          (collisionPhaseRoots leftPlan rightPlan) 0 cutoff) := by
        congr 1
        simpa only [Nat.zero_add] using
          sum_quittingJointSurvivalWeight_mul_one_sub_continueMass
            (collisionPhaseRoots leftPlan rightPlan) 0 cutoff

/-- **Nonstationary rare-punishment no-go.**  The payoff of the legal Never
plan through an arbitrary finite product phase is bounded below by
`(1 - 2*mesh)` times the phase's absorbed mass. -/
theorem truncated_ownerNeverValue_ge_one_sub_two_mul_mesh
    (leftPlan rightPlan : ℕ → PMF Bool) (cutoff : ℕ) {mesh : ℝ}
    (hmesh0 : 0 ≤ mesh)
    (hmesh : ∀ time < cutoff,
      stageAbsorption leftPlan rightPlan time ≤ mesh) :
    (1 - 2 * mesh) *
        (1 - quittingJointSurvivalWeight
          (collisionPhaseRoots leftPlan rightPlan) 0 cutoff) ≤
      quittingRootSequenceTerminalValue reward
        (quittingTruncatedRoots
          (collisionPhaseRoots leftPlan rightPlan) cutoff) owner 0 := by
  rw [quittingRootSequenceTerminalValue_quittingTruncatedRoots_eq_sum]
  calc
    (1 - 2 * mesh) *
        (1 - quittingJointSurvivalWeight
          (collisionPhaseRoots leftPlan rightPlan) 0 cutoff) =
      ∑ time ∈ Finset.range cutoff,
        quittingJointSurvivalWeight
            (collisionPhaseRoots leftPlan rightPlan) 0 time *
          ((1 - 2 * mesh) *
            stageAbsorption leftPlan rightPlan time) := by
        rw [← sum_quittingJointSurvivalWeight_mul_one_sub_continueMass]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro time _
        rw [collisionPhaseRoots_continueMass]
        ring_nf
    _ ≤ ∑ time ∈ Finset.range cutoff,
        quittingJointSurvivalWeight
            (collisionPhaseRoots leftPlan rightPlan) 0 time *
          quittingRootAbsorbingContribution reward
            (collisionPhaseRoots leftPlan rightPlan time) owner := by
        apply Finset.sum_le_sum
        intro time htime
        rw [collisionPhaseRoots_owner_absorbingContribution]
        apply mul_le_mul_of_nonneg_left _
          (quittingJointSurvivalWeight_nonneg _ 0 time)
        have hcollision := stageCollision_le_mesh_mul_stageAbsorption
          leftPlan rightPlan time hmesh0
            (hmesh time (Finset.mem_range.mp htime))
        linarith

/-- The full behavioral envelope is at least the displayed Never payoff.
This is the formal bridge from the finite accounting no-go to arbitrary
stopping-time deviations. -/
theorem truncated_bestResponseValue_ge_one_sub_two_mul_mesh
    (leftPlan rightPlan : ℕ → PMF Bool) (cutoff : ℕ) {mesh : ℝ}
    (hmesh0 : 0 ≤ mesh)
    (hmesh : ∀ time < cutoff,
      stageAbsorption leftPlan rightPlan time ≤ mesh) :
    (1 - 2 * mesh) *
        (1 - quittingJointSurvivalWeight
          (collisionPhaseRoots leftPlan rightPlan) 0 cutoff) ≤
      quittingRootSequenceBestResponseValue reward
        (quittingTruncatedRoots
          (collisionPhaseRoots leftPlan rightPlan) cutoff) owner := by
  refine (truncated_ownerNeverValue_ge_one_sub_two_mul_mesh
    leftPlan rightPlan cutoff hmesh0 hmesh).trans ?_
  unfold quittingRootSequenceBestResponseValue
  let profile := quittingRootSequenceProfile reward
    (quittingTruncatedRoots
      (collisionPhaseRoots leftPlan rightPlan) cutoff) 0
  have hle := quittingTerminalPayoff_update_le_continuationBestResponseValue
    reward profile owner (profile owner) (by norm_num) reward_abs_le_one
  simpa [profile, quittingRootSequenceTerminalValue,
    Function.update_eq_self] using hle

/-- A later tail can improve the diffuse phase only in proportion to the
mass which survives to it.  This is the exact atom-or-survival alternative
for an arbitrary infinite nonstationary product plan. -/
theorem full_bestResponseValue_ge_diffusePrefix_sub_survival
    (leftPlan rightPlan : ℕ → PMF Bool) (cutoff : ℕ) {mesh : ℝ}
    (hmesh0 : 0 ≤ mesh)
    (hmesh : ∀ time < cutoff,
      stageAbsorption leftPlan rightPlan time ≤ mesh) :
    (1 - 2 * mesh) *
          (1 - quittingJointSurvivalWeight
            (collisionPhaseRoots leftPlan rightPlan) 0 cutoff) -
        quittingJointSurvivalWeight
          (collisionPhaseRoots leftPlan rightPlan) 0 cutoff ≤
      quittingRootSequenceBestResponseValue reward
        (collisionPhaseRoots leftPlan rightPlan) owner := by
  let roots := collisionPhaseRoots leftPlan rightPlan
  let survival := quittingJointSurvivalWeight roots 0 cutoff
  have hprefix := truncated_ownerNeverValue_ge_one_sub_two_mul_mesh
    leftPlan rightPlan cutoff hmesh0 hmesh
  have hdecomp :=
    quittingRootSequenceTerminalValue_eq_truncated_add_jointSurvival_mul
      reward roots owner cutoff
  have htailAbs :
      |quittingRootSequenceTerminalValue reward roots owner cutoff| ≤ 1 := by
    unfold quittingRootSequenceTerminalValue
    exact abs_quittingTerminalPayoff_le reward _ owner (by norm_num)
      reward_abs_le_one
  have htailLower :
      -1 ≤ quittingRootSequenceTerminalValue reward roots owner cutoff :=
    (abs_le.mp htailAbs).1
  have hsurvival0 : 0 ≤ survival :=
    quittingJointSurvivalWeight_nonneg roots 0 cutoff
  have hterminalLower :
      (1 - 2 * mesh) * (1 - survival) - survival ≤
        quittingRootSequenceTerminalValue reward roots owner 0 := by
    rw [hdecomp]
    dsimp only [roots, survival] at hprefix hsurvival0 ⊢
    nlinarith [mul_nonneg hsurvival0 (sub_nonneg.mpr htailLower)]
  refine hterminalLower.trans ?_
  unfold quittingRootSequenceBestResponseValue
  let profile := quittingRootSequenceProfile reward roots 0
  have hle := quittingTerminalPayoff_update_le_continuationBestResponseValue
    reward profile owner (profile owner) (by norm_num) reward_abs_le_one
  simpa [profile, roots, quittingRootSequenceTerminalValue,
    Function.update_eq_self] using hle

/-- **Structural consequence.**  If every row in a prefix has absorption
mesh at most one half and the full plan holds the owner's behavioral cap
below `-kappa`, at least `kappa` live mass must survive the whole prefix.
Hence a uniformly diffuse plan with a genuinely negative cap cannot be
completely absorbing. -/
theorem survival_ge_of_half_mesh_and_negative_cap
    (leftPlan rightPlan : ℕ → PMF Bool) (cutoff : ℕ) {kappa : ℝ}
    (hmesh : ∀ time < cutoff,
      stageAbsorption leftPlan rightPlan time ≤ (1 : ℝ) / 2)
    (hcap : quittingRootSequenceBestResponseValue reward
        (collisionPhaseRoots leftPlan rightPlan) owner ≤ -kappa) :
    kappa ≤ quittingJointSurvivalWeight
      (collisionPhaseRoots leftPlan rightPlan) 0 cutoff := by
  have hlower := full_bestResponseValue_ge_diffusePrefix_sub_survival
    leftPlan rightPlan cutoff (mesh := (1 : ℝ) / 2) (by norm_num) hmesh
  norm_num at hlower
  linarith

/-- Sharp finite-prefix form of the atom-or-survival alternative.  If the
owner's full behavioral cap is at most `-kappa` and every prefix atom is at
most `mesh < 1`, the surviving mass is at least the displayed exact ratio. -/
theorem survival_ge_ratio_of_mesh_and_negative_cap
    (leftPlan rightPlan : ℕ → PMF Bool) (cutoff : ℕ) {mesh kappa : ℝ}
    (hmesh0 : 0 ≤ mesh) (hmeshOne : mesh < 1)
    (hmesh : ∀ time < cutoff,
      stageAbsorption leftPlan rightPlan time ≤ mesh)
    (hcap : quittingRootSequenceBestResponseValue reward
        (collisionPhaseRoots leftPlan rightPlan) owner ≤ -kappa) :
    (1 + kappa - 2 * mesh) / (2 * (1 - mesh)) ≤
      quittingJointSurvivalWeight
        (collisionPhaseRoots leftPlan rightPlan) 0 cutoff := by
  have hlower := full_bestResponseValue_ge_diffusePrefix_sub_survival
    leftPlan rightPlan cutoff hmesh0 hmesh
  have hcombined := hlower.trans hcap
  have hden : 0 < 2 * (1 - mesh) := by linarith
  rw [div_le_iff₀ hden]
  nlinarith

/-- Without a supplied mesh bound, the same statement is an exact
disjunction: either one date has a macroscopic absorption atom above `mesh`,
or the indicated amount of live mass survives the prefix. -/
theorem exists_large_stageAbsorption_or_survival_ge_ratio
    (leftPlan rightPlan : ℕ → PMF Bool) (cutoff : ℕ) {mesh kappa : ℝ}
    (hmesh0 : 0 ≤ mesh) (hmeshOne : mesh < 1)
    (hcap : quittingRootSequenceBestResponseValue reward
        (collisionPhaseRoots leftPlan rightPlan) owner ≤ -kappa) :
    (∃ time, time < cutoff ∧
        mesh < stageAbsorption leftPlan rightPlan time) ∨
      (1 + kappa - 2 * mesh) / (2 * (1 - mesh)) ≤
        quittingJointSurvivalWeight
          (collisionPhaseRoots leftPlan rightPlan) 0 cutoff := by
  by_cases hlarge : ∃ time, time < cutoff ∧
      mesh < stageAbsorption leftPlan rightPlan time
  · exact Or.inl hlarge
  · right
    apply survival_ge_ratio_of_mesh_and_negative_cap
      leftPlan rightPlan cutoff hmesh0 hmeshOne _ hcap
    intro time htime
    exact le_of_not_gt fun hgt => hlarge ⟨time, htime, hgt⟩

/-- A stage atom above `1-d^2` contains a genuinely near-sure opponent
marginal: at least one of the two opponent Continue probabilities is below
`d`.  This is precisely the numerical input expected by near-sure root
replacement, before any Nash provenance is considered. -/
theorem exists_nearSureOpponent_of_stageAbsorption_gt_one_sub_sq
    (leftPlan rightPlan : ℕ → PMF Bool) (time : ℕ) {d : ℝ}
    (hd0 : 0 ≤ d)
    (hlarge : 1 - d ^ 2 < stageAbsorption leftPlan rightPlan time) :
    (leftPlan time false).toReal < d ∨
      (rightPlan time false).toReal < d := by
  by_contra hnot
  push Not at hnot
  have hleft0 : 0 ≤ (leftPlan time false).toReal := ENNReal.toReal_nonneg
  have hright0 : 0 ≤ (rightPlan time false).toReal := ENNReal.toReal_nonneg
  have hproduct : d ^ 2 ≤
      (leftPlan time false).toReal * (rightPlan time false).toReal := by
    rw [pow_two]
    exact mul_le_mul hnot.1 hnot.2 hd0 hleft0
  have hidentity :
      1 - stageAbsorption leftPlan rightPlan time =
        (leftPlan time false).toReal * (rightPlan time false).toReal := by
    simp [stageAbsorption, leftHazard, rightHazard,
      Math.PMFProduct.pmfBool_false_toReal]
    ring
  nlinarith

/-- For a completely absorbing nonstationary product plan, a uniform stage
mesh bound `mesh` forces the owner's full behavioral cap above
`1 - 2*mesh`.  This is the exact infinite-horizon strengthening of the
stationary rare-scaling regression. -/
theorem bestResponseValue_ge_one_sub_two_mul_mesh_of_completeAbsorption
    (leftPlan rightPlan : ℕ → PMF Bool) {mesh : ℝ}
    (hmesh0 : 0 ≤ mesh)
    (hmesh : ∀ time,
      stageAbsorption leftPlan rightPlan time ≤ mesh)
    (hcomplete : Tendsto
      (quittingJointSurvivalWeight
        (collisionPhaseRoots leftPlan rightPlan) 0) atTop (nhds 0)) :
    1 - 2 * mesh ≤ quittingRootSequenceBestResponseValue reward
      (collisionPhaseRoots leftPlan rightPlan) owner := by
  let survival := fun cutoff => quittingJointSurvivalWeight
    (collisionPhaseRoots leftPlan rightPlan) 0 cutoff
  have hlower : ∀ cutoff,
      (1 - 2 * mesh) * (1 - survival cutoff) - survival cutoff ≤
        quittingRootSequenceBestResponseValue reward
          (collisionPhaseRoots leftPlan rightPlan) owner := by
    intro cutoff
    exact full_bestResponseValue_ge_diffusePrefix_sub_survival
      leftPlan rightPlan cutoff hmesh0 (fun time _ => hmesh time)
  have hsurvival : Tendsto survival atTop (nhds 0) := by
    simpa only [survival] using hcomplete
  have htend : Tendsto
      (fun cutoff =>
        (1 - 2 * mesh) * (1 - survival cutoff) - survival cutoff)
      atTop (nhds (1 - 2 * mesh)) := by
    have honeSub : Tendsto (fun cutoff => 1 - survival cutoff)
        atTop (nhds 1) := by
      simpa using tendsto_const_nhds.sub hsurvival
    have hscaled : Tendsto
        (fun cutoff => (1 - 2 * mesh) * (1 - survival cutoff))
        atTop (nhds (1 - 2 * mesh)) := by
      simpa using tendsto_const_nhds.mul honeSub
    simpa using hscaled.sub hsurvival
  exact le_of_tendsto' htend hlower

/-- A completely absorbing legal product plan whose every stage has
absorption at most one half has nonnegative full behavioral cap for the
owner.  In particular it cannot implement the collision punishment value
`-1`, even with arbitrary time variation. -/
theorem bestResponseValue_nonneg_of_half_mesh_of_completeAbsorption
    (leftPlan rightPlan : ℕ → PMF Bool)
    (hmesh : ∀ time,
      stageAbsorption leftPlan rightPlan time ≤ (1 : ℝ) / 2)
    (hcomplete : Tendsto
      (quittingJointSurvivalWeight
        (collisionPhaseRoots leftPlan rightPlan) 0) atTop (nhds 0)) :
    0 ≤ quittingRootSequenceBestResponseValue reward
      (collisionPhaseRoots leftPlan rightPlan) owner := by
  simpa using
    bestResponseValue_ge_one_sub_two_mul_mesh_of_completeAbsorption
      leftPlan rightPlan (mesh := (1 : ℝ) / 2) (by norm_num) hmesh hcomplete

end QuittingNonstationaryCollisionPunishmentNoGo

end GameTheory
