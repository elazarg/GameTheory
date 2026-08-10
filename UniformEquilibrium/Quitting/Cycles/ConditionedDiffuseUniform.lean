/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.ConditionedDiffuseCompiler
import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalUniformPayoffSelection

/-!
# Uniform payoff from diffuse conditioned certificates

`ConditionedDiffuseCompiler` turns one singleton-tight, deleted-complete
conditioned source with mesh at most `rho` into a terminal approximate Nash
profile with error linear in `rho`.  This file packages those hypotheses and
performs the all-errors diagonal step.

This is a consumer theorem.  It does not assert that an arbitrary quitting
game supplies the certificates, that strict phantom slack can be removed, or
that an incomplete deleted clock can be repaired.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Chronological suffix of a root sequence. -/
def quittingRootSequenceSuffix
    (roots : ℕ → ι → PMF Bool) (start : ℕ) : ℕ → ι → PMF Bool :=
  fun time => roots (start + time)

omit [DecidableEq ι] in
theorem quittingJointSurvivalWeight_suffix
    (roots : ℕ → ι → PMF Bool) (start time fuel : ℕ) :
    quittingJointSurvivalWeight (quittingRootSequenceSuffix roots start)
        time fuel =
      quittingJointSurvivalWeight roots (start + time) fuel := by
  calc
    quittingJointSurvivalWeight (quittingRootSequenceSuffix roots start)
        time fuel =
      quittingJointSurvivalWeight
        (fun offset => quittingRootSequenceSuffix roots start (time + offset))
        0 fuel := quittingJointSurvivalWeight_eq_shift _ time fuel
    _ = quittingJointSurvivalWeight
        (fun offset => roots ((start + time) + offset)) 0 fuel := by
      congr 1
      funext offset
      simp only [quittingRootSequenceSuffix, Nat.add_assoc]
    _ = quittingJointSurvivalWeight roots (start + time) fuel :=
      (quittingJointSurvivalWeight_eq_shift roots (start + time) fuel).symm

omit [DecidableEq ι] in
theorem quittingJointSurvivalLimit_suffix
    (roots : ℕ → ι → PMF Bool) (start time : ℕ) :
    quittingJointSurvivalLimit (quittingRootSequenceSuffix roots start) time =
      quittingJointSurvivalLimit roots (start + time) := by
  apply tendsto_nhds_unique
    (tendsto_quittingJointSurvivalLimit
      (quittingRootSequenceSuffix roots start) time)
  convert tendsto_quittingJointSurvivalLimit roots (start + time) using 1
  funext fuel
  exact quittingJointSurvivalWeight_suffix roots start time fuel

omit [DecidableEq ι] in
@[simp] theorem quittingTailEventualAbsorption_suffix
    (roots : ℕ → ι → PMF Bool) (start time : ℕ) :
    quittingTailEventualAbsorption (quittingRootSequenceSuffix roots start)
        time =
      quittingTailEventualAbsorption roots (start + time) := by
  unfold quittingTailEventualAbsorption
  rw [quittingJointSurvivalLimit_suffix]

omit [DecidableEq ι] in
@[simp] theorem quittingTailConditionedAbsorptionWeight_suffix
    (roots : ℕ → ι → PMF Bool) (start time : ℕ) :
    quittingTailConditionedAbsorptionWeight
        (quittingRootSequenceSuffix roots start) time =
      quittingTailConditionedAbsorptionWeight roots (start + time) := by
  unfold quittingTailConditionedAbsorptionWeight
  rw [quittingTailEventualAbsorption_suffix]
  rfl

@[simp] theorem quittingTailConditionedOpponentWeight_suffix
    (roots : ℕ → ι → PMF Bool) (start time : ℕ) (who : ι) :
    quittingTailConditionedOpponentWeight
        (quittingRootSequenceSuffix roots start) time who =
      quittingTailConditionedOpponentWeight roots (start + time) who := by
  unfold quittingTailConditionedOpponentWeight
  rw [quittingTailEventualAbsorption_suffix]
  rfl

omit [DecidableEq ι] in
@[simp] theorem quittingTailConditionedValue_suffix
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι) (start time : ℕ) :
    quittingTailConditionedValue (quittingRootSequenceSuffix roots start)
        (fun offset => value (start + offset)) boundary time =
      quittingTailConditionedValue roots value boundary (start + time) := by
  funext who
  unfold quittingTailConditionedValue
  rw [quittingJointSurvivalLimit_suffix,
    quittingTailEventualAbsorption_suffix]

/-- The exact source-side hypotheses consumed by the conditioned diffuse
compiler at one mesh scale. -/
structure QuittingConditionedDiffuseCertificate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (rho : ℝ) where
  roots : ℕ → ι → PMF Bool
  value : ℕ → Payoff ι
  boundary : Payoff ι
  rho_nonneg : 0 ≤ rho
  policy : ∀ time, value time =
    quittingRootSuccessorPayoff reward (value (time + 1)) (roots time)
  nash : ∀ time,
    IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time)
  positive : ∀ time, 0 < quittingTailEventualAbsorption roots time
  conditionedBound : ∀ time player,
    |quittingTailConditionedValue roots value boundary time player| ≤
      quittingRewardBound reward
  tight : ∀ who, boundary who = quittingSoloBaseline reward who
  sourceFloor : ∀ time who,
    quittingSoloBaseline reward who ≤ value time who
  mesh : ∀ time,
    quittingTailConditionedAbsorptionWeight roots time ≤ rho
  small : ∀ time, Fintype.card ι *
    quittingTailConditionedAbsorptionWeight roots time ≤ 1
  half : ∀ time,
    quittingTailConditionedAbsorptionWeight roots time ≤ 1 / 2
  deletedComplete : ∀ who start,
    ¬Summable (fun offset =>
      quittingTailConditionedOpponentWeight roots (start + offset) who)

namespace QuittingConditionedDiffuseCertificate

variable {rho : ℝ}

/-- The terminal profile produced by a diffuse conditioned certificate. -/
def profile (certificate : QuittingConditionedDiffuseCertificate reward rho) :
    (quittingGame reward).BehaviorProfile :=
  quittingInfinitePathProfile reward
    (quittingTailDiffuseRescaledRoots certificate.roots certificate.positive)

/-- A certificate at mesh `rho` produces the explicit linear-error terminal
approximate Nash profile and approximates its initial conditioned target. -/
theorem isεAsymptoticNash_and_approximates
    [Nonempty ι]
    (certificate : QuittingConditionedDiffuseCertificate reward rho) :
    (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward)
        ((6 * quittingRewardBound reward * Fintype.card ι * rho) +
          (2 * quittingRewardBound reward * Fintype.card ι * rho) +
          ((7 * Fintype.card ι + 16) * quittingRewardBound reward * rho))
        certificate.profile ∧
      ∀ who,
        |quittingTerminalPayoff reward certificate.profile who -
          quittingTailConditionedValue certificate.roots certificate.value
            certificate.boundary 0 who| ≤
        6 * quittingRewardBound reward * Fintype.card ι * rho := by
  exact conditionedDiffuseRescaledRoots_isεAsymptoticNash_and_approximates
    certificate.roots certificate.value certificate.boundary
      certificate.policy certificate.nash
      (quittingRewardBound_nonneg reward) certificate.rho_nonneg
      (abs_reward_le_quittingRewardBound reward) certificate.positive
      certificate.conditionedBound certificate.tight certificate.sourceFloor
      certificate.mesh certificate.small certificate.half
      certificate.deletedComplete

end QuittingConditionedDiffuseCertificate

/-- The coefficient of the mesh in the diffuse conditioned compiler's
terminal Nash error. -/
def quittingConditionedDiffuseCompilerCoefficient
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : ℝ :=
  6 * quittingRewardBound reward * Fintype.card ι +
    2 * quittingRewardBound reward * Fintype.card ι +
    (7 * Fintype.card ι + 16) * quittingRewardBound reward

omit [DecidableEq ι] in
theorem quittingConditionedDiffuseCompilerCoefficient_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    0 ≤ quittingConditionedDiffuseCompilerCoefficient reward := by
  unfold quittingConditionedDiffuseCompilerCoefficient
  have hbound := quittingRewardBound_nonneg reward
  positivity

/-- **All-errors diffuse conditioned compiler.**  If arbitrarily fine positive
mesh scales admit singleton-tight, deleted-complete conditioned certificates,
the finite quitting game has a uniform-equilibrium payoff. -/
theorem
    quittingGame_exists_uniformEquilibriumPayoff_of_arbitrarilyFineConditionedDiffuseCertificates
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcertificates : ∀ targetMesh : ℝ, 0 < targetMesh →
      ∃ rho : ℝ, 0 < rho ∧ rho ≤ targetMesh ∧
        Nonempty (QuittingConditionedDiffuseCertificate reward rho)) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors
    reward
  intro epsilon hepsilon
  let coefficient := quittingConditionedDiffuseCompilerCoefficient reward
  let targetMesh := epsilon / (coefficient + 1)
  have hcoefficient : 0 ≤ coefficient := by
    exact quittingConditionedDiffuseCompilerCoefficient_nonneg reward
  have hdenominator : 0 < coefficient + 1 := by linarith
  have htargetMesh : 0 < targetMesh := by
    exact div_pos hepsilon hdenominator
  obtain ⟨rho, hrho, hrhoTarget, ⟨certificate⟩⟩ :=
    hcertificates targetMesh htargetMesh
  have hcompiled := certificate.isεAsymptoticNash_and_approximates.1
  have herrorEq :
      (6 * quittingRewardBound reward * Fintype.card ι * rho) +
          (2 * quittingRewardBound reward * Fintype.card ι * rho) +
          ((7 * Fintype.card ι + 16) * quittingRewardBound reward * rho) =
        coefficient * rho := by
    dsimp only [coefficient]
    unfold quittingConditionedDiffuseCompilerCoefficient
    ring
  have htargetErrorLe : coefficient * targetMesh ≤ epsilon := by
    dsimp only [targetMesh]
    calc
      coefficient * (epsilon / (coefficient + 1)) =
          coefficient * epsilon / (coefficient + 1) := by ring
      _ ≤ epsilon := by
        rw [div_le_iff₀ hdenominator]
        nlinarith [mul_nonneg hcoefficient (le_of_lt hepsilon)]
  have herrorLe : coefficient * rho ≤ epsilon :=
    (mul_le_mul_of_nonneg_left hrhoTarget hcoefficient).trans htargetErrorLe
  refine ⟨certificate.profile, ?_⟩
  intro who deviation
  have hlocal := hcompiled who deviation
  rw [herrorEq] at hlocal
  linarith

/-- Exact-scale convenience wrapper for the arbitrarily-fine theorem. -/
theorem
    quittingGame_exists_uniformEquilibriumPayoff_of_conditionedDiffuseCertificates
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcertificates : ∀ rho : ℝ, 0 < rho →
      Nonempty (QuittingConditionedDiffuseCertificate reward rho)) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply
    quittingGame_exists_uniformEquilibriumPayoff_of_arbitrarilyFineConditionedDiffuseCertificates
      reward
  intro targetMesh htargetMesh
  exact ⟨targetMesh, htargetMesh, le_rfl,
    hcertificates targetMesh htargetMesh⟩

/-- **Single-tail diffuse compiler.**  A singleton-tight exact source tail
whose conditioned mesh tends to zero and whose every deleted conditioned
clock is complete supplies the arbitrarily fine certificates above. -/
theorem
    quittingGame_exists_uniformEquilibriumPayoff_of_conditionedDiffuseTail
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time))
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption roots time)
    (hconditionedBound : ∀ time player,
      |quittingTailConditionedValue roots value boundary time player| ≤
        quittingRewardBound reward)
    (htight : ∀ who, boundary who = quittingSoloBaseline reward who)
    (hsourceFloor : ∀ time who,
      quittingSoloBaseline reward who ≤ value time who)
    (hmesh : Tendsto
      (quittingTailConditionedAbsorptionWeight roots) atTop (nhds 0))
    (hdeletedComplete : ∀ who start,
      ¬Summable (fun offset =>
        quittingTailConditionedOpponentWeight roots (start + offset) who)) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply
    quittingGame_exists_uniformEquilibriumPayoff_of_arbitrarilyFineConditionedDiffuseCertificates
      reward
  intro targetMesh htargetMesh
  have hcardNat : 0 < Fintype.card ι := Fintype.card_pos
  have hcard : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast hcardNat
  let safetyMesh : ℝ := 1 / (2 * Fintype.card ι)
  let requestedMesh := min targetMesh safetyMesh
  have hsafetyMesh : 0 < safetyMesh := by
    dsimp only [safetyMesh]
    positivity
  have hrequestedMesh : 0 < requestedMesh := by
    exact lt_min htargetMesh hsafetyMesh
  have heventually : ∀ᶠ time : ℕ in atTop,
      quittingTailConditionedAbsorptionWeight roots time < requestedMesh :=
    (tendsto_order.1 hmesh).2 requestedMesh hrequestedMesh
  obtain ⟨start, hstart⟩ := Filter.eventually_atTop.1 heventually
  let suffixRoots := quittingRootSequenceSuffix roots start
  let suffixValue : ℕ → Payoff ι := fun time => value (start + time)
  have hsafetyHalf : safetyMesh ≤ 1 / 2 := by
    dsimp only [safetyMesh]
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * (Fintype.card ι : ℝ))
      (by norm_num : (0 : ℝ) < 2)).2
    norm_num
    exact_mod_cast (Nat.succ_le_iff.mpr hcardNat)
  let certificate : QuittingConditionedDiffuseCertificate reward requestedMesh :=
    { roots := suffixRoots
      value := suffixValue
      boundary := boundary
      rho_nonneg := hrequestedMesh.le
      policy := by
        intro time
        simpa only [suffixRoots, suffixValue, quittingRootSequenceSuffix,
          Nat.add_assoc] using hpolicy (start + time)
      nash := by
        intro time
        simpa only [suffixRoots, suffixValue, quittingRootSequenceSuffix,
          Nat.add_assoc] using hnash (start + time)
      positive := by
        intro time
        simpa only [suffixRoots, quittingTailEventualAbsorption_suffix] using
          hpositive (start + time)
      conditionedBound := by
        intro time player
        simpa only [suffixRoots, suffixValue,
          quittingTailConditionedValue_suffix] using
            hconditionedBound (start + time) player
      tight := htight
      sourceFloor := by
        intro time who
        exact hsourceFloor (start + time) who
      mesh := by
        intro time
        rw [show quittingTailConditionedAbsorptionWeight suffixRoots time =
            quittingTailConditionedAbsorptionWeight roots (start + time) by
          simp only [suffixRoots, quittingTailConditionedAbsorptionWeight_suffix]]
        exact (hstart (start + time) (Nat.le_add_right start time)).le
      small := by
        intro time
        have halpha : quittingTailConditionedAbsorptionWeight suffixRoots time ≤
            requestedMesh := by
          rw [show quittingTailConditionedAbsorptionWeight suffixRoots time =
              quittingTailConditionedAbsorptionWeight roots (start + time) by
            simp only [suffixRoots,
              quittingTailConditionedAbsorptionWeight_suffix]]
          exact (hstart (start + time) (Nat.le_add_right start time)).le
        have halphaSafety :
            quittingTailConditionedAbsorptionWeight suffixRoots time ≤
              safetyMesh := halpha.trans (min_le_right _ _)
        calc
          (Fintype.card ι : ℝ) *
              quittingTailConditionedAbsorptionWeight suffixRoots time ≤
            Fintype.card ι * safetyMesh :=
              mul_le_mul_of_nonneg_left halphaSafety hcard.le
          _ = 1 / 2 := by
            dsimp only [safetyMesh]
            field_simp
          _ ≤ 1 := by norm_num
      half := by
        intro time
        have halpha : quittingTailConditionedAbsorptionWeight suffixRoots time ≤
            requestedMesh := by
          rw [show quittingTailConditionedAbsorptionWeight suffixRoots time =
              quittingTailConditionedAbsorptionWeight roots (start + time) by
            simp only [suffixRoots,
              quittingTailConditionedAbsorptionWeight_suffix]]
          exact (hstart (start + time) (Nat.le_add_right start time)).le
        exact halpha.trans (min_le_right _ _ |>.trans hsafetyHalf)
      deletedComplete := by
        intro who suffixStart
        have hsource := hdeletedComplete who (start + suffixStart)
        simpa only [suffixRoots,
          quittingTailConditionedOpponentWeight_suffix, Nat.add_assoc] using
            hsource }
  exact ⟨requestedMesh, hrequestedMesh,
    min_le_left targetMesh safetyMesh, ⟨certificate⟩⟩

end GameTheory
