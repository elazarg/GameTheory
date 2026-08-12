/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.OrdinaryNonQProducer
import UniformEquilibrium.Quitting.Classification.LCP.SupportHierarchy

/-!
# Closing the ordinary non-Q branch

This module combines the algebraic forbidden right-hand side with the
analytic Bellman germ.  It is deliberately downstream of both the strategic
endpoint compilers and the punctured-support normal-layer induction.
-/

noncomputable section

namespace GameTheory
namespace QuittingLCPClassification

open Filter Set Topology
open StochasticGame

variable {ι : Type}

/-- Failure of projective Q exposes one right-hand side with no projective
solution. -/
theorem exists_direction_without_projectiveLCPSolution
    [Fintype ι] (M : ι → ι → ℝ) (hM : ¬IsProjectiveQMatrix M) :
    ∃ q : ι → ℝ, ¬Nonempty (ProjectiveLCPSolution M q) := by
  unfold IsProjectiveQMatrix HasProjectiveLCPSolution at hM
  exact not_forall.mp hM

/-- A nonnegative right-hand side always has the cemetery-only projective
solution. -/
def projectiveLCPSolution_cemeteryOnly
    [Fintype ι] (M : ι → ι → ℝ) (q : ι → ℝ) (hq : ∀ who, 0 ≤ q who) :
    ProjectiveLCPSolution M q where
  cemetery := 1
  singleton := 0
  cemetery_nonneg := zero_le_one
  singleton_nonneg := fun _ => le_rfl
  total := by simp
  residual_nonneg := by simpa using hq
  complementary := by simp

/-- Therefore a forbidden projective right-hand side has a negative
coordinate. -/
theorem exists_negative_of_no_projectiveLCPSolution
    [Fintype ι] (M : ι → ι → ℝ) (q : ι → ℝ)
    (hno : ¬Nonempty (ProjectiveLCPSolution M q)) :
    ∃ who, q who < 0 := by
  by_contra hnone
  have hq : ∀ who, 0 ≤ q who := by
    intro who
    exact le_of_not_gt (fun hnegative => hnone ⟨who, hnegative⟩)
  exact hno ⟨projectiveLCPSolution_cemeteryOnly M q hq⟩

/-- Shifting by the solo baseline plus a direction with a negative
coordinate cannot land in the zero-solo branch. -/
theorem not_isQuittingZeroSolo_baselineShift_of_negative
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (q : ι → ℝ) {who : ι} (hwho : q who < 0) :
    ¬IsQuittingZeroSolo
      (quittingRewardShift reward
        (fun player => quittingSoloBaseline reward player + q player)) := by
  intro hzero
  have h := hzero who
  change reward (quittingSingletonTerminal who) who -
      (quittingSoloBaseline reward who + q who) ≤ 0 at h
  have hbaseline : quittingSoloBaseline reward who =
      reward (quittingSingletonTerminal who) who := by
    rfl
  rw [hbaseline] at h
  linarith

variable [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- An absorbing product root either has two positive quitters or has one
positive owner and every other marginal is pure Continue. -/
theorem two_positive_or_isolated_of_continueMass_lt_one
    (root : ι → PMF Bool)
    (habsorbs : quittingStationaryContinueMass root < 1) :
    (∃ first second, first ≠ second ∧
        0 < (root first true).toReal ∧ 0 < (root second true).toReal) ∨
      ∃ owner, 0 < (root owner true).toReal ∧
        ∀ other, other ≠ owner → root other = PMF.pure false := by
  classical
  have hexists : ∃ owner, 0 < (root owner true).toReal := by
    by_contra hnone
    have hzero : ∀ owner, (root owner true).toReal = 0 := by
      intro owner
      have hnonpos : ¬0 < (root owner true).toReal := by
        intro hpositive
        exact hnone ⟨owner, hpositive⟩
      exact le_antisymm (le_of_not_gt hnonpos) ENNReal.toReal_nonneg
    have hroot : root = (quittingAllContinueRoot : ι → PMF Bool) := by
      funext owner
      exact pmf_eq_pure_false_of_apply_true_toReal_eq_zero _ (hzero owner)
    subst root
    rw [quittingStationaryContinueMass_eq_prod_continueProbability] at habsorbs
    simp [quittingAllContinueRoot] at habsorbs
  obtain ⟨owner, howner⟩ := hexists
  by_cases hsecond : ∃ other, other ≠ owner ∧
      0 < (root other true).toReal
  · obtain ⟨other, hne, hother⟩ := hsecond
    exact Or.inl ⟨owner, other, Ne.symm hne, howner, hother⟩
  · refine Or.inr ⟨owner, howner, ?_⟩
    intro other hne
    apply pmf_eq_pure_false_of_apply_true_toReal_eq_zero
    apply le_antisymm
    · by_contra hpositive
      have hpos : 0 < (root other true).toReal :=
        lt_of_not_ge hpositive
      exact hsecond ⟨other, hne, hpos⟩
    · exact ENNReal.toReal_nonneg

/-- A provenance-preserving packet on the baseline-shifted table contradicts
a forbidden normal-core right-hand side once punctured support has been
placed in the corrected core. -/
theorem false_of_supportedPacket_and_active_mem_normalCore
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (q : normalCore (normalizedSoloMatrix reward) → ℝ)
    (hno : ¬Nonempty (ProjectiveLCPSolution
      (normalizedNormalPlayerMatrix reward) q))
    (g : (quittingGame
      (quittingRewardShift reward (fun who =>
        quittingSoloBaseline reward who +
          extendNormalDirection (normalizedSoloMatrix reward) q who))).AnalyticBellmanGerm)
    (supported : QuittingGermSupportedProjectivePacket
      (quittingRewardShift reward (fun who =>
        quittingSoloBaseline reward who +
          extendNormalDirection (normalizedSoloMatrix reward) q who)) g)
    (hactiveCore : ∀ who,
      QuittingGermEventuallyActive g who →
        who ∈ normalCore (normalizedSoloMatrix reward)) : False := by
  let qfull := extendNormalDirection (normalizedSoloMatrix reward) q
  let solution : ProjectiveLCPSolution (normalizedSoloMatrix reward) qfull :=
    projectiveLCPSolutionOfBaselineShiftedPacket
      reward qfull supported.packet
  have hsupport : ∀ who, 0 < solution.singleton who →
      who ∈ normalCore (normalizedSoloMatrix reward) := by
    intro who hpositive
    rw [projectiveLCPSolutionOfBaselineShiftedPacket_singleton] at hpositive
    exact hactiveCore who
      (supported.positive_eventuallyActive who hpositive)
  exact hno ⟨restrictProjectiveLCPSolutionToNormalCore
    (normalizedSoloMatrix reward) q solution hsupport⟩

/-- The all-Continue endpoint of the forbidden-direction auxiliary germ is
impossible: its projective packet preserves punctured support, the hierarchy
places that support in the corrected core, and restriction gives the
forbidden projective solution. -/
theorem false_of_forbidden_direction_allContinue_endpoint
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (q : normalCore (normalizedSoloMatrix reward) → ℝ)
    (hno : ¬Nonempty (ProjectiveLCPSolution
      (normalizedNormalPlayerMatrix reward) q))
    (g : (quittingGame
      (quittingRewardShift reward (fun who =>
        quittingSoloBaseline reward who +
          extendNormalDirection (normalizedSoloMatrix reward) q who))).AnalyticBellmanGerm)
    (hcontinue : quittingStationaryContinueMass
      (g.endpointProfile none) = 1) : False := by
  obtain ⟨normalOwner, hqnegative⟩ :=
    exists_negative_of_no_projectiveLCPSolution
      (normalizedNormalPlayerMatrix reward) q hno
  let qfull := extendNormalDirection (normalizedSoloMatrix reward) q
  have hnegative : qfull normalOwner.1 < 0 := by
    simpa [qfull, extendNormalDirection_of_mem _ _ normalOwner.property]
      using hqnegative
  have hnotZero : ¬IsQuittingZeroSolo
      (quittingRewardShift reward (fun who =>
        quittingSoloBaseline reward who + qfull who)) :=
    not_isQuittingZeroSolo_baselineShift_of_negative
      reward qfull hnegative
  rcases quittingGerm_allContinue_zeroSolo_or_supportedProjectivePacket
      _ g hcontinue with hzero | hsupported
  · exact hnotZero hzero
  · exact false_of_supportedPacket_and_active_mem_normalCore
      reward q hno g hsupported.some (fun who hactive =>
        quittingGerm_eventuallyActive_mem_normalCore_of_baseline_extendShift
          reward q g hcontinue who hactive)

/-! ## Strategic closure -/

/-- Every ordinary non-Q branch produces an ordinary uniform-equilibrium
payoff.  The forbidden projective direction is fed to an analytic Bellman
germ.  An all-Continue endpoint contradicts the provenance-preserving normal
hierarchy; an absorbing endpoint either has two positive hazards and hence
contracts every unilateral tail, or has one positive owner and is repaired by
the first nonpositive opponent column exposed by the same germ. -/
theorem exists_uniformEquilibriumPayoff_of_ordinaryNonQMatrixBranch
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (branch : OrdinaryNonQMatrixBranch reward) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  obtain ⟨q, hno⟩ := exists_direction_without_projectiveLCPSolution
    (normalizedNormalPlayerMatrix reward) branch.not_projectiveQ
  let qfull := extendNormalDirection (normalizedSoloMatrix reward) q
  let anchor : Payoff ι := fun who =>
    quittingSoloBaseline reward who + qfull who
  obtain ⟨g⟩ := nonempty_analyticBellmanGerm_quittingGame
    (quittingRewardShift reward anchor)
  have hmassLe : quittingStationaryContinueMass
      (g.endpointProfile none) ≤ 1 :=
    quittingStationaryContinueMass_le_one (g.endpointProfile none)
  rcases lt_or_eq_of_le hmassLe with habsorbs | hcontinue
  · rcases two_positive_or_isolated_of_continueMass_lt_one
        (g.endpointProfile none) habsorbs with htwo | hisolated
    · exact ⟨_,
        isUniformEquilibriumPayoff_of_shiftedGerm_absorbingEndpoint_contracts
          reward anchor g habsorbs
            (fixedOpponents_contract_of_two_positive
              (g.endpointProfile none) htwo)⟩
    · obtain ⟨owner, howner, hother⟩ := hisolated
      by_cases hnormal : owner ∈ normalCore (normalizedSoloMatrix reward)
      · exact
          exists_uniformEquilibriumPayoff_of_shiftedGerm_isolatedNormalEndpoint
            reward anchor g owner howner hother hnormal
      · have hqfull : 0 < qfull owner := by
          change 0 < extendNormalDirection
            (normalizedSoloMatrix reward) q owner
          rw [extendNormalDirection_of_notMem
            (normalizedSoloMatrix reward) q hnormal]
          norm_num
        obtain ⟨blocker, hne, hentry⟩ :=
          exists_normalizedSoloMatrix_blocker_of_isolated_endpoint
            reward qfull (by simpa only [anchor] using g)
              owner howner hother hqfull
        exact
          exists_uniformEquilibriumPayoff_of_shiftedGerm_isolatedEndpoint_of_blocker
            reward anchor g owner howner hother blocker hne hentry
  · exact False.elim
      (false_of_forbidden_direction_allContinue_endpoint
        reward q hno (by simpa only [anchor, qfull] using g)
          (by simpa only [anchor, qfull] using hcontinue))

end QuittingLCPClassification
end GameTheory
