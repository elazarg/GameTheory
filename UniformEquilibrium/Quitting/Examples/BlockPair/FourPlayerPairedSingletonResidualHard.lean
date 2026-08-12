/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Examples.BlockPair.FourPlayerPairedSingletonLCP
import UniformEquilibrium.Quitting.Examples.BlockPair.FourPlayerPairedSingletonPeriodTwoStationary
import UniformEquilibrium.Quitting.Classification.LCP.Gate

/-!
# Residual-hard calibration for the paired-singleton family

The paired singleton matrix fails projective Q-bar already on the principal
pair `{0,2}`.  Together with its full corrected core, standard-Q property,
and lack of a homogeneous simplex solution, this places both concrete
completions in the residual hard class of the LCP gate.

The period-two completion nevertheless has an exact uniform-equilibrium
payoff, although it has no exact stationary terminal Nash profile.  Thus
membership in the residual hard class, even with a full four-player core and
exact stationary nonexistence, is only an algebraic/temporal calibration; it
is not sufficient for counterexamplehood.
-/

noncomputable section

namespace GameTheory
namespace FourPlayerPairedSingleton

open QuittingLCPClassification Math.LinearProgramming StochasticGame

private def crossPair : Finset Player := {0, 2}

private def crossZero : crossPair := ⟨0, by simp [crossPair]⟩

private def crossTwo : crossPair := ⟨2, by simp [crossPair]⟩

/-- The paired singleton matrix fails projective Q-bar on its cross-pair
principal block. -/
theorem pairedSingletonMatrix_not_projectiveQBar :
    ¬ IsProjectiveQBarMatrix pairedSingletonMatrix := by
  intro hqbar
  have hprojective := hqbar crossPair (by simp [crossPair])
  obtain ⟨solution⟩ := hprojective (fun _ => -1)
  have hzero := solution.residual_nonneg crossZero
  have htwo := solution.residual_nonneg crossTwo
  have hcemetery := solution.cemetery_nonneg
  have hs0 := solution.singleton_nonneg crossZero
  have hs2 := solution.singleton_nonneg crossTwo
  have htotal := solution.total
  have huniv : (Finset.univ : Finset crossPair) = {crossZero, crossTwo} := by
    symm
    apply Finset.eq_univ_of_forall
    intro player
    have hplayer : player.1 ∈ ({0, 2} : Finset Player) := player.2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hplayer
    rcases hplayer with hplayer | hplayer
    · have heq : player = crossZero := by
        apply Subtype.ext
        exact hplayer
      simp [heq]
    · have heq : player = crossTwo := by
        apply Subtype.ext
        exact hplayer
      simp [heq]
  change 0 ≤ solution.cemetery * -1 +
      (Finset.univ.sum fun j : crossPair =>
        solution.singleton j *
          principalMatrix pairedSingletonMatrix crossPair crossZero j)
    at hzero
  change 0 ≤ solution.cemetery * -1 +
      (Finset.univ.sum fun j : crossPair =>
        solution.singleton j *
          principalMatrix pairedSingletonMatrix crossPair crossTwo j)
    at htwo
  change solution.cemetery +
      (Finset.univ.sum fun j : crossPair => solution.singleton j) = 1
    at htotal
  rw [huniv] at hzero htwo htotal
  have hne : crossZero ≠ crossTwo := by decide
  have hnotMem : crossZero ∉ ({crossTwo} : Finset crossPair) := by
    simpa using hne
  rw [Finset.sum_insert hnotMem, Finset.sum_singleton] at hzero htwo htotal
  simp [crossPair, crossZero, crossTwo, principalMatrix,
    pairedSingletonMatrix] at hzero htwo htotal
  have hsum : solution.cemetery +
      solution.singleton crossZero + solution.singleton crossTwo = 1 := by
    linarith
  linarith

private def pairedCoreEquiv : Player ≃ normalCore pairedSingletonMatrix :=
  Equiv.ofBijective
    (fun player => ⟨player, pairedSingletonMatrix_mem_normalCore player⟩)
    ⟨fun _ _ h => Subtype.ext_iff.mp h, fun player =>
      ⟨player.1, Subtype.ext rfl⟩⟩

private theorem pairedNormalPlayerMatrix_eq_reindex :
    normalPlayerMatrix pairedSingletonMatrix =
      reindexMatrix pairedCoreEquiv pairedSingletonMatrix := by
  funext receiver owner
  simp [normalPlayerMatrix, principalMatrix, reindexMatrix,
    pairedCoreEquiv]

private theorem pairedSingletonMatrix_normal_standardQ :
    IsStandardQMatrix (normalPlayerMatrix pairedSingletonMatrix) := by
  rw [pairedNormalPlayerMatrix_eq_reindex]
  exact isStandardQMatrix_reindexMatrix pairedCoreEquiv
    pairedSingletonMatrix pairedSingletonMatrix_standardQ

private theorem pairedSingletonMatrix_normal_noHomogeneous :
    ¬ HasHomogeneousSimplexSolution
      (normalPlayerMatrix pairedSingletonMatrix) := by
  rw [pairedNormalPlayerMatrix_eq_reindex]
  intro h
  exact pairedSingletonMatrix_noHomogeneous
    ((singletonLCPFeasible_reindexMatrix_iff pairedCoreEquiv
      pairedSingletonMatrix).mp h)

theorem normalizedSoloMatrix_stationaryCompletion :
    normalizedSoloMatrix stationaryCompletionReward = pairedSingletonMatrix := by
  funext who owner
  rw [normalizedSoloMatrix,
    normalized_singletonMatrix_eq_quittingSingletonMatrix]
  exact stationaryCompletion_singletonMatrix who owner

theorem normalizedSoloMatrix_periodTwo :
    normalizedSoloMatrix periodTwoReward = pairedSingletonMatrix := by
  funext who owner
  rw [normalizedSoloMatrix,
    normalized_singletonMatrix_eq_quittingSingletonMatrix]
  exact periodTwo_singletonMatrix who owner

private theorem residualHardClass_of_normalizedSoloMatrix_eq
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (hmatrix : normalizedSoloMatrix reward = pairedSingletonMatrix) :
    ResidualHardClass reward := by
  refine
    { normal_nonempty := ?_
      no_homogeneous := ?_
      normal_standardQ := ?_
      not_full_projectiveQBar := ?_ }
  · rw [hmatrix]
    exact ⟨0, pairedSingletonMatrix_mem_normalCore 0⟩
  · change ¬ HasHomogeneousSimplexSolution
      (normalPlayerMatrix (normalizedSoloMatrix reward))
    rw [hmatrix]
    exact pairedSingletonMatrix_normal_noHomogeneous
  · change IsStandardQMatrix
      (normalPlayerMatrix (normalizedSoloMatrix reward))
    rw [hmatrix]
    exact pairedSingletonMatrix_normal_standardQ
  · rw [hmatrix]
    exact pairedSingletonMatrix_not_projectiveQBar

/-- The stationary completion belongs to the exact residual hard class of
the LCP gate. -/
theorem stationaryCompletion_residualHardClass :
    ResidualHardClass stationaryCompletionReward :=
  residualHardClass_of_normalizedSoloMatrix_eq
    stationaryCompletionReward normalizedSoloMatrix_stationaryCompletion

/-- The period-two completion belongs to the same residual hard class. -/
theorem periodTwo_residualHardClass :
    ResidualHardClass periodTwoReward :=
  residualHardClass_of_normalizedSoloMatrix_eq
    periodTwoReward normalizedSoloMatrix_periodTwo

/-- Residual-hard membership, a full four-player corrected core, and exact
stationary nonexistence do not imply counterexamplehood: the period-two
completion has all three properties and an exact uniform-equilibrium payoff. -/
theorem periodTwo_residualHard_fullCore_nonstationary_but_uniform :
    ResidualHardClass periodTwoReward ∧
      normalCore (normalizedSoloMatrix periodTwoReward) = Finset.univ ∧
      (∀ root : Player → PMF Bool,
        ¬ (quittingGame periodTwoReward).IsεAsymptoticNash
          (quittingTerminalPayoff periodTwoReward) 0
          (quittingStationaryProfile periodTwoReward root)) ∧
      (quittingGame periodTwoReward).IsUniformEquilibriumPayoff none
        oddValue := by
  refine ⟨periodTwo_residualHardClass, ?_, periodTwo_no_stationary_exactTerminalNash,
    periodTwo_isUniformEquilibriumPayoff⟩
  rw [normalizedSoloMatrix_periodTwo]
  exact pairedSingletonMatrix_normalCore_eq_univ

end FourPlayerPairedSingleton
end GameTheory
