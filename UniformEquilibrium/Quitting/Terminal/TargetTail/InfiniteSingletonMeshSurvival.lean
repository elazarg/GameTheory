/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Terminal.TargetTail.InfiniteSingletonMesh

/-!
# Survival transport through a fixed singleton-flow mesh

A fixed-width logarithmic subdivision is an exact deterministic time change of
the opponent-survival clocks.  Over one microblock the product of Continue
probabilities is the original coarse Continue probability.  Induction then
identifies survival over any whole number of microblocks, and transports every
coarse block-contraction certificate to the subdivided path.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem quittingUniformMeshOwner_block_add
    (owner : ℕ → ι) {m block offset : ℕ}
    (hm : 0 < m) (hoffset : offset < m) :
    quittingUniformMeshOwner owner m (block * m + offset) = owner block := by
  unfold quittingUniformMeshOwner
  rw [quittingUniformMeshCoarseTime_block_add hm hoffset]

@[simp] theorem quittingUniformMeshMass_block_add
    (mass : ℕ → ℝ) {m block offset : ℕ}
    (hm : 0 < m) (hoffset : offset < m) :
    quittingUniformMeshMass mass m (block * m + offset) =
      quittingMeshHazard (mass block) m := by
  unfold quittingUniformMeshMass
  rw [quittingUniformMeshCoarseTime_block_add hm hoffset]

omit [Fintype ι] in
/-- Stagewise opponent mass is constant throughout a subdivided coarse block. -/
theorem quittingEssentialAPSOpponentStageMass_uniformMesh_block_add
    (owner : ℕ → ι) (mass : ℕ → ℝ) (who : ι)
    {m block offset : ℕ} (hm : 0 < m) (hoffset : offset < m) :
    quittingEssentialAPSOpponentStageMass
        (quittingUniformMeshOwner owner m)
        (quittingUniformMeshMass mass m)
        who (block * m + offset) =
      if owner block = who then 0
      else quittingMeshHazard (mass block) m := by
  unfold quittingEssentialAPSOpponentStageMass
  rw [quittingUniformMeshOwner_block_add owner hm hoffset,
    quittingUniformMeshMass_block_add mass hm hoffset]

/-- One full microblock has exactly the same deleted-player survival as its
single coarse singleton root. -/
theorem quittingOpponentSurvivalWeight_uniformMesh_one_block
    (owner : ℕ → ι) (mass : ℕ → ℝ)
    (hmass0 : ∀ time, 0 ≤ mass time)
    (hmass1 : ∀ time, mass time ≤ 1)
    {m : ℕ} (hm : 0 < m) (who : ι) (block : ℕ) :
    quittingOpponentSurvivalWeight
        (quittingUniformMeshRoots owner mass m hmass0 hmass1)
        who (block * m) m =
      quittingOpponentSurvivalWeight
        (quittingEssentialAPSSingletonRoots owner mass hmass0 hmass1)
        who block 1 := by
  unfold quittingUniformMeshRoots
  rw [quittingOpponentSurvivalWeight_singletonRoots_eq,
    quittingOpponentSurvivalWeight_singletonRoots_eq]
  simp only [Finset.prod_range_one, Nat.add_zero]
  by_cases howner : owner block = who
  · calc
      (∏ offset ∈ Finset.range m,
          (1 - quittingEssentialAPSOpponentStageMass
            (quittingUniformMeshOwner owner m)
            (quittingUniformMeshMass mass m) who
            (block * m + offset))) =
          ∏ _offset ∈ Finset.range m, (1 - 0) := by
            apply Finset.prod_congr rfl
            intro offset hoffset
            rw [quittingEssentialAPSOpponentStageMass_uniformMesh_block_add
              owner mass who hm (Finset.mem_range.mp hoffset), if_pos howner]
      _ = 1 := by simp
      _ = 1 - quittingEssentialAPSOpponentStageMass
          owner mass who block := by
            simp [quittingEssentialAPSOpponentStageMass, howner]
  · calc
      (∏ offset ∈ Finset.range m,
          (1 - quittingEssentialAPSOpponentStageMass
            (quittingUniformMeshOwner owner m)
            (quittingUniformMeshMass mass m) who
            (block * m + offset))) =
          ∏ _offset ∈ Finset.range m,
            (1 - quittingMeshHazard (mass block) m) := by
              apply Finset.prod_congr rfl
              intro offset hoffset
              rw [quittingEssentialAPSOpponentStageMass_uniformMesh_block_add
                owner mass who hm (Finset.mem_range.mp hoffset), if_neg howner]
      _ = (1 - quittingMeshHazard (mass block) m) ^ m := by simp
      _ = 1 - mass block :=
        one_sub_quittingMeshHazard_pow (hmass1 block) hm
      _ = 1 - quittingEssentialAPSOpponentStageMass
          owner mass who block := by
            simp [quittingEssentialAPSOpponentStageMass, howner]

/-- Survival over `fuel` coarse stages is unchanged after replacing each stage
by one full microblock. -/
theorem quittingOpponentSurvivalWeight_uniformMesh_blocks
    (owner : ℕ → ι) (mass : ℕ → ℝ)
    (hmass0 : ∀ time, 0 ≤ mass time)
    (hmass1 : ∀ time, mass time ≤ 1)
    {m : ℕ} (hm : 0 < m) (who : ι) :
    ∀ start fuel,
      quittingOpponentSurvivalWeight
          (quittingUniformMeshRoots owner mass m hmass0 hmass1)
          who (start * m) (fuel * m) =
        quittingOpponentSurvivalWeight
          (quittingEssentialAPSSingletonRoots owner mass hmass0 hmass1)
          who start fuel := by
  intro start fuel
  induction fuel with
  | zero => simp [quittingOpponentSurvivalWeight]
  | succ fuel ih =>
      calc
        quittingOpponentSurvivalWeight
            (quittingUniformMeshRoots owner mass m hmass0 hmass1)
            who (start * m) (fuel.succ * m) =
          quittingOpponentSurvivalWeight
              (quittingUniformMeshRoots owner mass m hmass0 hmass1)
              who (start * m) (fuel * m) *
            quittingOpponentSurvivalWeight
              (quittingUniformMeshRoots owner mass m hmass0 hmass1)
              who ((start + fuel) * m) m := by
                rw [Nat.succ_mul, quittingOpponentSurvivalWeight_add]
                congr 2
                exact (Nat.add_mul start fuel m).symm
        _ = quittingOpponentSurvivalWeight
              (quittingEssentialAPSSingletonRoots owner mass hmass0 hmass1)
              who start fuel *
            quittingOpponentSurvivalWeight
              (quittingUniformMeshRoots owner mass m hmass0 hmass1)
              who ((start + fuel) * m) m := by rw [ih]
        _ = quittingOpponentSurvivalWeight
              (quittingEssentialAPSSingletonRoots owner mass hmass0 hmass1)
              who start fuel *
            quittingOpponentSurvivalWeight
              (quittingEssentialAPSSingletonRoots owner mass hmass0 hmass1)
              who (start + fuel) 1 := by
                rw [quittingOpponentSurvivalWeight_uniformMesh_one_block
                  owner mass hmass0 hmass1 hm who (start + fuel)]
        _ = quittingOpponentSurvivalWeight
            (quittingEssentialAPSSingletonRoots owner mass hmass0 hmass1)
            who start fuel.succ := by
              rw [show fuel.succ = fuel + 1 by omega,
                quittingOpponentSurvivalWeight_add]

/-- Uniform block contraction survives fixed-width logarithmic subdivision;
the block length is multiplied by the mesh width and the contraction factor is
unchanged. -/
theorem isQuittingOpponentBlockContraction_uniformMesh
    (owner : ℕ → ι) (mass : ℕ → ℝ)
    (hmass0 : ∀ time, 0 ≤ mass time)
    (hmass1 : ∀ time, mass time ≤ 1)
    {m K : ℕ} (hm : 0 < m) {rho : ℝ}
    (hblock : IsQuittingOpponentBlockContraction
      (quittingEssentialAPSSingletonRoots owner mass hmass0 hmass1)
      K rho) :
    IsQuittingOpponentBlockContraction
      (quittingUniformMeshRoots owner mass m hmass0 hmass1)
      (K * m) rho := by
  intro block who
  have htransport := quittingOpponentSurvivalWeight_uniformMesh_blocks
    owner mass hmass0 hmass1 hm who (block * K) K
  have hstart : block * (K * m) = (block * K) * m := by ring
  rw [hstart, htransport]
  exact hblock block who

/-- Every arbitrary-start opponent-survival tail of the subdivided path tends
to zero whenever the coarse path has uniform block contraction. -/
theorem tendsto_zero_quittingOpponentSurvivalWeight_uniformMesh
    (owner : ℕ → ι) (mass : ℕ → ℝ)
    (hmass0 : ∀ time, 0 ≤ mass time)
    (hmass1 : ∀ time, mass time ≤ 1)
    {m K : ℕ} (hm : 0 < m) (hK : 0 < K) {rho : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (hblock : IsQuittingOpponentBlockContraction
      (quittingEssentialAPSSingletonRoots owner mass hmass0 hmass1)
      K rho)
    (who : ι) (start : ℕ) :
    Tendsto
      (quittingOpponentSurvivalWeight
        (quittingUniformMeshRoots owner mass m hmass0 hmass1) who start)
      atTop (nhds 0) := by
  exact tendsto_zero_quittingOpponentSurvivalWeight_of_blockContraction
    (quittingUniformMeshRoots owner mass m hmass0 hmass1)
    (Nat.mul_pos hK hm)
    (isQuittingOpponentBlockContraction_uniformMesh
      owner mass hmass0 hmass1 hm hblock)
    hrho0 hrho1 who start

end GameTheory
