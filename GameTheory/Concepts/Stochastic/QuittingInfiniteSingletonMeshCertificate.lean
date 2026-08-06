/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingInfiniteSingletonMeshSurvival

/-!
# Nonperiodic quit-error certificates from a fixed singleton-flow mesh

This file combines the interpolated singleton-root certificate with exact
survival transport.  At every microstage, policy evaluation and prescribed
Continue are exact; immediate Quit exceeds the interpolated value by at most
`D` times the micro-hazard.  A uniform local error cap therefore produces the
nonperiodic quit-error certificate consumed by the Snell supersolution
compiler.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Every terminal reward bound gives the elementary `2 * bound` bound on the
positive collision surplus at a singleton root. -/
theorem quittingSingletonCollisionSurplus_le_two_mul_bound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (owner other : ι) :
    max (quittingSingletonCollisionReward reward owner other -
        quittingSoloReward reward other other) 0 ≤ 2 * bound := by
  have hcollision :
      |quittingSingletonCollisionReward reward owner other| ≤ bound := by
    simpa [quittingSingletonCollisionReward] using
      hreward ⟨{owner, other}, by simp⟩ other
  have hsolo : |quittingSoloReward reward other other| ≤ bound := by
    simpa [quittingSoloReward, quittingSingletonTerminal] using
      hreward (quittingSingletonTerminal other) other
  rw [abs_le] at hcollision hsolo
  exact max_le (by linarith) (by linarith)

/-- Every microstage of a subdivided viable singleton arc supplies exact policy
transport, exact prescribed Continue, and the expected local Quit-error cap. -/
theorem quittingUniformMesh_local_certificate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ℕ → ι) (mass : ℕ → ℝ) (value : ℕ → Payoff ι)
    {m : ℕ} (hm : 0 < m)
    (hmass0 : ∀ time, 0 ≤ mass time)
    (hmass1 : ∀ time, mass time < 1)
    (harc : ∀ time,
      value time = quittingSingletonArcPayoff (mass time)
        (quittingSoloReward reward (owner time)) (value (time + 1)))
    (hactive : ∀ time,
      value time (owner time) =
        quittingSoloReward reward (owner time) (owner time))
    (hviable : ∀ time, QuittingEssentialAPSViable reward (value time))
    {D : ℝ} (hD : 0 ≤ D)
    (hcollision : ∀ active other, other ≠ active →
      max (quittingSingletonCollisionReward reward active other -
        quittingSoloReward reward other other) 0 ≤ D)
    (time : ℕ) :
    let roots := quittingUniformMeshRoots owner mass m hmass0
      (fun coarse ↦ (hmass1 coarse).le)
    let microValue := quittingUniformMeshValue reward owner mass value m
    microValue time = quittingRootSuccessorPayoff reward
        (microValue (time + 1)) (roots time) ∧
      (∀ who,
        quittingStationaryFixedOpponentsContinueReward reward
              (roots time) who +
            quittingStationaryFixedOpponentsContinueMass
                (roots time) who * microValue (time + 1) who =
          microValue time who) ∧
      ∀ who,
        quittingStationaryFixedOpponentsQuitValue reward
            (roots time) who ≤
          microValue time who +
            D * quittingUniformMeshMass mass m time := by
  dsimp only
  let coarse := quittingUniformMeshCoarseTime m time
  let offset := quittingUniformMeshOffset m time
  have hcurrent :
      quittingUniformMeshValue reward owner mass value m time =
        quittingMeshPayoffInterpolant
          (quittingSoloReward reward (owner coarse))
          (value coarse)
          (1 - quittingMeshHazard (mass coarse) m) offset := by
    rfl
  have hnext :
      quittingUniformMeshValue reward owner mass value m (time + 1) =
        quittingMeshPayoffInterpolant
          (quittingSoloReward reward (owner coarse))
          (value coarse)
          (1 - quittingMeshHazard (mass coarse) m) (offset + 1) := by
    exact quittingUniformMeshValue_succ
      reward owner mass value hm hmass1 harc time
  have hroot :
      quittingUniformMeshRoots owner mass m hmass0
          (fun coarse ↦ (hmass1 coarse).le) time =
        quittingSoloStationaryRoot (owner coarse)
          (quittingMeshHazardCoin (mass coarse) m
            (hmass0 coarse) (hmass1 coarse)) := by
    rfl
  have hsolo : ∀ who,
      quittingSoloReward reward who who ≤
        quittingMeshPayoffInterpolant
          (quittingSoloReward reward (owner coarse))
          (value coarse)
          (1 - quittingMeshHazard (mass coarse) m) offset who := by
    intro who
    have hmicroViable := quittingUniformMeshValue_viable
      reward owner mass value hm hmass0 hmass1 harc hviable time who
    rw [hcurrent] at hmicroViable
    simpa only [quittingSoloBaseline_apply] using hmicroViable
  have hlocal := singletonMeshStationaryRoot_interpolant_certificate
    reward (owner coarse) m (hmass0 coarse) (hmass1 coarse)
      (quittingSoloReward reward (owner coarse)) (value coarse) offset
      hD rfl (hactive coarse) hsolo (hcollision (owner coarse))
  rw [hcurrent, hnext, hroot]
  simpa [quittingUniformMeshMass, coarse] using hlocal

/-- **Fixed-mesh nonperiodic certificate.**  A bounded viable coarse path with
opponent block contraction and a uniform micro-hazard error cap compiles to a
bounded nonperiodic quit-error certificate delivering its initial value. -/
theorem quittingUniformMesh_quitErrorCertificate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ℕ → ι) (mass : ℕ → ℝ) (value : ℕ → Payoff ι)
    {m K : ℕ} (hm : 0 < m) (hK : 0 < K)
    (hmass0 : ∀ time, 0 ≤ mass time)
    (hmass1 : ∀ time, mass time < 1)
    (harc : ∀ time,
      value time = quittingSingletonArcPayoff (mass time)
        (quittingSoloReward reward (owner time)) (value (time + 1)))
    (hactive : ∀ time,
      value time (owner time) =
        quittingSoloReward reward (owner time) (owner time))
    (hviable : ∀ time, QuittingEssentialAPSViable reward (value time))
    {D error bound rho : ℝ}
    (hD : 0 ≤ D)
    (hcollision : ∀ active other, other ≠ active →
      max (quittingSingletonCollisionReward reward active other -
        quittingSoloReward reward other other) 0 ≤ D)
    (hlocalError : ∀ coarse,
      D * quittingMeshHazard (mass coarse) m ≤ error)
    (hvalueBound : ∀ time who, |value time who| ≤ bound)
    (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (hblock : IsQuittingOpponentBlockContraction
      (quittingEssentialAPSSingletonRoots owner mass hmass0
        (fun time ↦ (hmass1 time).le)) K rho) :
    QuittingInfinitePathQuitErrorCertificate
      reward (value 0) error bound := by
  let hmassLe : ∀ time, mass time ≤ 1 :=
    fun time ↦ (hmass1 time).le
  let roots := quittingUniformMeshRoots owner mass m hmass0 hmassLe
  let microValue := quittingUniformMeshValue reward owner mass value m
  have hlocal := quittingUniformMesh_local_certificate
    reward owner mass value hm hmass0 hmass1 harc hactive hviable
      hD hcollision
  refine
    { roots := roots
      value := microValue
      value_zero := ?_
      survival := ?_
      value_bound := ?_
      policy := ?_
      quit_le := ?_
      continue_eq := ?_ }
  · dsimp only [microValue]
    simpa using
      (quittingUniformMeshValue_block
        reward owner mass value hm 0)
  · intro who start
    dsimp only [roots, hmassLe]
    exact tendsto_zero_quittingOpponentSurvivalWeight_uniformMesh
      owner mass hmass0 (fun time ↦ (hmass1 time).le)
        hm hK hrho0 hrho1 hblock who start
  · dsimp only [microValue]
    exact quittingUniformMeshValue_bound
      reward owner mass value hm hmass0 hmass1 harc hvalueBound
  · intro time
    dsimp only [roots, microValue, hmassLe]
    exact (hlocal time).1
  · intro time who
    have hquit := (hlocal time).2.2 who
    have herror := hlocalError
      (quittingUniformMeshCoarseTime m time)
    dsimp only [roots, microValue, hmassLe] at hquit ⊢
    calc
      quittingStationaryFixedOpponentsQuitValue reward
          (quittingUniformMeshRoots owner mass m hmass0
            (fun coarse ↦ (hmass1 coarse).le) time) who ≤
        quittingUniformMeshValue reward owner mass value m time who +
          D * quittingUniformMeshMass mass m time := hquit
      _ ≤ quittingUniformMeshValue reward owner mass value m time who +
          error := by
            apply add_le_add_left
            simpa [quittingUniformMeshMass] using herror
  · intro time who
    dsimp only [roots, microValue, hmassLe]
    exact (hlocal time).2.1 who

end GameTheory
