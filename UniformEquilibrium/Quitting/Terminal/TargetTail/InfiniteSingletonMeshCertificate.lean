/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Terminal.TargetTail.InfiniteSingletonMeshSurvival

/-!
# Nonperiodic quit-error certificates from a fixed singleton-flow mesh

This file combines the interpolated singleton-root certificate with exact
survival transport.  At every microstage, policy evaluation and prescribed
Continue are exact; immediate Quit exceeds the interpolated value by at most
`D` times the micro-hazard.  A uniform local error cap therefore produces the
nonperiodic quit-error certificate consumed by the Snell supersolution
compiler.

The capstone is deliberately independent of the source of the coarse path.
Any viable bounded singleton-flow path whose hazards have one ceiling below
one and whose opponent clocks contract in fixed blocks yields a uniform-
equilibrium payoff.  Essential APS is one producer of these hypotheses, but
is not part of the compiler's statement.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
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
def quittingUniformMesh_quitErrorCertificate
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
            simpa [quittingUniformMeshMass, add_comm] using
              add_le_add_left herror
                (quittingUniformMeshValue reward owner mass value m time who)
  · intro time who
    dsimp only [roots, microValue, hmassLe]
    exact (hlocal time).2.1 who

/-- **Uniform payoff from a contracted singleton-flow path.**  A bounded
viable singleton-flow path compiles to a uniform-equilibrium payoff whenever
its coarse hazards share a ceiling strictly below one and its playerwise
opponent-survival clocks contract uniformly in fixed blocks.

The theorem is source-agnostic: the path need not be periodic or arise from an
essential-APS fixed family.  The collision-surplus constant `D` is exposed so
consumers may use a sharper local bound than the generic `2 * bound`. -/
theorem isUniformEquilibriumPayoff_of_singletonFlow_uniformHazard
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ℕ → ι) (mass : ℕ → ℝ) (value : ℕ → Payoff ι)
    {K : ℕ} (hK : 0 < K)
    (hmass0 : ∀ time, 0 ≤ mass time)
    {pStar : ℝ} (hpStar1 : pStar < 1)
    (hmassCeiling : ∀ time, mass time ≤ pStar)
    (harc : ∀ time,
      value time = quittingSingletonArcPayoff (mass time)
        (quittingSoloReward reward (owner time)) (value (time + 1)))
    (hactive : ∀ time,
      value time (owner time) =
        quittingSoloReward reward (owner time) (owner time))
    (hviable : ∀ time, QuittingEssentialAPSViable reward (value time))
    {D bound rho : ℝ}
    (hD : 0 ≤ D)
    (hcollision : ∀ active other, other ≠ active →
      max (quittingSingletonCollisionReward reward active other -
        quittingSoloReward reward other other) 0 ≤ D)
    (hvalueBound : ∀ time who, |value time who| ≤ bound)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (hblock : IsQuittingOpponentBlockContraction
      (quittingEssentialAPSSingletonRoots owner mass hmass0
        (fun time ↦ ((hmassCeiling time).trans_lt hpStar1).le)) K rho) :
    (quittingGame reward).IsUniformEquilibriumPayoff none (value 0) := by
  have hmass1 : ∀ time, mass time < 1 :=
    fun time ↦ (hmassCeiling time).trans_lt hpStar1
  have hpStar0 : 0 ≤ pStar :=
    (hmass0 0).trans (hmassCeiling 0)
  have hbound : 0 ≤ bound :=
    (abs_nonneg (reward (quittingSingletonTerminal (owner 0)) (owner 0))).trans
      (hreward (quittingSingletonTerminal (owner 0)) (owner 0))
  apply isUniformEquilibriumPayoff_of_arbitrarily_small_infinitePath_quitError
    reward (value 0) hbound hreward
  intro error herror
  obtain ⟨mesh, hmesh, hmeshError⟩ :=
    exists_uniform_quittingMeshScale hpStar0 hpStar1 hD herror
  have hlocalError : ∀ time,
      D * quittingMeshHazard (mass time) mesh ≤ error := by
    intro time
    exact hmeshError (mass time) (hmass0 time) (hmassCeiling time)
  exact ⟨quittingUniformMesh_quitErrorCertificate
    reward owner mass value hmesh hK hmass0 hmass1 harc hactive hviable
      hD hcollision hlocalError hvalueBound hrho0 hrho1 hblock⟩

end GameTheory
