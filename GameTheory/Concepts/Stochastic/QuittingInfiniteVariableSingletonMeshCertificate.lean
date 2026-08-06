/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingInfiniteVariableSingletonMeshSurvival
import GameTheory.Concepts.Stochastic.QuittingInfiniteSingletonMeshCertificate

/-!
# Adaptive certificates for proper nonperiodic singleton paths

Each proper coarse hazard chooses its own finite logarithmic subdivision width.
Exact policy and Continue transport survive at every microstage, while the
immediate-Quit excess is uniformly small. Exact survival transport and the
nonperiodic Snell supersolution compiler then yield uniform-equilibrium
payoffs without a uniform hazard ceiling or a geometric contraction rate.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Local and global adaptive-mesh certificates -/

/-- Every microstage of a variable-width mesh has exact policy and Continue
transport and local Quit excess bounded by `D` times its micro-hazard. -/
theorem quittingVariableMesh_local_certificate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ℕ → ι) (mass : ℕ → ℝ) (value : ℕ → Payoff ι)
    (mesh : ℕ → ℕ) (hmesh : ∀ coarse, 0 < mesh coarse)
    (hmass0 : ∀ time, 0 ≤ mass time)
    (hmass1 : ∀ time, mass time < 1)
    (harc : ∀ time,
      value time = quittingSingletonArcPayoff (mass time)
        (quittingSoloReward reward (owner time)) (value (time + 1)))
    (hactive : ∀ time,
      value time (owner time) =
        quittingSoloReward reward (owner time) (owner time))
    (hsolo : ∀ time who, quittingSoloReward reward who who ≤ value time who)
    {D : ℝ} (hD : 0 ≤ D)
    (hcollision : ∀ active other, other ≠ active →
      max (quittingSingletonCollisionReward reward active other -
        quittingSoloReward reward other other) 0 ≤ D)
    (time : ℕ) :
    let roots := quittingVariableMeshRoots owner mass mesh hmass0
      (fun coarse ↦ (hmass1 coarse).le)
    let microValue := quittingVariableMeshValue reward owner mass value mesh
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
            D * quittingVariableMeshMass mass mesh time := by
  dsimp only
  let coarse := quittingVariableMeshCoarseTime mesh time
  let offset := quittingVariableMeshOffset mesh time
  have hcurrent :
      quittingVariableMeshValue reward owner mass value mesh time =
        quittingMeshPayoffInterpolant
          (quittingSoloReward reward (owner coarse))
          (value coarse)
          (1 - quittingMeshHazard (mass coarse) (mesh coarse)) offset := by
    rfl
  have hnext :
      quittingVariableMeshValue reward owner mass value mesh (time + 1) =
        quittingMeshPayoffInterpolant
          (quittingSoloReward reward (owner coarse))
          (value coarse)
          (1 - quittingMeshHazard (mass coarse) (mesh coarse)) (offset + 1) := by
    exact quittingVariableMeshValue_succ
      reward owner mass value mesh hmesh hmass1 harc time
  have hroot :
      quittingVariableMeshRoots owner mass mesh hmass0
          (fun coarse ↦ (hmass1 coarse).le) time =
        quittingSoloStationaryRoot (owner coarse)
          (quittingMeshHazardCoin (mass coarse) (mesh coarse)
            (hmass0 coarse) (hmass1 coarse)) := by
    rfl
  have hsolo : ∀ who,
      quittingSoloReward reward who who ≤
        quittingMeshPayoffInterpolant
          (quittingSoloReward reward (owner coarse))
          (value coarse)
          (1 - quittingMeshHazard (mass coarse) (mesh coarse)) offset who := by
    intro who
    exact quittingVariableMeshValue_solo_floor
      reward owner mass value mesh hmesh hmass0 hmass1 harc hsolo time who
  have hlocal := singletonMeshStationaryRoot_interpolant_certificate
    reward (owner coarse) (mesh coarse) (hmass0 coarse) (hmass1 coarse)
      (quittingSoloReward reward (owner coarse)) (value coarse) offset
      hD rfl (hactive coarse) hsolo (hcollision (owner coarse))
  rw [hcurrent, hnext, hroot]
  simpa [quittingVariableMeshMass, coarse] using hlocal

/-- A supplied positive variable mesh with a uniform local error cap compiles a
bounded proper singleton path with vanishing coarse survival. -/
def quittingVariableMesh_quitErrorCertificate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ℕ → ι) (mass : ℕ → ℝ) (value : ℕ → Payoff ι)
    (mesh : ℕ → ℕ) (hmesh : ∀ coarse, 0 < mesh coarse)
    (hmass0 : ∀ time, 0 ≤ mass time)
    (hmass1 : ∀ time, mass time < 1)
    (harc : ∀ time,
      value time = quittingSingletonArcPayoff (mass time)
        (quittingSoloReward reward (owner time)) (value (time + 1)))
    (hactive : ∀ time,
      value time (owner time) =
        quittingSoloReward reward (owner time) (owner time))
    (hsolo : ∀ time who, quittingSoloReward reward who who ≤ value time who)
    {D error bound : ℝ}
    (hD : 0 ≤ D)
    (hcollision : ∀ active other, other ≠ active →
      max (quittingSingletonCollisionReward reward active other -
        quittingSoloReward reward other other) 0 ≤ D)
    (hlocalError : ∀ coarse,
      D * quittingMeshHazard (mass coarse) (mesh coarse) ≤ error)
    (hvalueBound : ∀ time who, |value time who| ≤ bound)
    (hcoarse : ∀ who start,
      Tendsto
        (quittingOpponentSurvivalWeight
          (quittingEssentialAPSSingletonRoots owner mass hmass0
            (fun time ↦ (hmass1 time).le)) who start)
        atTop (nhds 0)) :
    QuittingInfinitePathQuitErrorCertificate
      reward (value 0) error bound := by
  let hmassLe : ∀ time, mass time ≤ 1 :=
    fun time ↦ (hmass1 time).le
  let roots := quittingVariableMeshRoots owner mass mesh hmass0 hmassLe
  let microValue := quittingVariableMeshValue reward owner mass value mesh
  have hlocal := quittingVariableMesh_local_certificate
    reward owner mass value mesh hmesh hmass0 hmass1 harc hactive hsolo
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
      (quittingVariableMeshValue_boundary
        reward owner mass value mesh hmesh 0)
  · intro who start
    dsimp only [roots, hmassLe]
    exact tendsto_zero_quittingOpponentSurvivalWeight_variableMesh
      owner mass mesh hmesh hmass0 (fun time ↦ (hmass1 time).le)
        hcoarse who start
  · dsimp only [microValue]
    exact quittingVariableMeshValue_bound
      reward owner mass value mesh hmesh hmass0 hmass1 harc hvalueBound
  · intro time
    dsimp only [roots, microValue, hmassLe]
    exact (hlocal time).1
  · intro time who
    have hquit := (hlocal time).2.2 who
    have herror := hlocalError
      (quittingVariableMeshCoarseTime mesh time)
    dsimp only [roots, microValue, hmassLe] at hquit ⊢
    calc
      quittingStationaryFixedOpponentsQuitValue reward
          (quittingVariableMeshRoots owner mass mesh hmass0
            (fun coarse ↦ (hmass1 coarse).le) time) who ≤
        quittingVariableMeshValue reward owner mass value mesh time who +
          D * quittingVariableMeshMass mass mesh time := hquit
      _ ≤ quittingVariableMeshValue reward owner mass value mesh time who +
          error := by
            change quittingVariableMeshValue reward owner mass value mesh time who +
              D * quittingMeshHazard
                (mass (quittingVariableMeshCoarseTime mesh time))
                (mesh (quittingVariableMeshCoarseTime mesh time)) ≤ _
            simpa [add_comm] using
              add_le_add_left herror
                (quittingVariableMeshValue reward owner mass value mesh time who)
  · intro time who
    dsimp only [roots, microValue, hmassLe]
    exact (hlocal time).2.1 who

/-- Every individual proper coarse hazard admits a positive mesh width meeting
one requested local error cap. -/
theorem exists_quittingMeshScale_pointwise
    {p D error : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1)
    (hD : 0 ≤ D) (herror : 0 < error) :
    ∃ m : ℕ, 0 < m ∧ D * quittingMeshHazard p m ≤ error := by
  obtain ⟨m, hm, hbound⟩ :=
    exists_uniform_quittingMeshScale hp0 hp1 hD herror
  exact ⟨m, hm, hbound p hp0 le_rfl⟩

/-- Pointwise Archimedean mesh selection produces a variable-mesh quit-error
certificate with no uniform upper bound on the coarse hazards. -/
theorem exists_quittingVariableMesh_quitErrorCertificate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ℕ → ι) (mass : ℕ → ℝ) (value : ℕ → Payoff ι)
    (hmass0 : ∀ time, 0 ≤ mass time)
    (hmass1 : ∀ time, mass time < 1)
    (harc : ∀ time,
      value time = quittingSingletonArcPayoff (mass time)
        (quittingSoloReward reward (owner time)) (value (time + 1)))
    (hactive : ∀ time,
      value time (owner time) =
        quittingSoloReward reward (owner time) (owner time))
    (hsolo : ∀ time who, quittingSoloReward reward who who ≤ value time who)
    {D error bound : ℝ}
    (hD : 0 ≤ D) (herror : 0 < error)
    (hcollision : ∀ active other, other ≠ active →
      max (quittingSingletonCollisionReward reward active other -
        quittingSoloReward reward other other) 0 ≤ D)
    (hvalueBound : ∀ time who, |value time who| ≤ bound)
    (hcoarse : ∀ who start,
      Tendsto
        (quittingOpponentSurvivalWeight
          (quittingEssentialAPSSingletonRoots owner mass hmass0
            (fun time ↦ (hmass1 time).le)) who start)
        atTop (nhds 0)) :
    Nonempty (QuittingInfinitePathQuitErrorCertificate
      reward (value 0) error bound) := by
  classical
  have hlocal : ∀ coarse, ∃ m : ℕ, 0 < m ∧
      D * quittingMeshHazard (mass coarse) m ≤ error := by
    intro coarse
    exact exists_quittingMeshScale_pointwise
      (hmass0 coarse) (hmass1 coarse) hD herror
  choose mesh hmesh hlocalError using hlocal
  exact ⟨quittingVariableMesh_quitErrorCertificate
    reward owner mass value mesh hmesh hmass0 hmass1 harc hactive hsolo
      hD hcollision hlocalError hvalueBound hcoarse⟩

/-- **Adaptive nonperiodic singleton-path compiler.** Every bounded viable
proper singleton path with vanishing coarse opponent-survival tails delivers
its initial value as a uniform-equilibrium payoff. Coarse hazards may approach
one arbitrarily fast and the selected mesh widths may be unbounded. -/
theorem isUniformEquilibriumPayoff_of_proper_infiniteSingletonPath
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ℕ → ι) (mass : ℕ → ℝ) (value : ℕ → Payoff ι)
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (hmass0 : ∀ time, 0 ≤ mass time)
    (hmass1 : ∀ time, mass time < 1)
    (harc : ∀ time,
      value time = quittingSingletonArcPayoff (mass time)
        (quittingSoloReward reward (owner time)) (value (time + 1)))
    (hactive : ∀ time,
      value time (owner time) =
        quittingSoloReward reward (owner time) (owner time))
    (hsolo : ∀ time who, quittingSoloReward reward who who ≤ value time who)
    (hvalueBound : ∀ time who, |value time who| ≤ bound)
    (hcoarse : ∀ who start,
      Tendsto
        (quittingOpponentSurvivalWeight
          (quittingEssentialAPSSingletonRoots owner mass hmass0
            (fun time ↦ (hmass1 time).le)) who start)
        atTop (nhds 0)) :
    (quittingGame reward).IsUniformEquilibriumPayoff none (value 0) := by
  have hD : 0 ≤ 2 * bound := by positivity
  have hcollision : ∀ active other, other ≠ active →
      max (quittingSingletonCollisionReward reward active other -
        quittingSoloReward reward other other) 0 ≤ 2 * bound := by
    intro active other _hne
    exact quittingSingletonCollisionSurplus_le_two_mul_bound
      reward hbound hreward active other
  apply isUniformEquilibriumPayoff_of_arbitrarily_small_infinitePath_quitError
    reward (value 0) hbound hreward
  intro error herror
  exact exists_quittingVariableMesh_quitErrorCertificate
    reward owner mass value hmass0 hmass1 harc hactive hsolo
      hD herror hcollision hvalueBound hcoarse

/-- Adaptive nonperiodic singleton-path compiler whose survival input is
needed only from the initial coarse time. Proper hazards make every finite
deleted-player prefix strictly positive, so exact product factorization
recovers the shifted survival tails required by the mesh compiler. -/
theorem isUniformEquilibriumPayoff_of_proper_infiniteSingletonPath_of_initialSurvival
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ℕ → ι) (mass : ℕ → ℝ) (value : ℕ → Payoff ι)
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (hmass0 : ∀ time, 0 ≤ mass time)
    (hmass1 : ∀ time, mass time < 1)
    (harc : ∀ time,
      value time = quittingSingletonArcPayoff (mass time)
        (quittingSoloReward reward (owner time)) (value (time + 1)))
    (hactive : ∀ time,
      value time (owner time) =
        quittingSoloReward reward (owner time) (owner time))
    (hsolo : ∀ time who, quittingSoloReward reward who who ≤ value time who)
    (hvalueBound : ∀ time who, |value time who| ≤ bound)
    (hcoarseZero : ∀ who,
      Tendsto
        (quittingOpponentSurvivalWeight
          (quittingEssentialAPSSingletonRoots owner mass hmass0
            (fun time ↦ (hmass1 time).le)) who 0)
        atTop (nhds 0)) :
    (quittingGame reward).IsUniformEquilibriumPayoff none (value 0) := by
  apply isUniformEquilibriumPayoff_of_proper_infiniteSingletonPath
    reward owner mass value hbound hreward hmass0 hmass1 harc hactive hsolo
      hvalueBound
  exact
    (tendsto_zero_quittingOpponentSurvivalWeight_singletonRoots_tail_iff_zero
      owner mass hmass0 hmass1).2 hcoarseZero

/-- Source-agnostic proper singleton-path compiler with an exposed local
collision constant. -/
theorem isUniformEquilibriumPayoff_of_proper_infiniteSingletonPath_of_collisionBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ℕ → ι) (mass : ℕ → ℝ) (value : ℕ → Payoff ι)
    {D bound : ℝ} (hbound : 0 ≤ bound) (hD : 0 ≤ D)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (hmass0 : ∀ time, 0 ≤ mass time) (hmass1 : ∀ time, mass time < 1)
    (harc : ∀ time, value time = quittingSingletonArcPayoff (mass time)
      (quittingSoloReward reward (owner time)) (value (time + 1)))
    (hactive : ∀ time, value time (owner time) =
      quittingSoloReward reward (owner time) (owner time))
    (hsolo : ∀ time who, quittingSoloReward reward who who ≤ value time who)
    (hcollision : ∀ active other, other ≠ active →
      max (quittingSingletonCollisionReward reward active other -
        quittingSoloReward reward other other) 0 ≤ D)
    (hvalueBound : ∀ time who, |value time who| ≤ bound)
    (hcoarse : ∀ who start, Tendsto
      (quittingOpponentSurvivalWeight
        (quittingEssentialAPSSingletonRoots owner mass hmass0
          (fun time ↦ (hmass1 time).le)) who start) atTop (nhds 0)) :
    (quittingGame reward).IsUniformEquilibriumPayoff none (value 0) := by
  apply isUniformEquilibriumPayoff_of_arbitrarily_small_infinitePath_quitError
    reward (value 0) hbound hreward
  intro error herror
  exact exists_quittingVariableMesh_quitErrorCertificate
    reward owner mass value hmass0 hmass1 harc hactive hsolo hD herror
      hcollision hvalueBound hcoarse

/-- Source-agnostic proper singleton-path compiler whose survival input is
needed only from the initial coarse time. Proper hazards make every finite
deleted-player prefix strictly positive, so exact product factorization
recovers the all-start survival tails used by the adaptive mesh. -/
theorem
    isUniformEquilibriumPayoff_of_proper_infiniteSingletonPath_of_collisionBound_of_initialSurvival
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ℕ → ι) (mass : ℕ → ℝ) (value : ℕ → Payoff ι)
    {D bound : ℝ} (hbound : 0 ≤ bound) (hD : 0 ≤ D)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (hmass0 : ∀ time, 0 ≤ mass time) (hmass1 : ∀ time, mass time < 1)
    (harc : ∀ time, value time = quittingSingletonArcPayoff (mass time)
      (quittingSoloReward reward (owner time)) (value (time + 1)))
    (hactive : ∀ time, value time (owner time) =
      quittingSoloReward reward (owner time) (owner time))
    (hsolo : ∀ time who, quittingSoloReward reward who who ≤ value time who)
    (hcollision : ∀ active other, other ≠ active →
      max (quittingSingletonCollisionReward reward active other -
        quittingSoloReward reward other other) 0 ≤ D)
    (hvalueBound : ∀ time who, |value time who| ≤ bound)
    (hcoarseZero : ∀ who, Tendsto
      (quittingOpponentSurvivalWeight
        (quittingEssentialAPSSingletonRoots owner mass hmass0
          (fun time ↦ (hmass1 time).le)) who 0) atTop (nhds 0)) :
    (quittingGame reward).IsUniformEquilibriumPayoff none (value 0) := by
  apply
    isUniformEquilibriumPayoff_of_proper_infiniteSingletonPath_of_collisionBound
      reward owner mass value hbound hD hreward hmass0 hmass1 harc hactive
        hsolo hcollision hvalueBound
  exact
    (tendsto_zero_quittingOpponentSurvivalWeight_singletonRoots_tail_iff_zero
      owner mass hmass0 hmass1).2 hcoarseZero

/-- **Divergent-mass Flesch-path compiler.** A bounded viable proper Flesch
singleton path whose total absorption mass diverges on every tail already
delivers its initial value as a uniform-equilibrium payoff. Bounded drift
supplies playerwise survival decay and the adaptive clock supplies arbitrarily
fine local deviation control. -/
theorem
    isUniformEquilibriumPayoff_of_proper_flesch_infiniteSingletonPath_of_windowMass_atTop
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (successor : ι → ι) (owner : ℕ → ι)
    (mass : ℕ → ℝ) (value : ℕ → Payoff ι)
    {gap bound : ℝ}
    (hgapPos : 0 < gap) (hbound : 0 ≤ bound)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (hmass0 : ∀ time, 0 ≤ mass time)
    (hmass1 : ∀ time, mass time < 1)
    (harc : ∀ time,
      value time = quittingSingletonArcPayoff (mass time)
        (quittingSoloReward reward (owner time)) (value (time + 1)))
    (hactive : ∀ time,
      value time (owner time) =
        quittingSoloReward reward (owner time) (owner time))
    (hownerNext : ∀ time,
      owner (time + 1) = successor (owner time))
    (hgap : ∀ player,
      gap ≤ quittingSoloReward reward player (successor player) -
        quittingSoloReward reward (successor player) (successor player))
    (hsolo : ∀ time who, quittingSoloReward reward who who ≤ value time who)
    (hvalueBound : ∀ time who, |value time who| ≤ bound)
    (htotal :
      Tendsto (quittingEssentialAPSWindowMass mass 0) atTop atTop) :
    (quittingGame reward).IsUniformEquilibriumPayoff none (value 0) := by
  have hrootBound : ∀ time who,
      |quittingSoloReward reward (owner time) who| ≤ bound := by
    intro time who
    simpa [quittingSoloReward, quittingSingletonTerminal] using
      hreward (quittingSingletonTerminal (owner time)) who
  have htails :=
    tendsto_quittingEssentialAPSWindowMass_tail_atTop_of_zero mass htotal
  have hcoarse :=
    tendsto_zero_quittingOpponentSurvivalWeight_singletonRoots_of_windowMass_atTop
      reward successor owner mass value hgapPos hbound hmass0
        (fun time ↦ (hmass1 time).le) harc hactive hownerNext hgap
        hrootBound hvalueBound htails
  exact isUniformEquilibriumPayoff_of_proper_infiniteSingletonPath
    reward owner mass value hbound hreward hmass0 hmass1 harc hactive
      hsolo hvalueBound hcoarse

end GameTheory
