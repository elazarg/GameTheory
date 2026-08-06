/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingAdaptiveMeshSchedule
import GameTheory.Concepts.Stochastic.QuittingEssentialAPSOpponentContraction
import GameTheory.Concepts.Stochastic.QuittingSingletonStationaryRoot

/-!
# Adaptive nonperiodic singleton-flow meshes

Each coarse singleton arc receives its own positive subdivision count.  The
variable-block schedule flattens these microblocks into one ordinary root
sequence.  Every microstage has exact policy transport and exact prescribed
Continue.  Its only unilateral error is immediate Quit, bounded by the local
micro-hazard times a uniform collision-surplus bound.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Coarse block occupied by a flattened adaptive mesh time. -/
def quittingAdaptiveMeshBlock
    (count : ℕ → ℕ) (time : ℕ) : ℕ :=
  (quittingVariableBlockState count time).1

/-- Offset inside the coarse block occupied by a flattened adaptive mesh
time. -/
def quittingAdaptiveMeshOffset
    (count : ℕ → ℕ) (time : ℕ) : ℕ :=
  (quittingVariableBlockState count time).2

/-- Active owner at a flattened adaptive mesh time. -/
def quittingAdaptiveMeshOwner
    (owner : ℕ → ι) (count : ℕ → ℕ) (time : ℕ) : ι :=
  owner (quittingAdaptiveMeshBlock count time)

/-- Micro-hazard used at a flattened adaptive mesh time. -/
def quittingAdaptiveMeshHazard
    (mass : ℕ → ℝ) (count : ℕ → ℕ) (time : ℕ) : ℝ :=
  quittingMeshHazard
    (mass (quittingAdaptiveMeshBlock count time))
    (count (quittingAdaptiveMeshBlock count time))

/-- Interpolated payoff at a flattened adaptive mesh time. -/
def quittingAdaptiveMeshValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ℕ → ι) (mass : ℕ → ℝ) (value : ℕ → Payoff ι)
    (count : ℕ → ℕ) (time : ℕ) : Payoff ι :=
  let block := quittingAdaptiveMeshBlock count time
  quittingMeshPayoffInterpolant
    (quittingSoloReward reward (owner block)) (value block)
    (1 - quittingMeshHazard (mass block) (count block))
    (quittingAdaptiveMeshOffset count time)

/-- Product roots implementing the flattened adaptive mesh. -/
def quittingAdaptiveMeshRoots
    (owner : ℕ → ι) (mass : ℕ → ℝ) (count : ℕ → ℕ)
    (hmass0 : ∀ time, 0 ≤ mass time)
    (hmass1 : ∀ time, mass time ≤ 1) :
    ℕ → ι → PMF Bool :=
  quittingEssentialAPSSingletonRoots
    (quittingAdaptiveMeshOwner owner count)
    (quittingAdaptiveMeshHazard mass count)
    (fun time ↦ quittingMeshHazard_nonneg _
      (hmass0 (quittingAdaptiveMeshBlock count time))
      (hmass1 (quittingAdaptiveMeshBlock count time)))
    (fun time ↦ quittingMeshHazard_le_one _
      (hmass1 (quittingAdaptiveMeshBlock count time)))

@[simp] theorem quittingAdaptiveMeshBlock_zero
    (count : ℕ → ℕ) :
    quittingAdaptiveMeshBlock count 0 = 0 := rfl

@[simp] theorem quittingAdaptiveMeshOffset_zero
    (count : ℕ → ℕ) :
    quittingAdaptiveMeshOffset count 0 = 0 := rfl

@[simp] theorem quittingAdaptiveMeshValue_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ℕ → ι) (mass : ℕ → ℝ) (value : ℕ → Payoff ι)
    (count : ℕ → ℕ) :
    quittingAdaptiveMeshValue reward owner mass value count 0 = value 0 := by
  funext who
  simp [quittingAdaptiveMeshValue, quittingAdaptiveMeshBlock,
    quittingAdaptiveMeshOffset, quittingMeshPayoffInterpolant,
    quittingMeshInterpolant]

/-- Adaptive micro-hazards are nonnegative. -/
theorem quittingAdaptiveMeshHazard_nonneg
    (mass : ℕ → ℝ) (count : ℕ → ℕ)
    (hmass0 : ∀ time, 0 ≤ mass time)
    (hmass1 : ∀ time, mass time ≤ 1)
    (time : ℕ) :
    0 ≤ quittingAdaptiveMeshHazard mass count time :=
  quittingMeshHazard_nonneg _
    (hmass0 (quittingAdaptiveMeshBlock count time))
    (hmass1 (quittingAdaptiveMeshBlock count time))

/-- Adaptive micro-hazards are at most one. -/
theorem quittingAdaptiveMeshHazard_le_one
    (mass : ℕ → ℝ) (count : ℕ → ℕ)
    (hmass1 : ∀ time, mass time ≤ 1)
    (time : ℕ) :
    quittingAdaptiveMeshHazard mass count time ≤ 1 :=
  quittingMeshHazard_le_one _
    (hmass1 (quittingAdaptiveMeshBlock count time))

/-- Strictly subunit coarse hazards give strictly subunit adaptive
micro-hazards. -/
theorem quittingAdaptiveMeshHazard_lt_one
    (mass : ℕ → ℝ) (count : ℕ → ℕ)
    (hmass1 : ∀ time, mass time < 1)
    (time : ℕ) :
    quittingAdaptiveMeshHazard mass count time < 1 :=
  quittingMeshHazard_lt_one
    (hmass1 (quittingAdaptiveMeshBlock count time))
    (count (quittingAdaptiveMeshBlock count time))

/-- Upper-bound companion to
`le_quittingMeshPayoffInterpolant_of_arcEndpoints`.  Every microstage lies
coordinatewise below any upper bound shared by the two coarse endpoints. -/
theorem quittingMeshPayoffInterpolant_le_of_arcEndpoints
    {p : ℝ} {m : ℕ} (hp0 : 0 ≤ p) (hp1 : p < 1) (hm : 0 < m)
    {root start next upper : Payoff ι}
    (harc : start = quittingSingletonArcPayoff p root next)
    (hupperStart : ∀ who, start who ≤ upper who)
    (hupperNext : ∀ who, next who ≤ upper who)
    (k : ℕ) (hk : k ≤ m) (who : ι) :
    quittingMeshPayoffInterpolant root start
        (1 - quittingMeshHazard p m) k who ≤ upper who := by
  let q := 1 - quittingMeshHazard p m
  have hqpos : 0 < q := by
    dsimp only [q]
    rw [one_sub_quittingMeshHazard]
    exact Real.rpow_pos_of_pos (sub_pos.mpr hp1) _
  have hqle : q ≤ 1 := by
    dsimp only [q]
    have hhazard := quittingMeshHazard_nonneg m hp0 hp1.le
    linarith
  have hqpow : q ^ m = 1 - p := by
    dsimp only [q]
    exact one_sub_quittingMeshHazard_pow hp1.le hm
  have harcWho : start who =
      p * root who + (1 - p) * next who := by
    simpa [quittingSingletonArcPayoff] using congrFun harc who
  have hstart : start who =
      root who + q ^ m * (next who - root who) := by
    rw [hqpow, harcWho]
    ring
  have hform := quittingMeshInterpolant_eq_pow_sub
    hqpos.ne' hk hstart
  rw [quittingMeshPayoffInterpolant_apply, hform]
  have hpowerLower : q ^ m ≤ q ^ (m - k) :=
    pow_le_pow_of_le_one hqpos.le hqle (Nat.sub_le m k)
  have hpowerUpper : q ^ (m - k) ≤ 1 :=
    pow_le_one₀ hqpos.le hqle
  by_cases hdirection : 0 ≤ next who - root who
  · have hscaled := mul_le_mul_of_nonneg_right
      hpowerUpper hdirection
    calc
      root who + q ^ (m - k) * (next who - root who) ≤
          root who + 1 * (next who - root who) :=
        add_le_add (le_refl _) hscaled
      _ = next who := by ring
      _ ≤ upper who := hupperNext who
  · have hscaled := mul_le_mul_of_nonpos_right
      hpowerLower (le_of_not_ge hdirection)
    calc
      root who + q ^ (m - k) * (next who - root who) ≤
          root who + q ^ m * (next who - root who) :=
        add_le_add (le_refl _) hscaled
      _ = start who := hstart.symm
      _ ≤ upper who := hupperStart who

/-- The flattened schedule stays inside the selected coarse block and offset. -/
theorem quittingAdaptiveMeshBlock_offset_prefix_add
    (count : ℕ → ℕ) (hcount : ∀ block, 0 < count block)
    (block offset : ℕ) (hoffset : offset < count block) :
    quittingAdaptiveMeshBlock count
          (quittingVariableBlockPrefix count block + offset) = block ∧
      quittingAdaptiveMeshOffset count
          (quittingVariableBlockPrefix count block + offset) = offset := by
  have hstate := quittingVariableBlockState_prefix_add
    count hcount block offset hoffset
  constructor
  · simpa [quittingAdaptiveMeshBlock] using congrArg Prod.fst hstate
  · simpa [quittingAdaptiveMeshOffset] using congrArg Prod.snd hstate

/-- The next flattened value is exactly the next mesh interpolant of the
current coarse block, including at the seam where that interpolant closes at
the next coarse value. -/
theorem quittingAdaptiveMeshValue_succ_eq_interpolant
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ℕ → ι) (mass : ℕ → ℝ) (value : ℕ → Payoff ι)
    (count : ℕ → ℕ)
    (hcount : ∀ block, 0 < count block)
    (hmass1 : ∀ block, mass block < 1)
    (harc : ∀ block,
      value block = quittingSingletonArcPayoff (mass block)
        (quittingSoloReward reward (owner block)) (value (block + 1)))
    (time : ℕ) :
    let block := quittingAdaptiveMeshBlock count time
    quittingAdaptiveMeshValue reward owner mass value count (time + 1) =
      quittingMeshPayoffInterpolant
        (quittingSoloReward reward (owner block)) (value block)
        (1 - quittingMeshHazard (mass block) (count block))
        (quittingAdaptiveMeshOffset count time + 1) := by
  dsimp only
  generalize hstate : quittingVariableBlockState count time = state
  rcases state with ⟨block, offset⟩
  have hoffset : offset < count block := by
    have hraw := quittingVariableBlockState_offset_lt count hcount time
    simpa [hstate] using hraw
  by_cases hinterior : offset + 1 < count block
  · simp [quittingAdaptiveMeshValue, quittingAdaptiveMeshBlock,
      quittingAdaptiveMeshOffset, quittingVariableBlockState,
      hstate, hinterior]
  · have hseam : offset + 1 = count block := by omega
    have hclose := quittingMeshPayoffInterpolant_at_length_eq_next
      (hmass1 block) (hcount block) (harc block)
    funext who
    simp only [quittingAdaptiveMeshValue, quittingAdaptiveMeshBlock,
      quittingAdaptiveMeshOffset, quittingVariableBlockState,
      hstate, hinterior, ↓reduceIte, Prod.fst, Prod.snd,
      quittingMeshPayoffInterpolant_apply]
    rw [hseam]
    have hzero : quittingMeshInterpolant
        (quittingSoloReward reward (owner (block + 1)) who)
        (value (block + 1) who)
        (1 - quittingMeshHazard (mass (block + 1)) (count (block + 1)))
        0 = value (block + 1) who := by
      simp [quittingMeshInterpolant]
    rw [hzero]
    exact (congrFun hclose who).symm

/-- Viability of consecutive coarse values propagates through every adaptive
microblock. -/
theorem quittingAdaptiveMeshValue_viable
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ℕ → ι) (mass : ℕ → ℝ) (value : ℕ → Payoff ι)
    (count : ℕ → ℕ)
    (hcount : ∀ block, 0 < count block)
    (hmass0 : ∀ block, 0 ≤ mass block)
    (hmass1 : ∀ block, mass block < 1)
    (harc : ∀ block,
      value block = quittingSingletonArcPayoff (mass block)
        (quittingSoloReward reward (owner block)) (value (block + 1)))
    (hviable : ∀ block, QuittingEssentialAPSViable reward (value block))
    (time : ℕ) :
    QuittingEssentialAPSViable reward
      (quittingAdaptiveMeshValue reward owner mass value count time) := by
  intro who
  generalize hstate : quittingVariableBlockState count time = state
  rcases state with ⟨block, offset⟩
  have hoffset : offset < count block := by
    have hraw := quittingVariableBlockState_offset_lt count hcount time
    simpa [hstate] using hraw
  simpa [quittingAdaptiveMeshValue, quittingAdaptiveMeshBlock,
      quittingAdaptiveMeshOffset, hstate] using
    (le_quittingMeshPayoffInterpolant_of_arcEndpoints
      (hmass0 block) (hmass1 block) (hcount block) (harc block)
      (hviable block) (hviable (block + 1)) offset hoffset.le who)

/-- A uniform bound on consecutive coarse values bounds every adaptive
interpolant by the same constant. -/
theorem abs_quittingAdaptiveMeshValue_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ℕ → ι) (mass : ℕ → ℝ) (value : ℕ → Payoff ι)
    (count : ℕ → ℕ)
    (hcount : ∀ block, 0 < count block)
    (hmass0 : ∀ block, 0 ≤ mass block)
    (hmass1 : ∀ block, mass block < 1)
    (harc : ∀ block,
      value block = quittingSingletonArcPayoff (mass block)
        (quittingSoloReward reward (owner block)) (value (block + 1)))
    {bound : ℝ}
    (hvalueBound : ∀ block who, |value block who| ≤ bound)
    (time : ℕ) (who : ι) :
    |quittingAdaptiveMeshValue reward owner mass value count time who| ≤
      bound := by
  generalize hstate : quittingVariableBlockState count time = state
  rcases state with ⟨block, offset⟩
  have hoffset : offset < count block := by
    have hraw := quittingVariableBlockState_offset_lt count hcount time
    simpa [hstate] using hraw
  rw [abs_le]
  constructor
  · simpa [quittingAdaptiveMeshValue, quittingAdaptiveMeshBlock,
        quittingAdaptiveMeshOffset, hstate] using
      (le_quittingMeshPayoffInterpolant_of_arcEndpoints
        (hmass0 block) (hmass1 block) (hcount block) (harc block)
        (fun player ↦ (abs_le.mp (hvalueBound block player)).1)
        (fun player ↦ (abs_le.mp (hvalueBound (block + 1) player)).1)
        offset hoffset.le who)
  · simpa [quittingAdaptiveMeshValue, quittingAdaptiveMeshBlock,
        quittingAdaptiveMeshOffset, hstate] using
      (quittingMeshPayoffInterpolant_le_of_arcEndpoints
        (hmass0 block) (hmass1 block) (hcount block) (harc block)
        (fun player ↦ (abs_le.mp (hvalueBound block player)).2)
        (fun player ↦ (abs_le.mp (hvalueBound (block + 1) player)).2)
        offset hoffset.le who)

/-- One adaptive microstage has exact policy evaluation, exact prescribed
Continue, and Quit error bounded by `D` times its micro-hazard. -/
theorem quittingAdaptiveMesh_local_certificate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ℕ → ι) (mass : ℕ → ℝ) (value : ℕ → Payoff ι)
    (count : ℕ → ℕ)
    (hcount : ∀ block, 0 < count block)
    (hmass0 : ∀ block, 0 ≤ mass block)
    (hmass1 : ∀ block, mass block < 1)
    (harc : ∀ block,
      value block = quittingSingletonArcPayoff (mass block)
        (quittingSoloReward reward (owner block)) (value (block + 1)))
    (hactive : ∀ block,
      value block (owner block) =
        quittingSoloReward reward (owner block) (owner block))
    (hviable : ∀ block, QuittingEssentialAPSViable reward (value block))
    {D : ℝ} (hD : 0 ≤ D)
    (hcollision : ∀ block other, other ≠ owner block →
      max (quittingSingletonCollisionReward reward (owner block) other -
        quittingSoloReward reward other other) 0 ≤ D)
    (time : ℕ) :
    let roots := quittingAdaptiveMeshRoots owner mass count hmass0
      (fun block ↦ (hmass1 block).le)
    let current := quittingAdaptiveMeshValue reward owner mass value count time
    let next := quittingAdaptiveMeshValue reward owner mass value count (time + 1)
    current = quittingRootSuccessorPayoff reward next (roots time) ∧
      (∀ who,
        quittingStationaryFixedOpponentsContinueReward reward (roots time) who +
          quittingStationaryFixedOpponentsContinueMass (roots time) who *
            next who = current who) ∧
      ∀ who,
        quittingStationaryFixedOpponentsQuitValue reward (roots time) who ≤
          current who + D * quittingAdaptiveMeshHazard mass count time := by
  dsimp only
  generalize hstate : quittingVariableBlockState count time = state
  rcases state with ⟨block, offset⟩
  have hoffset : offset < count block := by
    have hraw := quittingVariableBlockState_offset_lt count hcount time
    simpa [hstate] using hraw
  have hnext := quittingAdaptiveMeshValue_succ_eq_interpolant
    reward owner mass value count hcount hmass1 harc time
  have hsolo : ∀ who,
      quittingSoloReward reward who who ≤
        quittingMeshPayoffInterpolant
          (quittingSoloReward reward (owner block)) (value block)
          (1 - quittingMeshHazard (mass block) (count block)) offset who := by
    intro who
    have hmicro := quittingAdaptiveMeshValue_viable
      reward owner mass value count hcount hmass0 hmass1 harc hviable time who
    simpa [quittingAdaptiveMeshValue, quittingAdaptiveMeshBlock,
      quittingAdaptiveMeshOffset, hstate, quittingSoloBaseline] using hmicro
  have hcertificate :=
    singletonStationaryRoot_interpolant_certificate
      reward (owner block)
      (quittingHazardCoin
        (quittingMeshHazard (mass block) (count block))
        (quittingMeshHazard_nonneg _ (hmass0 block) (hmass1 block).le)
        (quittingMeshHazard_le_one _ (hmass1 block).le))
      (quittingMeshHazard_nonneg _ (hmass0 block) (hmass1 block).le)
      (quittingMeshHazard_lt_one (hmass1 block) (count block))
      (quittingHazardCoin_true_toReal _ _ _)
      (quittingHazardCoin_false_toReal _ _ _)
      (quittingSoloReward reward (owner block)) (value block) offset
      hD rfl (hactive block) hsolo (hcollision block)
  rw [hnext]
  simpa [quittingAdaptiveMeshRoots, quittingAdaptiveMeshOwner,
    quittingAdaptiveMeshHazard, quittingAdaptiveMeshValue,
    quittingAdaptiveMeshBlock, quittingAdaptiveMeshOffset, hstate] using
      hcertificate

end GameTheory
