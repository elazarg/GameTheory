/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingInfiniteSingletonMesh

/-!
# Variable subdivision of nonperiodic singleton-flow paths

A fixed subdivision width is stronger than the nonperiodic compiler needs.
For each coarse singleton arc with hazard `p_t < 1`, choose its own positive
mesh width `m_t` and repeat the logarithmic micro-hazard

`h_t = 1 - (1 - p_t)^(1 / m_t)`.

The resulting deterministic clock traverses block `t` for exactly `m_t`
microstages. At every coarse boundary the value and deleted-player survival
agree exactly with the original path. Consequently arbitrary positive,
finite widths preserve vanishing opponent survival even when the widths are
unbounded. Choosing `m_t` separately makes every immediate-Quit error smaller
than one common tolerance without any uniform ceiling `sup_t p_t < 1`.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The variable-width clock -/

/-- State `(coarse, offset)` of the deterministic variable-width clock. -/
def quittingVariableMeshState (mesh : ℕ → ℕ) : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | time + 1 =>
      let state := quittingVariableMeshState mesh time
      if state.2 + 1 < mesh state.1 then
        (state.1, state.2 + 1)
      else
        (state.1 + 1, 0)

/-- Coarse stage containing a variable-mesh microstage. -/
def quittingVariableMeshCoarseTime
    (mesh : ℕ → ℕ) (time : ℕ) : ℕ :=
  (quittingVariableMeshState mesh time).1

/-- Offset inside the current variable-width coarse block. -/
def quittingVariableMeshOffset
    (mesh : ℕ → ℕ) (time : ℕ) : ℕ :=
  (quittingVariableMeshState mesh time).2

/-- Beginning of coarse block `coarse`. -/
def quittingVariableMeshBoundary (mesh : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | coarse + 1 =>
      quittingVariableMeshBoundary mesh coarse + mesh coarse

@[simp] theorem quittingVariableMeshState_zero (mesh : ℕ → ℕ) :
    quittingVariableMeshState mesh 0 = (0, 0) := rfl

@[simp] theorem quittingVariableMeshCoarseTime_zero (mesh : ℕ → ℕ) :
    quittingVariableMeshCoarseTime mesh 0 = 0 := rfl

@[simp] theorem quittingVariableMeshOffset_zero (mesh : ℕ → ℕ) :
    quittingVariableMeshOffset mesh 0 = 0 := rfl

@[simp] theorem quittingVariableMeshBoundary_zero (mesh : ℕ → ℕ) :
    quittingVariableMeshBoundary mesh 0 = 0 := rfl

@[simp] theorem quittingVariableMeshBoundary_succ
    (mesh : ℕ → ℕ) (coarse : ℕ) :
    quittingVariableMeshBoundary mesh (coarse + 1) =
      quittingVariableMeshBoundary mesh coarse + mesh coarse := rfl

/-- Every offset is valid when every selected mesh width is positive. -/
theorem quittingVariableMeshOffset_lt
    (mesh : ℕ → ℕ) (hmesh : ∀ coarse, 0 < mesh coarse) :
    ∀ time,
      quittingVariableMeshOffset mesh time <
        mesh (quittingVariableMeshCoarseTime mesh time) := by
  intro time
  induction time with
  | zero =>
      simpa [quittingVariableMeshOffset,
        quittingVariableMeshCoarseTime] using hmesh 0
  | succ time _ih =>
      unfold quittingVariableMeshOffset quittingVariableMeshCoarseTime
      rw [quittingVariableMeshState]
      dsimp only
      split_ifs with hinside
      · exact hinside
      · exact hmesh ((quittingVariableMeshState mesh time).1 + 1)

/-- Inside one block, the clock keeps its coarse coordinate and increments its
micro-offset. -/
theorem quittingVariableMeshState_succ_of_inside
    (mesh : ℕ → ℕ) (time : ℕ)
    (hinside : quittingVariableMeshOffset mesh time + 1 <
      mesh (quittingVariableMeshCoarseTime mesh time)) :
    quittingVariableMeshState mesh (time + 1) =
      (quittingVariableMeshCoarseTime mesh time,
        quittingVariableMeshOffset mesh time + 1) := by
  unfold quittingVariableMeshCoarseTime quittingVariableMeshOffset at hinside ⊢
  rw [quittingVariableMeshState]
  dsimp only
  rw [if_pos hinside]

/-- At the final offset of a block, the clock advances to offset zero of the
next coarse stage. -/
theorem quittingVariableMeshState_succ_of_last
    (mesh : ℕ → ℕ) (time : ℕ)
    (hlast : quittingVariableMeshOffset mesh time + 1 =
      mesh (quittingVariableMeshCoarseTime mesh time)) :
    quittingVariableMeshState mesh (time + 1) =
      (quittingVariableMeshCoarseTime mesh time + 1, 0) := by
  unfold quittingVariableMeshCoarseTime quittingVariableMeshOffset at hlast ⊢
  rw [quittingVariableMeshState]
  dsimp only
  rw [if_neg (by omega)]

/-- Starting from a known clock state, every strictly interior finite advance
has the expected state. -/
theorem quittingVariableMeshState_add_inside
    (mesh : ℕ → ℕ) {time coarse offset steps : ℕ}
    (hstate : quittingVariableMeshState mesh time = (coarse, offset))
    (hsteps : offset + steps < mesh coarse) :
    quittingVariableMeshState mesh (time + steps) =
      (coarse, offset + steps) := by
  revert hsteps
  induction steps with
  | zero =>
      intro _hsteps
      simpa using hstate
  | succ steps ih =>
      intro hsteps
      have hprevious : offset + steps < mesh coarse := by omega
      have hih := ih hprevious
      rw [Nat.add_succ, quittingVariableMeshState, hih]
      dsimp only
      rw [if_pos (by omega)]

/-- A full positive-width block advances exactly once in the coarse clock. -/
theorem quittingVariableMeshState_add_mesh
    (mesh : ℕ → ℕ) (hmesh : ∀ coarse, 0 < mesh coarse)
    {time coarse : ℕ}
    (hstate : quittingVariableMeshState mesh time = (coarse, 0)) :
    quittingVariableMeshState mesh (time + mesh coarse) =
      (coarse + 1, 0) := by
  have hmeshCoarse : 0 < mesh coarse := hmesh coarse
  let last := mesh coarse - 1
  have hlastLt : last < mesh coarse := by
    dsimp only [last]
    omega
  have hbefore := quittingVariableMeshState_add_inside
    mesh hstate (offset := 0) (steps := last) (by simpa using hlastLt)
  have htime : time + mesh coarse = (time + last) + 1 := by
    dsimp only [last]
    omega
  rw [htime, quittingVariableMeshState, hbefore]
  dsimp only
  rw [if_neg (by
    dsimp only [last]
    omega)]

/-- The recursive clock is at `(coarse, 0)` at the declared boundary of every
coarse block. -/
theorem quittingVariableMeshState_boundary
    (mesh : ℕ → ℕ) (hmesh : ∀ coarse, 0 < mesh coarse) :
    ∀ coarse,
      quittingVariableMeshState mesh
        (quittingVariableMeshBoundary mesh coarse) = (coarse, 0) := by
  intro coarse
  induction coarse with
  | zero => rfl
  | succ coarse ih =>
      rw [quittingVariableMeshBoundary_succ]
      exact quittingVariableMeshState_add_mesh mesh hmesh ih

/-- State at an arbitrary offset inside a declared coarse block. -/
theorem quittingVariableMeshState_boundary_add
    (mesh : ℕ → ℕ) (hmesh : ∀ coarse, 0 < mesh coarse)
    {coarse offset : ℕ} (hoffset : offset < mesh coarse) :
    quittingVariableMeshState mesh
        (quittingVariableMeshBoundary mesh coarse + offset) =
      (coarse, offset) := by
  apply quittingVariableMeshState_add_inside mesh
    (quittingVariableMeshState_boundary mesh hmesh coarse)
  simpa using hoffset

@[simp] theorem quittingVariableMeshCoarseTime_boundary
    (mesh : ℕ → ℕ) (hmesh : ∀ coarse, 0 < mesh coarse)
    (coarse : ℕ) :
    quittingVariableMeshCoarseTime mesh
        (quittingVariableMeshBoundary mesh coarse) = coarse := by
  unfold quittingVariableMeshCoarseTime
  rw [quittingVariableMeshState_boundary mesh hmesh coarse]

@[simp] theorem quittingVariableMeshOffset_boundary
    (mesh : ℕ → ℕ) (hmesh : ∀ coarse, 0 < mesh coarse)
    (coarse : ℕ) :
    quittingVariableMeshOffset mesh
        (quittingVariableMeshBoundary mesh coarse) = 0 := by
  unfold quittingVariableMeshOffset
  rw [quittingVariableMeshState_boundary mesh hmesh coarse]

/-- Every microtime has its canonical boundary-plus-offset decomposition. -/
theorem quittingVariableMesh_boundary_add_offset
    (mesh : ℕ → ℕ) (hmesh : ∀ coarse, 0 < mesh coarse) :
    ∀ time,
      quittingVariableMeshBoundary mesh
          (quittingVariableMeshCoarseTime mesh time) +
        quittingVariableMeshOffset mesh time = time := by
  intro time
  induction time with
  | zero => rfl
  | succ time ih =>
      have hoffset := quittingVariableMeshOffset_lt mesh hmesh time
      by_cases hinside : quittingVariableMeshOffset mesh time + 1 <
          mesh (quittingVariableMeshCoarseTime mesh time)
      · have hstate :=
          quittingVariableMeshState_succ_of_inside mesh time hinside
        have hcoarse :
            quittingVariableMeshCoarseTime mesh (time + 1) =
              quittingVariableMeshCoarseTime mesh time := by
          unfold quittingVariableMeshCoarseTime
          rw [hstate]
        have hoffsetSucc :
            quittingVariableMeshOffset mesh (time + 1) =
              quittingVariableMeshOffset mesh time + 1 := by
          unfold quittingVariableMeshOffset
          rw [hstate]
        rw [hcoarse, hoffsetSucc]
        omega
      · have hlast : quittingVariableMeshOffset mesh time + 1 =
            mesh (quittingVariableMeshCoarseTime mesh time) := by
          omega
        have hstate :=
          quittingVariableMeshState_succ_of_last mesh time hlast
        have hcoarse :
            quittingVariableMeshCoarseTime mesh (time + 1) =
              quittingVariableMeshCoarseTime mesh time + 1 := by
          unfold quittingVariableMeshCoarseTime
          rw [hstate]
        have hoffsetSucc :
            quittingVariableMeshOffset mesh (time + 1) = 0 := by
          unfold quittingVariableMeshOffset
          rw [hstate]
        rw [hcoarse, hoffsetSucc,
          quittingVariableMeshBoundary_succ]
        omega

/-- Boundaries are monotone under a finite coarse advance. -/
theorem quittingVariableMeshBoundary_le_add
    (mesh : ℕ → ℕ) (start fuel : ℕ) :
    quittingVariableMeshBoundary mesh start ≤
      quittingVariableMeshBoundary mesh (start + fuel) := by
  induction fuel with
  | zero => simp
  | succ fuel ih =>
      rw [show start + fuel.succ = (start + fuel) + 1 by omega,
        quittingVariableMeshBoundary_succ]
      exact ih.trans (Nat.le_add_right _ _)

/-! ## Variable subdivision of a singleton-flow path -/

/-- Active owner at a variable-mesh microstage. -/
def quittingVariableMeshOwner
    (owner : ℕ → ι) (mesh : ℕ → ℕ) : ℕ → ι :=
  fun time ↦ owner (quittingVariableMeshCoarseTime mesh time)

/-- Micro-hazard in the current variable-width coarse block. -/
def quittingVariableMeshMass
    (mass : ℕ → ℝ) (mesh : ℕ → ℕ) : ℕ → ℝ :=
  fun time ↦
    let coarse := quittingVariableMeshCoarseTime mesh time
    quittingMeshHazard (mass coarse) (mesh coarse)

/-- Interpolated payoff along the current variable-width coarse arc. -/
def quittingVariableMeshValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ℕ → ι) (mass : ℕ → ℝ) (value : ℕ → Payoff ι)
    (mesh : ℕ → ℕ) : ℕ → Payoff ι :=
  fun time ↦
    let coarse := quittingVariableMeshCoarseTime mesh time
    quittingMeshPayoffInterpolant
      (quittingSoloReward reward (owner coarse))
      (value coarse)
      (1 - quittingMeshHazard (mass coarse) (mesh coarse))
      (quittingVariableMeshOffset mesh time)

/-- The interpolated micro-value closes exactly at every variable boundary. -/
@[simp] theorem quittingVariableMeshValue_boundary
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ℕ → ι) (mass : ℕ → ℝ) (value : ℕ → Payoff ι)
    (mesh : ℕ → ℕ) (hmesh : ∀ coarse, 0 < mesh coarse)
    (coarse : ℕ) :
    quittingVariableMeshValue reward owner mass value mesh
        (quittingVariableMeshBoundary mesh coarse) = value coarse := by
  unfold quittingVariableMeshValue
  rw [quittingVariableMeshCoarseTime_boundary mesh hmesh coarse,
    quittingVariableMeshOffset_boundary mesh hmesh coarse]
  exact quittingMeshPayoffInterpolant_zero _ _ _

/-- The successor value is the next point of the current interpolant, including
its closing step into the next variable-width block. -/
theorem quittingVariableMeshValue_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ℕ → ι) (mass : ℕ → ℝ) (value : ℕ → Payoff ι)
    (mesh : ℕ → ℕ) (hmesh : ∀ coarse, 0 < mesh coarse)
    (hmass1 : ∀ time, mass time < 1)
    (harc : ∀ time,
      value time = quittingSingletonArcPayoff (mass time)
        (quittingSoloReward reward (owner time)) (value (time + 1)))
    (time : ℕ) :
    quittingVariableMeshValue reward owner mass value mesh (time + 1) =
      let coarse := quittingVariableMeshCoarseTime mesh time
      quittingMeshPayoffInterpolant
        (quittingSoloReward reward (owner coarse))
        (value coarse)
        (1 - quittingMeshHazard (mass coarse) (mesh coarse))
        (quittingVariableMeshOffset mesh time + 1) := by
  let coarse := quittingVariableMeshCoarseTime mesh time
  let offset := quittingVariableMeshOffset mesh time
  have hoffset : offset < mesh coarse :=
    quittingVariableMeshOffset_lt mesh hmesh time
  by_cases hinside : offset + 1 < mesh coarse
  · have hstate := quittingVariableMeshState_succ_of_inside
      mesh time (by simpa only [coarse, offset] using hinside)
    have hcoarseSucc :
        quittingVariableMeshCoarseTime mesh (time + 1) = coarse := by
      unfold quittingVariableMeshCoarseTime
      rw [hstate]
    have hoffsetSucc :
        quittingVariableMeshOffset mesh (time + 1) = offset + 1 := by
      unfold quittingVariableMeshOffset
      rw [hstate]
    unfold quittingVariableMeshValue
    rw [hcoarseSucc, hoffsetSucc]
  · have hlast : offset + 1 = mesh coarse := by omega
    have hstate := quittingVariableMeshState_succ_of_last
      mesh time (by simpa only [coarse, offset] using hlast)
    have hcoarseSucc :
        quittingVariableMeshCoarseTime mesh (time + 1) = coarse + 1 := by
      unfold quittingVariableMeshCoarseTime
      rw [hstate]
    have hoffsetSucc :
        quittingVariableMeshOffset mesh (time + 1) = 0 := by
      unfold quittingVariableMeshOffset
      rw [hstate]
    calc
      quittingVariableMeshValue reward owner mass value mesh (time + 1) =
          value (coarse + 1) := by
            unfold quittingVariableMeshValue
            rw [hcoarseSucc, hoffsetSucc]
            exact quittingMeshPayoffInterpolant_zero _ _ _
      _ = quittingMeshPayoffInterpolant
          (quittingSoloReward reward (owner coarse))
          (value coarse)
          (1 - quittingMeshHazard (mass coarse) (mesh coarse))
          (mesh coarse) := by
            symm
            exact quittingMeshPayoffInterpolant_at_length_eq_next
              (hmass1 coarse) (hmesh coarse) (harc coarse)
      _ = quittingMeshPayoffInterpolant
          (quittingSoloReward reward (owner coarse))
          (value coarse)
          (1 - quittingMeshHazard (mass coarse) (mesh coarse))
          (offset + 1) := by rw [hlast]

/-- Variable micro-hazards are nonnegative. -/
theorem quittingVariableMeshMass_nonneg
    (mass : ℕ → ℝ) (mesh : ℕ → ℕ)
    (hmass0 : ∀ time, 0 ≤ mass time)
    (hmass1 : ∀ time, mass time ≤ 1) :
    ∀ time, 0 ≤ quittingVariableMeshMass mass mesh time := by
  intro time
  exact quittingMeshHazard_nonneg
    (mesh (quittingVariableMeshCoarseTime mesh time))
    (hmass0 (quittingVariableMeshCoarseTime mesh time))
    (hmass1 (quittingVariableMeshCoarseTime mesh time))

/-- Variable micro-hazards are at most one. -/
theorem quittingVariableMeshMass_le_one
    (mass : ℕ → ℝ) (mesh : ℕ → ℕ)
    (hmass1 : ∀ time, mass time ≤ 1) :
    ∀ time, quittingVariableMeshMass mass mesh time ≤ 1 := by
  intro time
  exact quittingMeshHazard_le_one
    (mesh (quittingVariableMeshCoarseTime mesh time))
    (hmass1 (quittingVariableMeshCoarseTime mesh time))

/-- Product singleton roots implementing the variable-width mesh. -/
def quittingVariableMeshRoots
    (owner : ℕ → ι) (mass : ℕ → ℝ) (mesh : ℕ → ℕ)
    (hmass0 : ∀ time, 0 ≤ mass time)
    (hmass1 : ∀ time, mass time ≤ 1) :
    ℕ → ι → PMF Bool :=
  quittingEssentialAPSSingletonRoots
    (quittingVariableMeshOwner owner mesh)
    (quittingVariableMeshMass mass mesh)
    (quittingVariableMeshMass_nonneg mass mesh hmass0 hmass1)
    (quittingVariableMeshMass_le_one mass mesh hmass1)

/-- Viability of consecutive coarse endpoints is inherited by every
variable-mesh micro-value. -/
theorem quittingVariableMeshValue_viable
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ℕ → ι) (mass : ℕ → ℝ) (value : ℕ → Payoff ι)
    (mesh : ℕ → ℕ) (hmesh : ∀ coarse, 0 < mesh coarse)
    (hmass0 : ∀ time, 0 ≤ mass time)
    (hmass1 : ∀ time, mass time < 1)
    (harc : ∀ time,
      value time = quittingSingletonArcPayoff (mass time)
        (quittingSoloReward reward (owner time)) (value (time + 1)))
    (hviable : ∀ time, QuittingEssentialAPSViable reward (value time)) :
    ∀ time, QuittingEssentialAPSViable reward
      (quittingVariableMeshValue reward owner mass value mesh time) := by
  intro time who
  let coarse := quittingVariableMeshCoarseTime mesh time
  let offset := quittingVariableMeshOffset mesh time
  have hoffset : offset ≤ mesh coarse :=
    (quittingVariableMeshOffset_lt mesh hmesh time).le
  unfold quittingVariableMeshValue
  exact le_quittingMeshPayoffInterpolant_of_arcEndpoints
    (hmass0 coarse) (hmass1 coarse) (hmesh coarse) (harc coarse)
    (hviable coarse) (hviable (coarse + 1)) offset hoffset who

/-- A common absolute coarse bound holds at every variable-mesh microstage. -/
theorem quittingVariableMeshValue_bound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ℕ → ι) (mass : ℕ → ℝ) (value : ℕ → Payoff ι)
    (mesh : ℕ → ℕ) (hmesh : ∀ coarse, 0 < mesh coarse)
    (hmass0 : ∀ time, 0 ≤ mass time)
    (hmass1 : ∀ time, mass time < 1)
    (harc : ∀ time,
      value time = quittingSingletonArcPayoff (mass time)
        (quittingSoloReward reward (owner time)) (value (time + 1)))
    {bound : ℝ} (hvalueBound : ∀ time who, |value time who| ≤ bound) :
    ∀ time who,
      |quittingVariableMeshValue reward owner mass value mesh time who| ≤
        bound := by
  intro time who
  let coarse := quittingVariableMeshCoarseTime mesh time
  let offset := quittingVariableMeshOffset mesh time
  have hoffset : offset ≤ mesh coarse :=
    (quittingVariableMeshOffset_lt mesh hmesh time).le
  unfold quittingVariableMeshValue
  exact abs_quittingMeshPayoffInterpolant_le_of_arcEndpoints
    (hmass0 coarse) (hmass1 coarse) (hmesh coarse) (harc coarse)
    (hvalueBound coarse) (hvalueBound (coarse + 1)) offset hoffset who

end GameTheory
