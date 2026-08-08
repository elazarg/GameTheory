/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Terminal.TargetTail.InfiniteVariableSingletonMesh
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.EssentialAPS.OpponentContraction

/-!
# Survival transport and divergent mass for variable singleton meshes

Variable subdivision preserves deleted-player survival exactly at every coarse
boundary. Arbitrary positive finite block widths therefore preserve vanishing
coarse survival, even when the widths are unbounded.

The second half removes geometric contraction from the coarse path itself.
Bounded successor-coordinate drift converts divergence of total absorption
mass into divergence of every player's opponent mass; the elementary
product-versus-sum estimate then forces deleted-player survival to zero.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Exact survival transport -/

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem quittingVariableMeshOwner_boundary_add
    (owner : ℕ → ι) (mesh : ℕ → ℕ)
    (hmesh : ∀ coarse, 0 < mesh coarse)
    {coarse offset : ℕ} (hoffset : offset < mesh coarse) :
    quittingVariableMeshOwner owner mesh
        (quittingVariableMeshBoundary mesh coarse + offset) =
      owner coarse := by
  unfold quittingVariableMeshOwner quittingVariableMeshCoarseTime
  rw [quittingVariableMeshState_boundary_add mesh hmesh hoffset]

@[simp] theorem quittingVariableMeshMass_boundary_add
    (mass : ℕ → ℝ) (mesh : ℕ → ℕ)
    (hmesh : ∀ coarse, 0 < mesh coarse)
    {coarse offset : ℕ} (hoffset : offset < mesh coarse) :
    quittingVariableMeshMass mass mesh
        (quittingVariableMeshBoundary mesh coarse + offset) =
      quittingMeshHazard (mass coarse) (mesh coarse) := by
  unfold quittingVariableMeshMass quittingVariableMeshCoarseTime
  rw [quittingVariableMeshState_boundary_add mesh hmesh hoffset]

/-- One full variable-width microblock has exactly the deleted-player survival
of its coarse singleton root. -/
theorem quittingOpponentSurvivalWeight_variableMesh_one_block
    (owner : ℕ → ι) (mass : ℕ → ℝ) (mesh : ℕ → ℕ)
    (hmesh : ∀ coarse, 0 < mesh coarse)
    (hmass0 : ∀ time, 0 ≤ mass time)
    (hmass1 : ∀ time, mass time ≤ 1)
    (who : ι) (coarse : ℕ) :
    quittingOpponentSurvivalWeight
        (quittingVariableMeshRoots owner mass mesh hmass0 hmass1)
        who (quittingVariableMeshBoundary mesh coarse) (mesh coarse) =
      quittingOpponentSurvivalWeight
        (quittingEssentialAPSSingletonRoots owner mass hmass0 hmass1)
        who coarse 1 := by
  unfold quittingVariableMeshRoots
  rw [quittingOpponentSurvivalWeight_singletonRoots_eq,
    quittingOpponentSurvivalWeight_singletonRoots_eq]
  simp only [Finset.prod_range_one, Nat.add_zero]
  by_cases howner : owner coarse = who
  · calc
      (∏ offset ∈ Finset.range (mesh coarse),
          (1 - quittingEssentialAPSOpponentStageMass
            (quittingVariableMeshOwner owner mesh)
            (quittingVariableMeshMass mass mesh) who
            (quittingVariableMeshBoundary mesh coarse + offset))) =
          ∏ _offset ∈ Finset.range (mesh coarse), (1 - 0) := by
            apply Finset.prod_congr rfl
            intro offset hoffset
            have hoffsetLt := Finset.mem_range.mp hoffset
            simp [quittingEssentialAPSOpponentStageMass,
              quittingVariableMeshOwner_boundary_add owner mesh hmesh
                hoffsetLt,
              howner]
      _ = 1 := by simp
      _ = 1 - quittingEssentialAPSOpponentStageMass
          owner mass who coarse := by
            simp [quittingEssentialAPSOpponentStageMass, howner]
  · calc
      (∏ offset ∈ Finset.range (mesh coarse),
          (1 - quittingEssentialAPSOpponentStageMass
            (quittingVariableMeshOwner owner mesh)
            (quittingVariableMeshMass mass mesh) who
            (quittingVariableMeshBoundary mesh coarse + offset))) =
          ∏ _offset ∈ Finset.range (mesh coarse),
            (1 - quittingMeshHazard (mass coarse) (mesh coarse)) := by
              apply Finset.prod_congr rfl
              intro offset hoffset
              have hoffsetLt := Finset.mem_range.mp hoffset
              simp [quittingEssentialAPSOpponentStageMass,
                quittingVariableMeshOwner_boundary_add owner mesh hmesh
                  hoffsetLt,
                quittingVariableMeshMass_boundary_add mass mesh hmesh
                  hoffsetLt,
                howner]
      _ = (1 - quittingMeshHazard
          (mass coarse) (mesh coarse)) ^ mesh coarse := by simp
      _ = 1 - mass coarse :=
        one_sub_quittingMeshHazard_pow (hmass1 coarse) (hmesh coarse)
      _ = 1 - quittingEssentialAPSOpponentStageMass
          owner mass who coarse := by
            simp [quittingEssentialAPSOpponentStageMass, howner]

/-- Survival between any two declared variable boundaries is exactly the
corresponding coarse survival. -/
theorem quittingOpponentSurvivalWeight_variableMesh_boundaries
    (owner : ℕ → ι) (mass : ℕ → ℝ) (mesh : ℕ → ℕ)
    (hmesh : ∀ coarse, 0 < mesh coarse)
    (hmass0 : ∀ time, 0 ≤ mass time)
    (hmass1 : ∀ time, mass time ≤ 1)
    (who : ι) :
    ∀ start fuel,
      quittingOpponentSurvivalWeight
          (quittingVariableMeshRoots owner mass mesh hmass0 hmass1)
          who (quittingVariableMeshBoundary mesh start)
            (quittingVariableMeshBoundary mesh (start + fuel) -
              quittingVariableMeshBoundary mesh start) =
        quittingOpponentSurvivalWeight
          (quittingEssentialAPSSingletonRoots owner mass hmass0 hmass1)
          who start fuel := by
  intro start fuel
  induction fuel with
  | zero => simp [quittingOpponentSurvivalWeight]
  | succ fuel ih =>
      have hle := quittingVariableMeshBoundary_le_add mesh start fuel
      have hlength :
          quittingVariableMeshBoundary mesh (start + fuel.succ) -
              quittingVariableMeshBoundary mesh start =
            (quittingVariableMeshBoundary mesh (start + fuel) -
                quittingVariableMeshBoundary mesh start) +
              mesh (start + fuel) := by
        rw [show start + fuel.succ = (start + fuel) + 1 by omega,
          quittingVariableMeshBoundary_succ]
        omega
      have hboundary :
          quittingVariableMeshBoundary mesh start +
              (quittingVariableMeshBoundary mesh (start + fuel) -
                quittingVariableMeshBoundary mesh start) =
            quittingVariableMeshBoundary mesh (start + fuel) := by
        omega
      calc
        quittingOpponentSurvivalWeight
            (quittingVariableMeshRoots owner mass mesh hmass0 hmass1)
            who (quittingVariableMeshBoundary mesh start)
              (quittingVariableMeshBoundary mesh (start + fuel.succ) -
                quittingVariableMeshBoundary mesh start) =
          quittingOpponentSurvivalWeight
              (quittingVariableMeshRoots owner mass mesh hmass0 hmass1)
              who (quittingVariableMeshBoundary mesh start)
                (quittingVariableMeshBoundary mesh (start + fuel) -
                  quittingVariableMeshBoundary mesh start) *
            quittingOpponentSurvivalWeight
              (quittingVariableMeshRoots owner mass mesh hmass0 hmass1)
              who (quittingVariableMeshBoundary mesh (start + fuel))
                (mesh (start + fuel)) := by
                  rw [hlength, quittingOpponentSurvivalWeight_add,
                    hboundary]
        _ = quittingOpponentSurvivalWeight
              (quittingEssentialAPSSingletonRoots owner mass hmass0 hmass1)
              who start fuel *
            quittingOpponentSurvivalWeight
              (quittingVariableMeshRoots owner mass mesh hmass0 hmass1)
              who (quittingVariableMeshBoundary mesh (start + fuel))
                (mesh (start + fuel)) := by rw [ih]
        _ = quittingOpponentSurvivalWeight
              (quittingEssentialAPSSingletonRoots owner mass hmass0 hmass1)
              who start fuel *
            quittingOpponentSurvivalWeight
              (quittingEssentialAPSSingletonRoots owner mass hmass0 hmass1)
              who (start + fuel) 1 := by
                rw [quittingOpponentSurvivalWeight_variableMesh_one_block
                  owner mass mesh hmesh hmass0 hmass1 who (start + fuel)]
        _ = quittingOpponentSurvivalWeight
            (quittingEssentialAPSSingletonRoots owner mass hmass0 hmass1)
            who start fuel.succ := by
              rw [show fuel.succ = fuel + 1 by omega,
                quittingOpponentSurvivalWeight_add]

/-- Proper singleton hazards leave every finite deleted-player survival
prefix strictly positive. -/
theorem quittingOpponentSurvivalWeight_singletonRoots_pos_of_lt_one
    (owner : ℕ → ι) (mass : ℕ → ℝ)
    (hmass0 : ∀ time, 0 ≤ mass time)
    (hmass1 : ∀ time, mass time < 1)
    (who : ι) (start fuel : ℕ) :
    0 < quittingOpponentSurvivalWeight
      (quittingEssentialAPSSingletonRoots owner mass hmass0
        (fun time ↦ (hmass1 time).le)) who start fuel := by
  rw [quittingOpponentSurvivalWeight_singletonRoots_eq]
  apply Finset.prod_pos
  intro offset _hoffset
  unfold quittingEssentialAPSOpponentStageMass
  split
  · norm_num
  · exact sub_pos.mpr (hmass1 (start + offset))

/-- For proper singleton hazards, vanishing deleted-player survival from time
zero is equivalent to vanishing survival after every finite starting time.
The nontrivial direction divides the shifted time-zero product by its strictly
positive finite prefix. -/
theorem
    tendsto_zero_quittingOpponentSurvivalWeight_singletonRoots_tail_iff_zero
    (owner : ℕ → ι) (mass : ℕ → ℝ)
    (hmass0 : ∀ time, 0 ≤ mass time)
    (hmass1 : ∀ time, mass time < 1) :
    (∀ who start,
      Tendsto
        (quittingOpponentSurvivalWeight
          (quittingEssentialAPSSingletonRoots owner mass hmass0
            (fun time ↦ (hmass1 time).le)) who start)
        atTop (nhds 0)) ↔
      ∀ who,
        Tendsto
          (quittingOpponentSurvivalWeight
            (quittingEssentialAPSSingletonRoots owner mass hmass0
              (fun time ↦ (hmass1 time).le)) who 0)
          atTop (nhds 0) := by
  constructor
  · intro hall who
    exact hall who 0
  · intro hzero who start
    let roots := quittingEssentialAPSSingletonRoots owner mass hmass0
      (fun time ↦ (hmass1 time).le)
    have hprefixPos :
        0 < quittingOpponentSurvivalWeight roots who 0 start := by
      dsimp only [roots]
      exact quittingOpponentSurvivalWeight_singletonRoots_pos_of_lt_one
        owner mass hmass0 hmass1 who 0 start
    have hprefixNe :
        quittingOpponentSurvivalWeight roots who 0 start ≠ 0 :=
      ne_of_gt hprefixPos
    have hshift : Tendsto
        (fun fuel ↦ quittingOpponentSurvivalWeight roots who 0
          (fuel + start)) atTop (nhds 0) := by
      exact (hzero who).comp (tendsto_add_atTop_nat start)
    have hquotient := hshift.div_const
      (quittingOpponentSurvivalWeight roots who 0 start)
    have htail : Tendsto
        (quittingOpponentSurvivalWeight roots who start) atTop
          (nhds (0 /
            quittingOpponentSurvivalWeight roots who 0 start)) := by
      apply hquotient.congr'
      filter_upwards [] with fuel
      rw [show fuel + start = start + fuel by omega,
        quittingOpponentSurvivalWeight_add]
      field_simp
      simp
    simpa only [zero_div] using htail

/-- Arbitrary positive finite mesh widths preserve every vanishing coarse
opponent-survival tail. No rate or uniform bound on the widths is needed. -/
theorem tendsto_zero_quittingOpponentSurvivalWeight_variableMesh
    (owner : ℕ → ι) (mass : ℕ → ℝ) (mesh : ℕ → ℕ)
    (hmesh : ∀ coarse, 0 < mesh coarse)
    (hmass0 : ∀ time, 0 ≤ mass time)
    (hmass1 : ∀ time, mass time ≤ 1)
    (hcoarse : ∀ who start,
      Tendsto
        (quittingOpponentSurvivalWeight
          (quittingEssentialAPSSingletonRoots owner mass hmass0 hmass1)
          who start)
        atTop (nhds 0))
    (who : ι) (start : ℕ) :
    Tendsto
      (quittingOpponentSurvivalWeight
        (quittingVariableMeshRoots owner mass mesh hmass0 hmass1)
        who start)
      atTop (nhds 0) := by
  let coarse := quittingVariableMeshCoarseTime mesh start
  let nextBoundary := quittingVariableMeshBoundary mesh (coarse + 1)
  let wait := nextBoundary - start
  have hdecompose :=
    quittingVariableMesh_boundary_add_offset mesh hmesh start
  have hoffset := quittingVariableMeshOffset_lt mesh hmesh start
  have hstartBoundary : start ≤ nextBoundary := by
    dsimp only [nextBoundary, coarse]
    rw [quittingVariableMeshBoundary_succ]
    omega
  have hstartWait : start + wait = nextBoundary := by
    dsimp only [wait]
    omega
  have hsubBound : ∀ fuel,
      quittingOpponentSurvivalWeight
          (quittingVariableMeshRoots owner mass mesh hmass0 hmass1)
          who start
            (wait +
              (quittingVariableMeshBoundary mesh (coarse + 1 + fuel) -
                quittingVariableMeshBoundary mesh (coarse + 1))) ≤
        quittingOpponentSurvivalWeight
          (quittingEssentialAPSSingletonRoots owner mass hmass0 hmass1)
          who (coarse + 1) fuel := by
    intro fuel
    rw [quittingOpponentSurvivalWeight_add, hstartWait]
    have htransport :=
      quittingOpponentSurvivalWeight_variableMesh_boundaries
        owner mass mesh hmesh hmass0 hmass1 who (coarse + 1) fuel
    calc
      quittingOpponentSurvivalWeight
            (quittingVariableMeshRoots owner mass mesh hmass0 hmass1)
            who start wait *
          quittingOpponentSurvivalWeight
            (quittingVariableMeshRoots owner mass mesh hmass0 hmass1)
            who nextBoundary
              (quittingVariableMeshBoundary mesh (coarse + 1 + fuel) -
                quittingVariableMeshBoundary mesh (coarse + 1)) ≤
        1 * quittingOpponentSurvivalWeight
            (quittingEssentialAPSSingletonRoots owner mass hmass0 hmass1)
            who (coarse + 1) fuel := by
          apply mul_le_mul
          · exact quittingOpponentSurvivalWeight_le_one _ who start wait
          · exact le_of_eq (by simpa only [nextBoundary] using htransport)
          · exact quittingOpponentSurvivalWeight_nonneg _ who nextBoundary _
          · exact zero_le_one
      _ = quittingOpponentSurvivalWeight
          (quittingEssentialAPSSingletonRoots owner mass hmass0 hmass1)
          who (coarse + 1) fuel := one_mul _
  have hcoarseTail := hcoarse who (coarse + 1)
  rw [Metric.tendsto_atTop] at hcoarseTail ⊢
  intro epsilon hepsilon
  obtain ⟨fuel, hfuel⟩ := hcoarseTail epsilon hepsilon
  let threshold := wait +
    (quittingVariableMeshBoundary mesh (coarse + 1 + fuel) -
      quittingVariableMeshBoundary mesh (coarse + 1))
  refine ⟨threshold, ?_⟩
  intro later hlater
  have hmono := antitone_quittingOpponentSurvivalWeight
    (quittingVariableMeshRoots owner mass mesh hmass0 hmass1)
      who start hlater
  have hboundaryBound := hsubBound fuel
  have hclose := hfuel fuel le_rfl
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (quittingOpponentSurvivalWeight_nonneg
      (quittingEssentialAPSSingletonRoots owner mass hmass0 hmass1)
      who (coarse + 1) _)] at hclose
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (quittingOpponentSurvivalWeight_nonneg
      (quittingVariableMeshRoots owner mass mesh hmass0 hmass1)
      who start _)]
  exact hmono.trans_lt (hboundaryBound.trans_lt hclose)

/-! ## Total-mass divergence and bounded drift -/

/-- Nonnegative stage masses make every finite-window total monotone
in the window length. -/
theorem monotone_quittingEssentialAPSWindowMass
    (mass : ℕ → ℝ) (hmass0 : ∀ time, 0 ≤ mass time) (start : ℕ) :
    Monotone (quittingEssentialAPSWindowMass mass start) := by
  intro first second hle
  let rest := second - first
  have hsecond : second = first + rest := by
    dsimp only [rest]
    omega
  rw [hsecond, quittingEssentialAPSWindowMass_add]
  exact le_add_of_nonneg_right (by
    unfold quittingEssentialAPSWindowMass
    exact Finset.sum_nonneg fun offset _ ↦ hmass0 (start + first + offset))

/-- A positive mass floor in every fixed-width window forces divergence of the
cumulative total mass. -/
theorem tendsto_quittingEssentialAPSWindowMass_atTop_of_uniformWindow
    (mass : ℕ → ℝ) (hmass0 : ∀ time, 0 ≤ mass time)
    {window : ℕ} {nu : ℝ} (hnu : 0 < nu)
    (hwindow : ∀ start,
      nu ≤ quittingEssentialAPSWindowMass mass start window) :
    Tendsto (quittingEssentialAPSWindowMass mass 0) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro floor
  obtain ⟨blocks, hblocks⟩ := exists_nat_gt (floor / nu)
  have hfloor : floor < (blocks : ℝ) * nu := by
    calc
      floor = (floor / nu) * nu :=
        (div_mul_cancel₀ floor (ne_of_gt hnu)).symm
      _ < (blocks : ℝ) * nu :=
        mul_lt_mul_of_pos_right hblocks hnu
  have hblocksMass :=
    mul_le_quittingEssentialAPSWindowMass_mul mass hwindow blocks 0
  apply Filter.eventually_atTop.2
  refine ⟨blocks * window, ?_⟩
  intro fuel hfuel
  have hmono :=
    monotone_quittingEssentialAPSWindowMass mass hmass0 0 hfuel
  exact hfloor.le.trans (hblocksMass.trans hmono)

/-- Divergence of the cumulative total mass from time zero is invariant under
deleting any finite prefix. -/
theorem tendsto_quittingEssentialAPSWindowMass_tail_atTop_of_zero
    (mass : ℕ → ℝ)
    (htotal : Tendsto (quittingEssentialAPSWindowMass mass 0) atTop atTop) :
    ∀ start,
      Tendsto (quittingEssentialAPSWindowMass mass start) atTop atTop := by
  intro start
  apply Filter.tendsto_atTop.2
  intro floor
  have heventual := htotal.eventually_ge_atTop
    (floor + quittingEssentialAPSWindowMass mass 0 start)
  obtain ⟨threshold, hthreshold⟩ := Filter.eventually_atTop.1 heventual
  apply Filter.eventually_atTop.2
  refine ⟨threshold, ?_⟩
  intro fuel hfuel
  have hlarge := hthreshold (start + fuel) (by omega)
  have hsplit := quittingEssentialAPSWindowMass_add mass 0 start fuel
  simp only [Nat.zero_add] at hsplit
  linarith

/-- **Divergent total mass forces vanishing playerwise survival.**
Along a bounded active Flesch path, the successor-coordinate drift estimate
converts every sufficiently large total-mass window into an arbitrarily large
opponent-mass window. The product-versus-sum estimate then sends deleted-
player survival to zero. No uniform window lower bound or contraction rate is
assumed. -/
theorem
    tendsto_zero_quittingOpponentSurvivalWeight_singletonRoots_of_windowMass_atTop
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (successor : ι → ι) (owner : ℕ → ι)
    (mass : ℕ → ℝ) (value : ℕ → Payoff ι)
    {gap bound : ℝ}
    (hgapPos : 0 < gap) (hbound : 0 ≤ bound)
    (hmass0 : ∀ time, 0 ≤ mass time)
    (hmass1 : ∀ time, mass time ≤ 1)
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
    (hrootBound : ∀ time who,
      |quittingSoloReward reward (owner time) who| ≤ bound)
    (hvalueBound : ∀ time who, |value time who| ≤ bound)
    (htotal : ∀ start,
      Tendsto (quittingEssentialAPSWindowMass mass start) atTop atTop) :
    ∀ who start,
      Tendsto
        (quittingOpponentSurvivalWeight
          (quittingEssentialAPSSingletonRoots owner mass hmass0 hmass1)
          who start)
        atTop (nhds 0) := by
  intro who start
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  let eta : ℝ := 1 / epsilon
  have heta : 0 < eta := by
    dsimp only [eta]
    exact one_div_pos.mpr hepsilon
  let totalFloor : ℝ :=
    ((gap + 2 * bound) * eta + 2 * bound) / gap
  have heventual := (htotal start).eventually_ge_atTop totalFloor
  obtain ⟨threshold, hthreshold⟩ := Filter.eventually_atTop.1 heventual
  refine ⟨threshold, ?_⟩
  intro fuel hfuel
  have htotalFloor : totalFloor ≤
      quittingEssentialAPSWindowMass mass start fuel :=
    hthreshold fuel hfuel
  have hopponentRaw :=
    div_le_quittingEssentialAPSOpponentWindowMass_of_windowMass_le
      reward successor owner mass value hgapPos hbound hmass0 harc hactive
        hownerNext hgap hrootBound hvalueBound start fuel who htotalFloor
  have hgapDenom : 0 < gap + 2 * bound := by positivity
  have hfloorEq :
      (gap * totalFloor - 2 * bound) / (gap + 2 * bound) = eta := by
    dsimp only [totalFloor]
    field_simp [ne_of_gt hgapPos, ne_of_gt hgapDenom]
    all_goals ring
  have hopponent : eta ≤
      quittingEssentialAPSOpponentWindowMass owner mass who start fuel := by
    rw [hfloorEq] at hopponentRaw
    exact hopponentRaw
  have hsurvival :=
    quittingOpponentSurvivalWeight_singletonRoots_le
      owner mass hmass0 hmass1 heta.le who start fuel hopponent
  have hepsilonEta : epsilon * eta = 1 := by
    dsimp only [eta]
    field_simp [ne_of_gt hepsilon]
  have hreciprocal : 1 / (1 + eta) < epsilon := by
    apply (div_lt_iff₀ (by positivity : 0 < 1 + eta)).2
    nlinarith
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (quittingOpponentSurvivalWeight_nonneg
      (quittingEssentialAPSSingletonRoots owner mass hmass0 hmass1)
      who start fuel)]
  exact hsurvival.trans_lt hreciprocal

end GameTheory
